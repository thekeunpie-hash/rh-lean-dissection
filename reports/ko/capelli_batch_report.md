# `pp.explicit`가 많은 82개 파일의 탈-elaboration

> **실행 엔진**: [de_explicit_capelli.py](../scripts/de_explicit_capelli.py) (v2, 실행 시간 `44.76s`)  
> **입력 대상 목록**: [heavy82_targets.json](../out/heavy82_targets.json) (Round 1 [bloat_analysis_data.json](../out/bloat_analysis_data.json)의 `heavy_explicit_files = 82`, `heavy_explicit_total_lines = 75,221L`과 **1줄 오차 없이 100% 일치**)  
> **원시 검증 매니페스트**: [capelli_batch_manifest.json](../out/capelli_batch_manifest.json)  
> **변환 섀도우 트리**: `../out/capelli_shadow/` (원본 `downloads/lean/src/` **0바이트 변경**)

---

## 0. 핵심 정밀 구분: 정적 변환 절감치 vs Lean 4.34.1 단독 하네스 컴파일 검증 완료치

로컬 환경에는 `leanprover/lean4:v4.34.1`만 설치되어 있고, 원 레포지토리의 `leanprover/lean4:v4.33.1` 및 Mathlib `rev 0df444a3` 프리빌드 `.olean` 캐시(`downloads/lean/.lake/`)는 존재하지 않는다. 따라서 아래 두 수치를 엄격히 분리해 보고한다.

| 검증 범주 | 대상 범위 | Before | After | 절감량 (단축률) | 검증 방법 및 상태 |
| :--- | :--- | ---: | ---: | ---: | :--- |
| **정적 변환 절감치 (전체 82개 파일)** | Round 1 `heavy_explicit_files` 82개 파일 | **75,221L** (5,825,527B) | **13,612L** (1,008,203B) | **-61,609L (-81.90%)** / **-4,817,324B (-82.69%)** | AST 파서 + 선언명 100% 보존(1,542/1,542) + 괄호 균형 82/82 + 노테이션 인스턴스 누수 **0건** + 팬텀 암묵인자 명명 보존(**116회**) + `sorry`/`axiom`/`admit` 0건 + 안전 롤백 0건 |
| ├─ **정적 변환 절감치 (`CapelliIdentities` 46개)** | 82개 중 `CapelliIdentities` 소속 46개 파일 | **66,974L** (5,266,582B) | **6,119L** (498,725B) | **-60,855L (-90.86%)** / **-4,767,857B (-90.53%)** | 전체 절감량의 **98.78%** 차지 (`@` 라인 `55,875 → 703`, -98.74%) |
| ├─ **정적 변환 절감치 (실제 `pp.explicit` 51개)** | `CapelliIdentities` 46개 + `Lemmata.*` 5개 | **68,146L** (5,339,610B) | **6,537L** (522,286B) | **-61,609L (-90.41%)** / **-4,817,324B (-90.22%)** | `pp.explicit` 직렬화 덤프 변환 (`361`개 선언 리라이트) |
| └─ **수동 `@` 보존 파일 (31개, 오탐 방지)** | `pp.explicit`가 아닌 일반 수동 택틱 `@` 사용 파일 31개 | **7,075L** (485,917B) | **7,075L** (485,917B) | **0L (0.00%)** | **의도적 무변경 보존** — 수동 `@lemma` 택틱 호출 손상률 **0%** |
| **Lean 4.34.1 단독 코어 하네스 컴파일 검증 완료치** | 구조적으로 서로 다른 **5개 대표 모듈/정리군** (`FixPiIff`, `CovariantDegrees`, `MemOfClosed`, `MulMemIntA`, `Re3`/`Re4` 통합) | 원본 5개 대표 파일 합계 **28,572L** (섀도우 변환 후 **733L**, -97.43%; `Re3` 쌍둥이 포함 6개 **32,241L → 961L**) | 순수 Lean 4 코어 하네스 5개 (총 **907L**, 명시적 `@` vs 탈-elaboration `rfl` 커널 동치 증명 포함) | **5 / 5 컴파일 통과** | `elan run leanprover/lean4:v4.34.1 lean <file>` **전원 `exit 0`, 오류 0, 경고 0, `sorry` 0, `axiom` 0** |

### Round 1 보고서 표기 정밀 보정 (중요 발견)
Round 1 [bloat_report.md](../out/bloat_report.md#L144)에서는 `heavy_explicit_files = 82 (75,221L)`(조건: `reachable ∧ explicit_at_lines ≥ 20 ∧ explicit_at_lines / code_lines ≥ 0.15`)을 요약하여 "`Capelli` 82개 집중 파일"로 통칭했으나, 이번 역추적 결과 정확한 분포는 다음과 같다:
- **`Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.*` 소속**: **46개 파일 / 66,974L / `@` 라인 55,875L** (82개 파일 전체 라인의 **89.04%**, 전체 `@` 라인의 **95.73%**, 전체 절감 라인의 **98.78%**).
- **외부 라이브러리 `pp.explicit` 덤프 (`Lemmata.*`)**: **5개 파일 / 1,172L / `@` 라인 718L** (`Lemmata.GeneralBFactRightTerForm.Imports`, `GeneralBFactLeftAltForm.MQ`, `GeneralBFactLeftVersion.Imports`, `ClearingDenominators.UmonLeUzmon`, `GeneralBFactThirdVersion.Imports`).
- **외부 라이브러리 수동 `@` 파일**: **31개 파일 / 7,075L / `@` 라인 1,772L** (`MultiplicationLatticeSecond` 924L 등 — `pp.explicit` 덤프가 아니라 수동 `@` 호출). `de_explicit_capelli.py`는 이 31개 파일을 자동 판별하여 **단 한 글자도 훼손하지 않고 원문 보존**했다.

---

## 1. `de_explicit_capelli.py` 2계층 안전 AST 엔진 설계

1. **주석·문자열·유니코드·균형 괄호 인식 파서**:
   - `--` 한 줄 주석, 중첩 블록 주석 `/- ... -/`, 문자열 `"..."`, 속성 `@[...]`, as-패턴 `x@⟨...⟩`, 유니버스 레벨 `.{u_1, u_2}` 및 그리스·아래첨자 유니코드 식별자(`Ω`, `σ`, `τ`, `ε`, `Λ`, `ρ`, `χ₁` 등)를 정확히 토크나이징한다.
   - 최상위 선언 분할 시 `attribute [local instance]`, `section`, `end`, `namespace`, `open`, `variable` 명령을 독립 비-선언 블록으로 분리하여 선행 `def` 본문에 흡수되는 버그를 구조적으로 차단한다.
   - 람다 인수 스캔 시 `∀`/`∃` 한정자 깊이(`quant_depth`)를 추적하여 `Set.ofPred (fun a ↦ ∀ v, P v)` 내부의 `,`에서 조기 종료되지 않으며, 타입 표기 `(1 : Complex)` 및 튜플 `(a, b)`의 외곽 괄호는 절대 벗기지 않는다.
2. **Tier 1 — 검증된 스키마 기반 완전 탈-Elaboration (24,465회 적용)**:
   - Mathlib/Core 118개 핵심 심볼(`NumberField`, `RingOfIntegers`, `adicCompletion`, `FiniteAdeleRing`, `ValuativeRel`, `Valuation.integer`, `ResidueField`, `Units`, `Subgroup`, `RingHom`, `AlgHom`, `AlgEquiv`, `LinearMap`, `ContinuousLinearMap`, `TensorProduct`, `Representation`, `Matrix.GeneralLinearGroup`, `HasQuotient.Quotient`, `DFunLike.coe`, `OneHom.toFun`, `Membership.mem`, `Eq`, `LE.le`, `HAdd`/`HMul`/`HSMul`/`HPow`, `OfNat.ofNat`, `ite` 등)의 정확한 인자 개수와 `(명시적)` / `{암묵적}` / `[인스턴스]` 슬롯을 적용.
   - 대상 파일 전체 원문에서 절단 없이(DuckDB 250자 절단 컬럼 미사용) 파싱한 **364개 프로젝트 로컬 바인더 스키마**를 적용하되, (a) `[인스턴스]` 슬롯에서 제거할 인자가 실제 인스턴스 표현식(`@*.to*`, `@*inst*`, `inst_k`, `hl`, `hP`)인지 사중 안전 검증하고, (b) **명시적 인자 타입과 반환 타입 어디에서도 추론할 수 없는 팬텀 암묵 바인더(`{E}`, `{K}` 등)** 는 전이적 추론 가능성 고정점 분석으로 자동 탐지해 명명 인자 `(E := E)` / `(K := K)`로 보존(총 **116회** 적용; 익명 추론 불가 바인더는 안전하게 Tier 2 폴백).
3. **Tier 2 — 미등록 심볼에 대한 항수(Arity) 보존 와일드카드 폴딩 (9,611회 적용, 13,886개 인스턴스 슬롯 축약)**:
   - Tier 1 카탈로그에 없는 `@Head arg₀ ... argₖ`는 **`@Head`, 유니버스 인자 `.{...}`, 그리고 모든 위치 인자 슬롯을 1:1 그대로 보존**하고, 순수 합성 타입클래스 사전(`@*.to*`, `@*inst*`, 표준 Mathlib 사전)인 인자만 `_`로 치환한다. 이로써 알지 못하는 선언의 값·타입 인자가 탈락할 확률이 구조적으로 **0%**가 된다.
4. **자동 사후 무결성 검증 및 v2 회귀 방지 가드 (82개 파일 통과)**:
   - **선언명 100% 보존**: `1,542 / 1,542` (`theorem`/`lemma`/`def`/`abbrev`/`structure`/`class`/`inductive`/`instance`/`axiom`/`opaque`, 탈락 0, 개명 0).
   - **괄호·구분자 균형**: `82 / 82` (`()`, `[]`, `{}`, `⟨⟩` 일치, 안전 롤백 `0`건).
   - **노테이션 인스턴스 누수 검사(`check_notation_instance_leaks`)**: `→L[...]`, `→ₗ[...]`, `⧸` 우변에 타입클래스 인스턴스가 오출력되는 버그 탐지 → **`0 / 82` 파일 (`0`건)**.
   - **금지 토큰 미도입**: 신규 `sorry` `0`건, 신규 `axiom` `0`건, 신규 `admit` `0`건.
   - **v2 수정 내역 (검수 메모 #32 반영)**:
     - `ContinuousLinearMap` 13-인자 스키마 오프바이원 수정: 공역 `M₂` 슬롯을 `args[9]`(`[TopologicalSpace M₂]`)에서 정확한 `args[8]`(`M₂`)로 교정하여 `HloweqTransfer.lean`·`ComplexNormedInstanceCompat.lean`의 `→L[Complex]` 24개소 복구(`(L2 ε) →L[Complex] (L2 ε)`).
     - 팬텀 암묵 바인더 자동 명명 보존(`phantom_named_preserved = 116`): `CovariantDegrees.KwF (E := E)` (최종 섀도우 호출 36/36 보존), `SelectionLemmas.hcompl (K := K)` 및 `loc (K := K)` (3개소), `SquareOfApproximation.IsSplit (E := E)` (1개소) 복구.

---

## 2. 상위 25개 파일별 정적 변환 결과표 (전체 82개 상세는 `capelli_batch_manifest.json`)

| 순위 | 모듈 (`CapelliIdentities.*`는 `CI.` 축약) | Before L | After L | 절감 L (단축률) | Before B → After B | `@` 라인 (전→후) | 선언 (수정/전체) | 선언보존 / 괄호 | 리스크 등급 |
| ---: | :--- | ---: | ---: | ---: | ---: | ---: | ---: | :---: | :--- |
| 1 | `CI.FixPiIff` | 8,029 | 37 | **-7,992 (-99.5%)** | 732,359 → 3,451 | 7,969 → 4 | 1 / 2 | OK / OK | **HIGH** (`complRel`, `isLocalField`), MED |
| 2 | `CI.CovariantDegrees` | 6,170 | 248 | **-5,922 (-96.0%)** | 504,790 → 29,009 | 5,776 → 28 | 25 / 29 | OK / OK | **HIGH** (`aux*`), MED (Alg/Val/Normed) |
| 3 | `CI.MemOfClosed` | 5,746 | 155 | **-5,591 (-97.3%)** | 478,050 → 11,139 | 5,313 → 11 | 10 / 12 | OK / OK | **HIGH** (`aux1`/`algRes`), MED (Val) |
| 4 | `CI.MulMemIntA` | 4,969 | 76 | **-4,893 (-98.5%)** | 405,284 → 8,425 | 4,630 → 9 | 8 / 9 | OK / OK | **HIGH** (`aux3`), MED (Val/Alg) |
| 5 | `CI.HloweqTransfer` (`Re4`) | 3,658 | 217 | **-3,441 (-94.1%)** | 282,214 → 26,224 | 3,020 → 45 | 26 / 27 | OK / OK | **HIGH** (`inst*`), MED (Normed/Meas) |
| 6 | `CI.ComplexNormedInstanceCompat` (`Re3`) | 3,669 | 228 | **-3,441 (-93.8%)** | 283,079 → 27,089 | 3,019 → 44 | 26 / 27 | OK / OK | **HIGH** (`inst*`), MED (Normed/Meas) |
| 7 | `CI.SelectionLemmas` | 3,547 | 390 | **-3,157 (-89.0%)** | 252,719 → 31,813 | 2,941 → 33 | 23 / 34 | OK / OK | **HIGH** (`aux*`) |
| 8 | `CI.FreeModuleQuotient` | 2,516 | 91 | **-2,425 (-96.4%)** | 207,153 → 4,392 | 2,293 → 0 | 1 / 2 | OK / OK | MED (Alg/Quotient) |
| 9 | `CI.ZeroContDiffOnSupported` (`H23`) | 2,229 | 208 | **-2,021 (-90.7%)** | 170,621 → 15,306 | 1,915 → 29 | 16 / 20 | OK / OK | **HIGH** (`aux*`), MED (Val/Topo) |
| 10 | `CI.BorelApproximation` | 2,216 | 196 | **-2,020 (-91.2%)** | 172,169 → 15,838 | 1,915 → 29 | 16 / 20 | OK / OK | **HIGH** (`aux*`), MED (Val/Topo) |
| 11 | `CI.RootEquality` | 2,343 | 744 | **-1,599 (-68.2%)** | 159,339 → 42,679 | 1,377 → 24 | 15 / 54 | OK / OK | MED (Val) |
| 12 | `CI.CoboundaryOfGenerator` | 1,701 | 141 | **-1,560 (-91.7%)** | 120,528 → 13,588 | 1,381 → 31 | 9 / 10 | OK / OK | MED (Topo) |
| 13 | `CI.ImportsMoreExtra` | 1,551 | 67 | **-1,484 (-95.7%)** | 132,081 → 6,902 | 1,411 → 13 | 5 / 5 | OK / OK | **HIGH** (`aux*`), MED (Alg) |
| 14 | `CI.IntegerSpanGenerators` | 1,746 | 270 | **-1,476 (-84.5%)** | 162,957 → 26,873 | 893 → 36 | 2 / 11 | OK / OK | LOW (Tier-2 `_`) |
| 15 | `CI.ConjInvariantCharacterMem` | 1,756 | 295 | **-1,461 (-83.2%)** | 127,799 → 24,264 | 1,216 → 28 | 23 / 31 | OK / OK | **HIGH** (`aux*`), MED (Alg) |
| 16 | `CI.ContDiffHerm` | 1,727 | 290 | **-1,437 (-83.2%)** | 100,791 → 20,955 | 1,078 → 60 | 16 / 29 | OK / OK | **HIGH** (`aux*`), MED (Normed) |
| 17 | `CI.BlockHomomorphism` | 1,484 | 106 | **-1,378 (-92.9%)** | 96,581 → 9,953 | 1,061 → 17 | 10 / 12 | OK / OK | LOW (Tier-2 `_`) |
| 18 | `CI.EqZeroOfForallIntegralCoeff` | 1,180 | 318 | **-862 (-73.0%)** | 85,986 → 22,107 | 811 → 14 | 7 / 25 | OK / OK | **HIGH** (`aux*`), MED (Normed/Topo) |
| 19 | `CI.PhiMul` | 834 | 23 | **-811 (-97.2%)** | 74,945 → 2,889 | 757 → 4 | 1 / 1 | OK / OK | MED (Alg) |
| 20 | `CI.PlaceRankTwoOne` | 1,067 | 334 | **-733 (-68.7%)** | 69,413 → 20,986 | 681 → 17 | 14 / 29 | OK / OK | **HIGH** (`aux*`), MED (Normed/Topo) |
| 21 | `CI.InvolutionInvariants` | 821 | 123 | **-698 (-85.0%)** | 56,921 → 10,959 | 649 → 19 | 13 / 15 | OK / OK | **HIGH** (`aux*`), MED (Normed/Topo) |
| 22 | `CI.UnopSMul` | 646 | 30 | **-616 (-95.4%)** | 56,522 → 2,669 | 609 → 5 | 3 / 3 | OK / OK | MED (Alg) |
| 23 | `CI.FiniteCohomologyOfTrivialOfCyclic` | 608 | 45 | **-563 (-92.6%)** | 48,130 → 4,958 | 534 → 7 | 1 / 2 | OK / OK | LOW (Tier-2 `_`) |
| 24 | `CI.FgZ1T` | 523 | 66 | **-457 (-87.4%)** | 41,317 → 6,901 | 442 → 8 | 1 / 1 | OK / OK | MED (Alg) |
| 25 | `CI.HolSubMul` | 482 | 60 | **-422 (-87.5%)** | 38,164 → 4,881 | 247 → 27 | 3 / 4 | OK / OK | LOW (Tier-2 `_`) |
| — | **나머지 26개 수정 파일** (`CI.` 21개 + `Lemmata.` 5개) | 6,928 | 1,779 | **-5,149 (-74.3%)** | 479,698 → 128,036 | 4,655 → 184 | 86 / 109 | OK / OK | HIGH 2, MED 9 |
| — | **미수정 수동 `@` 파일 (31개)** | 7,075 | 7,075 | **0 (0.0%)** | 485,917 → 485,917 | 1,772 → 1,772 | 0 / 1,019 | OK / OK | — (원문 보존) |
| **합계** | **전체 82개 파일** | **75,221** | **13,612** | **-61,609 (-81.90%)** | **5,825,527 → 1,008,203 (-82.69%)** | **58,365 → 2,498** | **361 / 1,542** | **100% / 100%** | **HIGH 17 / MED 29** |

---

## 3. 암묵적 타입클래스 추론 모호성(Diamond / Non-Canonical Instance) 리스크 감사

탈-elaboration을 실제 Mathlib `v4.33.1` 빌드에 적용할 때 **반드시 확인·보완해야 할 추론 리스크**를 3단계로 자동 분류했다:

1. **HIGH RISK (17개 파일, 809건 탐지) — 비전역(non-global) 커스텀 로컬 인스턴스 제거**:
   - `GlobalTheory.LocalData.complRel` (192건) 및 `GlobalTheory.LocalData.isLocalField` (12건): `FixPiIff.lean`에서 `ValuativeRel` / `IsNonarchimedeanLocalField` 인자로 명시 전달됨. 원 파일 서두에 `attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField`가 없으므로, 탈-elaboration 적용 시 **반드시 해당 1줄을 파일 서두에 추가**해야 한다(단독 하네스 `verify_01_FixPiIff.lean`에서 실증).
   - 프로젝트 내부 보조 인스턴스 `UpperTheory.Reformulated.B.*.aux*` / `algRes` / `inst*` (605건): 예컨대 `MemOfClosed.lean`의 `Qi13.aux1` (`IsLocalRing`) 및 `Qi13.algRes` (`Algebra (ZMod l) (ResidueField ...)`), `CovariantDegrees.lean`의 `aux6`/`aux7`/`aux11`/`aux12` 등은 `theorem`/`def`로 선언되어 글로벌 인스턴스로 등록되지 않았다. 실배포 시 `attribute [local instance]` 부여 또는 `letI` 활성화가 필요하다.
2. **MEDIUM RISK (29개 파일, 3,076건 탐지) — Mathlib 타입클래스 다이아몬드 민감 계열**:
   - `ValuativeRel` / `IsNonarchimedeanLocalField` / `ValuationSubring` (1,492건): `adicCompletion`의 가치환과 `IsDiscreteValuationRing.toIsLocalRing` 경로 간 중복 합성 가능성.
   - `Algebra` / `IsScalarTower` / `SMulCommClass` / `IsAlgClosure` (719건): `CovariantDegrees.lean::aux11`에서 `j.toAlgebra : Algebra Ω (PadicAlgCl l)`처럼 국소 `RingHom.toAlgebra` 인스턴스가 개입하는 경우 `IsScalarTower Rat Ω (PadicAlgCl l)`의 암묵 합성이 실패할 수 있어 `letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra` 유지가 필수.
   - `TopologicalSpace` / `UniformSpace` / `MeasurableSpace` / `MeasureTheory.Lp` (414건) 및 `NormedRing` / `NormedAddCommGroup` / `CStarAlgebra` (413건): `Re3`/`Re4`(`ComplexNormedInstanceCompat`, `HloweqTransfer`)에서 `instMeasurableSpaceUJ` (`borel`)와 `MeasureTheory.Lp`의 노름·내적 공간 인스턴스 간 다이아몬드 주의 (`attribute [local instance] instMeasurableSpaceUJ`는 원문 그대로 보존됨).
   - `CharP` / `HasQuotient` (38건): `FreeModuleQuotient.lean`의 `Submodule.hasQuotient` vs `Ideal.instHasQuotient_1`.
3. **LOW RISK (9,611개 Tier-2 헤드, 13,886개 `_` 슬롯)**:
   - 카탈로그 미등록 Mathlib 헤드(`@RestrictedProduct.evalRingHom`, `@AlgHom.restrictNormal'`, `@MeasureTheory.Lp` 등)는 `@Head`와 위치 항수를 유지한 채 순수 합성 사전 인자만 `_`로 치환했다. Mathlib 엘라보레이터가 `_`를 단일화할 때 타입 힌트가 부족한 극소수 지점만 명시 복원하면 된다.

---

## 4. 5개 구조별 단독 Lean 4.34.1 코어 검증 하네스 컴파일 결과 (`exit 0`)

모든 하네스는 **Mathlib 임포트 0, `sorry` 0, `axiom` 0, `admit` 0** 상태에서 `elan run leanprover/lean4:v4.34.1 lean <file>`로 컴파일했으며, 각 파일마다 **명시적 `pp.explicit` 버전과 탈-elaboration 버전의 커널 정의적 동치(`:= rfl`)** 를 직접 증명했다.

| # | 하네스 파일 | 대응 원본 모듈 · 선언 | 검증 구조 유형 | 코드 줄 | 커널 `rfl` 동치 증명 | `v4.34.1` 결과 |
| ---: | :--- | :--- | :--- | ---: | :--- | :---: |
| 1 | [verify_01_FixPiIff.lean](../harnesses/verify_01_FixPiIff.lean) | `CI.FixPiIff :: Gr34.mem_UC` (8,001L) | `Field → ValuativeRel → ValuationInt → ResidueField → Units → Subgroup` + `local instance` 위험 실증 | 299L | `mem_UC_type_defeq : rfl` | **`exit 0`** (0 err, 0 warn) |
| 2 | [verify_02_CovariantDegrees.lean](../harnesses/verify_02_CovariantDegrees.lean) | `CI.CovariantDegrees :: jE`, `conj_invariant_character_transport` (878L), `rHom` (778L) | `RingHom` / `Algebra` / `AlgAut` / `MonHom` 시그니처 + `def` 본문 탈-elaboration | 142L | `jE_defeq : rfl`, `conj_transport_defeq : rfl` | **`exit 0`** (0 err, 0 warn) |
| 3 | [verify_03_MemOfClosed.lean](../harnesses/verify_03_MemOfClosed.lean) | `CI.MemOfClosed :: Qi13.aux8` (910L), `Qi13.blift` (1,237L) | `def` 본문(`Classical.choose`) + `theorem` 시그니처 동시 탈-elaboration (`aux1` 로컬 인스턴스) | 120L | `aux8_defeq : rfl`, `blift_defeq : rfl` | **`exit 0`** (0 err, 0 warn) |
| 4 | [verify_04_MulMemIntA.lean](../harnesses/verify_04_MulMemIntA.lean) | `CI.MulMemIntA :: Uc13.aux4` (2,650L), `Uc13.mul_mem_intA` (1,364L) | `FiniteAdeleRing` / `TensorProduct` / 부분대수 폐포 이중 귀납(`IntA`) | 155L | `aux4_defeq : rfl`, `mul_mem_intA_defeq : rfl` | **`exit 0`** (0 err, 0 warn) |
| 5 | [verify_05_Re3Re4_unified.lean](../harnesses/verify_05_Re3Re4_unified.lean) | `CI.ComplexNormedInstanceCompat` (`Re3`, 3,669L) + `CI.HloweqTransfer` (`Re4`, 3,658L) | 쌍둥이 파일 중복 제거 + `CStarAlgebra` / `NormedAddCommGroup` / `InnerProductSpace` 탈-elaboration + 호환 별칭 | 191L | `hloweq_type_defeq : rfl` | **`exit 0`** (0 err, 0 warn) |
