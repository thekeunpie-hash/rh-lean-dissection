# Round 2 RH/GRH 노트 검수

- **검수 대상**: Lean 4.33.1 RH/GRH 리포지토리(`../lean/src/`, 175,187 모듈) Round 2 전 트랙 산출물
  - **Track A (`audit`)**: [meta_audit_verdict.md](meta_audit_verdict.md) (563L)
  - **Track B (`proof notes`)**: [rosetta_stone.md](rosetta_stone.md) (286L), [rh_proof_explained.md](rh_proof_explained.md) (377L)
  - **Track C (`compression`)**: [capelli_batch_report.md](capelli_batch_report.md) (114L), [unitary_dedup_plan.md](unitary_dedup_plan.md) (104L), [tactic_golf_report.md](tactic_golf_report.md) (103L), [de_explicit_capelli.py](../scripts/de_explicit_capelli.py) (1,639L), `capelli_shadow/` (82파일), [UnifiedSWeqOm.lean](../poc/UnifiedSWeqOm.lean) (251L), [golfed_RingObjectsOfMatrixData.lean](../poc/golfed_RingObjectsOfMatrixData.lean) (598L), 7개 단독 Lean `v4.34.1` 하네스
- **검수 도구 및 원시 증빙**:
  - [verify_round2.py](../scripts/verify_round2.py) (514L — Unicode 대응 DuckDB+디스크 참조 검증, 82파일 섀도우 감사, Lean `v4.34.1` 하네스 독립 컴파일, `RingObjectsOfMatrixData` 시그니처·무결성 검사)
  - [critic_sig_dump.txt](../out/critic_sig_dump.txt) (1,142L — Track B 18개 핵심 정리 원시 시그니처 덤프)
  - [critic_trackc_verify.json](../out/critic_trackc_verify.json) (v1) / [critic_trackc_verify_v2.json](../out/critic_trackc_verify_v2.json) (v2 최종)
- **검증 툴체인**: `elan run leanprover/lean4:v4.34.1 lean <file>` (`v4.33.1` 미설치 및 `.lake/` 부재 환경 규칙 엄수; `lake build` 및 `src/` 전역 grep 미실행)

---

## 0. 검사

| 트랙 | 노트 | 검수 회차 | 발견 결함 → 수정 완료 | 자동 참조 정확도 (실제 리포 참조) | 단독 컴파일 / 구조 무결성 | 최종 판정 |
| :--- | :--- | :---: | :---: | :---: | :--- | :---: |
| **Track A** | `audit` | 1차 즉시 통과 | 0건 결함 | **257 / 257 (100.0%)** *(비리포 stdlib/구간 표기 22건 제외)* | `CutCptCopy`·`BuildAid/D1..D5`·4 `elab`·2 `partial def`·RH/GRH 경계조건 대조 통과 | **통과** |
| **Track B** | `proof notes` | **v1 → v2 (1회 완결)** (`#26`→`#27`→`#28`) | **10건 적발 → 10/10 수정** | **`rosetta_stone.md` 433 / 433 (100.0%)** / **`rh_proof_explained.md` 336 / 336 (100.0%)** | 18개 핵심 정리 원시 시그니처 직접 교차검증 18/18 통과, 9대 개념 이름 대조 통과, Mermaid 유효 | **통과** |
| **Track C** | `compression` | **v1 → v2 (1회 완결)** (`#32`→`#33`) | **4건 적발 → 4/4 수정** *(치명 버그 3건 포함)* | **115 / 115 (100.0%)** *(Mathlib/제안모듈/변경이력 14건 제외)* | 82파일 섀도우 무결성(`0` leaks, `116` phantom 보존), `RingObjects` 시그니처 100% 일치·`mkRingInst` 수정 검증, **7/7 하네스 `exit 0`** | **통과** |

**원본 불변성 검증 (`downloads/lean/src/` 무수정 확증)**: `capelli_shadow/` 대응 82개 원본 파일 + `Main.lean` + `RingObjectsOfMatrixData.lean` 등 핵심 84개 원본 파일의 mtime 조사 결과 Round 2 시작 시점(`2026-11-21T06:30:00Z`) 이후 수정된 파일 **0건** (최신 mtime `2026-11-21T05:06:36Z`). 모든 산출물은 `downloads/lean-analysis/teamwork_out/round2/` 하위에만 격리 기록되었다.

---

## 1. 자동 검증 통합 지표 (`verify_round2.py` 독립 실행 결과)

### 1.1 Markdown 산출물 `Module.decl` · 파일 참조 검증표

| 대상 산출물 | 총 검사 토큰 | 스크립트 PASS | WARN | 스크립트 FAIL (비리포/파서 아티팩트 내역) | **실제 리포 참조 정확도** |
| :--- | ---: | ---: | ---: | :--- | :---: |
| `round2/meta_audit_verdict.md` | 279 | 257 | 0 | 22건 전부 비리포/서식(Lean 4 stdlib 파일·API 17건 `Lean/AddDecl.lean` 등, 범위 약어 `BuildAid/D1..D5.lean` 1건, Python 리스트 리터럴 4건) | **257 / 257 (100.0%)** |
| `round2/rosetta_stone.md` (v2) | 433 | **433** | **0** | **0건** | **433 / 433 (100.0%)** |
| `round2/rh_proof_explained.md` (v2) | 336 | **336** | **0** | **0건** | **336 / 336 (100.0%)** |
| `round2/compression/capelli_batch_report.md` (v2) | 43 | 40 | 0 | 3건 전부 비리포(접두 약어 `Lemmata.` 1건, 실제 Mathlib 인스턴스/투영 `IsDiscreteValuationRing.toIsLocalRing`·`Ideal.instHasQuotient_1` 2건) | **40 / 40 (100.0%)** |
| `round2/compression/unitary_dedup_plan.md` (v2) | 62 | 53 | 0 | 9건 전부 비리포(표 행 매칭 `True`/`hsm` 3건, 설계 제안 모듈 `Common.*`·PoC `IsAdmCfg.toBase` 6건) | **53 / 53 (100.0%)** |
| `round2/compression/tactic_golf_report.md` (v2) | 24 | 22 | 0 | 2건 전부 비리포(v2 오기 교정 이력 문장 내 `Subalgebra.adjoin` 1건, 실제 Mathlib 보조정리 `Fintype.card_pos_iff.mp` 1건) | **22 / 22 (100.0%)** |
| **전 트랙 합계** | **1,177** | **1,141** | **0** | **실제 리포 참조 오류 0건** | **1,141 / 1,141 (100.0%)** |

### 1.2 독립 Lean `v4.34.1` 하네스 재컴파일 결과 (`elan run leanprover/lean4:v4.34.1 lean`)

| # | 하네스 / PoC 파일 | 줄 수 | 컴파일러 실행 | 종료 코드 | `sorry` / `axiom` / `admit` / `unsafe` | 검증 내용 |
| ---: | :--- | ---: | :---: | :---: | :---: | :--- |
| 1 | [verify_01_FixPiIff.lean](../harnesses/verify_01_FixPiIff.lean) | 299L | `v4.34.1` | **`exit 0`** | **0** | `Gr34.mem_UC` 명시적 vs 탈-elaboration `rfl` 동치 + `local instance` 리스크 실증 |
| 2 | [verify_02_CovariantDegrees.lean](../harnesses/verify_02_CovariantDegrees.lean) | 142L | `v4.34.1` | **`exit 0`** | **0** | `jE`/`conj_invariant_character_transport`/`rHom` 시그니처·본문 `rfl` 동치 |
| 3 | [verify_03_MemOfClosed.lean](../harnesses/verify_03_MemOfClosed.lean) | 120L | `v4.34.1` | **`exit 0`** | **0** | `Qi13.aux8`/`blift` (`Classical.choose` + `aux1` 로컬 인스턴스) `rfl` 동치 |
| 4 | [verify_04_MulMemIntA.lean](../harnesses/verify_04_MulMemIntA.lean) | 155L | `v4.34.1` | **`exit 0`** | **0** | `Uc13.aux4`/`mul_mem_intA` 부분대수 폐포 이중 귀납 `rfl` 동치 |
| 5 | [verify_05_Re3Re4_unified.lean](../harnesses/verify_05_Re3Re4_unified.lean) | 191L | `v4.34.1` | **`exit 0`** | **0** | `Re3`/`Re4` 쌍둥이 통합 + `Normed`/`InnerProduct`/`CStar` `rfl` 동치 |
| 6 | [verify_RingObjectsOfMatrixData_core.lean](../harnesses/verify_RingObjectsOfMatrixData_core.lean) | 272L | `v4.34.1` | **`exit 0`** | **0** | `RingObjectsOfMatrixData` 7개 핵심 추출 헬퍼 패턴 순수 코어 증명 (`Algebra.adjoin` 교정 완료) |
| 7 | [verify_unitary_unified_core.lean](../harnesses/verify_unitary_unified_core.lean) | 221L | `v4.34.1` | **`exit 0`** | **0** | `VolStabCfg` 3축 통합 `sWeqOm_of`, 3개 인스턴스 복원, `SWc1 → SWc1W → FirstChern` 단조성 |
| 8 | *(보조 스니펫)* `mkRingInst` v2 수정 패턴 (`rw [hρk, hρk, hsm, mul_smul]`) | stdin | `v4.34.1` | **`exit 0`** | **0** | `#32`에서 적발한 `L357` defeq 실패(`exit 1`)의 v2 수정안 커널 통과 직접 재확인 |
| — | *(Mathlib 드롭인)* [UnifiedSWeqOm.lean](../poc/UnifiedSWeqOm.lean) | **251L** (코드 187L) | Skip(Mathlib) | — | **0** | 3파일 `SWeqOm.lean` + 3개 컨텍스트 통합 드롭인 PoC (헤더·보고서 251L/187L 일치) |

---

## 2. Track A (`audit`) 독립 대조 감사 요약

[meta_audit_verdict.md](meta_audit_verdict.md)의 모든 핵심 주장을 `downloads/lean/src/` 원시 소스, `lean_index.duckdb`, 그리고 로컬 Lean 4 stdlib 소스(`../lean-toolchain/src/lean/Lean/{AddDecl,Environment,LibrarySuggestions/Basic}.lean`)와 직접 대조한 결과 **결함 0건**으로 1차 검증을 통과했다:

1. **`CutCptCopy.lean` 메타프로그래밍 커널 우회 여부 (무결성 확인)**:
   - 원시 소스 91줄 직접 확인: `addDecl (.defnDecl ...)` 및 `addDecl (.thmDecl ...)` 호출이 모두 `Lean.addDecl` → `Environment.addDeclCore` → C++ 커널 `lean_add_decl`을 경유한다. 리포지토리 전역 `debug.skipKernelTC = 0`, `addDeclWithoutChecking = 0`.
   - `partial def go`는 컴파일 타임 메타 `Expr` 치환기이며 커널에 제출되는 결과 항(`value`)에는 포함되지 않는다.
   - `CutMainCpt.lean:475, 944-945`에서 `cpt_copy_thms`로 생성된 `block_growth_bound_of_compact_coefCpt`가 `FinalS.lean:60-61`에서 실제 소비됨을 원시 확인.
2. **`BuildAid/D1..D5.lean` 확인 (무해한 검색 거부 목록)**:
   - 5개 파일 전부 정확히 4줄 구조(`initialize Lean.LibrarySuggestions.nameDenyListExt.addEntry ...`)로 `grind`/라이브러리 제안 필터링에만 작용하며 논리적 공리·커널 상태에 0% 영향.
   - 임포터 수(3 / 4 / 25 / 5 / 1) 및 `Main` 기준 최단 깊이(13 / 12 / 8 / 8 / 19)와 `MainTheorems` 기준 최단 깊이(12 / 11 / 5 / 6 / 18)가 DuckDB 조회와 100% 일치.
3. **전체 메타·옵션 인벤토리 대조**:
   - 4개 `elab`(`cpt_copy_thms`, `kexactB`, `kcopy`, `#kcopy_probe`), 2개 `partial def`(`go`, `copyAt`), 22개 전역 `macro`(`NegOnePowBoundaryTermsCancel:114`, `RttUpperRelationsFromDescent:30`, `Theta1:25` 스팟 대조), 37건 `allowUnsafeReducibility`, 31건 `hygiene`, 13건 기타 특수 `set_option` 전부 원시 코드와 일치하며 커널 건전성 위반 0건.
4. **RH / GRH 명제 경계조건 감사 (`Statements.lean`, `Main.lean`, `CritLine.lean`, `RhOfRight.lean`, `ClaimStrip.lean`, `EveryCharacter.lean`, `Imprimitive.lean`, `HalfPlane.lean`, `poleData.lean:196`, `CharFamilyLFunctionNeZeroOfOneLeRe.lean:17-20`, `PrimePairSizeCondition.lean:19`, `RiemannHypothesisOfEveryCharacter.lean:219`)**:
   - 자명영점 $s = -2(n+1)$ 배제, $s = 0$의 비영성(`riemannZeta_zero` 경유 3개 경로 전부 증명), $s = 1$ 극점 처리 및 `Imprimitive.lean:10-20` 대 `ZeroFreeAll`의 미묘한 차이(비원시 주지표 $N>1$의 오일러 인자 비영성 $\operatorname{Re}(s)>0$, `[NeZero N]`), 경계선 $\operatorname{Re}(s)=0, 1$ 처리, 임계대 점별 동치성 모두 누락 없이 정확히 기술됨.
5. **`SmallClassNumbers` 8모듈 콘 격리 검증**:
   - DuckDB ASCII 콘 차집합(`Main` − `MainTheorems`) = 정확히 8모듈(`Main`, `Statements`, `MainTheoremsAll`, `MainTheoremsCritical` + `SmallClassNumbers.{CorGKOf, ClassNumberThree, LenEqZeroIff, OnePoint}`); Unicode 포함 전체 콘에서도 `175,187 - 175,179 = 8`로 완전 일치.

---

## 3. Track B (`proof notes`) 18개 핵심 정리 원시 시그니처 교차검증 및 v1→v2 수정 감사

### 3.1 18개 핵심 정리 원시 Lean 시그니처 직접 교차검증표 (`>=10` 요건 대폭 초과)

모든 18개 선언의 원시 타입 시그니처를 `downloads/lean/src/`에서 직접 읽어([critic_sig_dump.txt](../out/critic_sig_dump.txt) 및 직접 열람 파일) 산문 번역에서 **가설 밀반입(smuggling)** 또는 **필수 조건 누락(dropping)** 이 없는지 v1·v2 양쪽에서 검사했다.

| # | Lean 선언 (모듈 · 원시 행) | 핵심 원시 시그니처 검증 포인트 | v1 적발 결함 (`#26`) | v2 재검증 결과 (`#27`→`#28`) |
| ---: | :--- | :--- | :--- | :---: |
| 1 | `Formalism.StatementOC.Gz` / `Formalism.HC.Level.Gm` (`StatementOC.lean`, `ExplicitFormulaErrorOfHostConditions.lean`) | `Sz x - x * log x + (1 + γ) * x`, 레벨별 가중 폰 망골트 합 | 결함 없음 (Alpöge 공지 식과 1:1 일치) | **PASS** |
| 2 | `Formalism.HC.level_of_tiedWin` (`TopWin.lean:27, 31, 68-71`) | `ChebyshevInequalityOnWindows`: `0 < eps`만 요구; `ChebyshevInequalityAtWindowScale`: `0 < ε₁`만 요구 (`eD, eL : ℝ` 부호 제약 없음) | **결함 #1**: 산문에 `e_D, e_L > 0` 가설 밀반입 | **FIXED & PASS** (`e_D, e_L ∈ ℝ`로 교정) |
| 3 | `BehrendSets.{WindowTwo, OrbitOne}` (`BehrendSets/Statement.lean:67-75`) | `L : ℕ` (`L ≥ 1` 없음); `BehrendFree (2*L) T`는 `WindowTwo` 소속 | **결함 #2**: `L ≥ 1` 밀반입 + `BehrendFree (2L) T`를 `OrbitOne`에 오귀속 | **FIXED & PASS** (원시 귀속 복원) |
| 4 | `SizeWindows` / `SizesTextAt` (`GrowthBoundGivesRiemannHypothesis.lean:109-117`, `SChain.lean:207-227`) | `SizeWindows`: `0 < n`만 명시적 양수 조건; `SChain.lean:215`는 상한 `< ... + 1`, 하한은 `RestSize` (`L225`) | **결함 #3**: 상·하한 출처 혼동 및 행번호 범위 부정확 | **FIXED & PASS** (`L207-227`·`RestSize L225` 정확 분리) |
| 5 | `Formalism.HN.TheoremF` / `TheoremFSharp` (`StatementFrameF.lean:26-100`) | `0 < ∑ i, card (ι i)` (`L41`), 상단 블록 결합 `Ball i (Sum.inl k) j = (Y'⁻¹ * emb_v(toMatrix B_i) * Y i) k j` (`L48-49`) | **결함 #4a**: 상단 블록 결합 조건 및 총 차원 양수 조건 누락 | **FIXED & PASS** (두 조건 모두 명시 복원) |
| 6 | `MeanBoundSecondForm` (`MeanBoundSecondForm.lean:187-190`) | `Nonempty U0 → D.HidaSetting C → ... → umean D.ASK ≤ umean D.Main + D.ErrX C` | **결함 #4b**: 선행 가설 `Nonempty U0` 누락 | **FIXED & PASS** (`Nonempty U0` 명시 복원) |
| 7 | `LinkDIV_at` (`GlobalTheoremInputs.lean:77-89`) | 9개 연언항 — 특히 3번째 `∀ u` 항 (`L85-86`: `log(g 0 * g 1)` 오차 `≤ C * L.B0`) 포함 | **결함 #5a**: `L85-86` `log(g_0 * g_1)` 연언항 누락 | **FIXED & PASS** (전 연언항 복원) |
| 8 | `LinkG_at` (`GlobalTheoremInputs.lean:122-136`) | 공집합 소멸(`L126`), `Sv ≤ 2 m Nv a / p`(`L127-128`), `ServedOrbitsContained ∧ MeanKappaBound`(`L136`) 포함 | **결함 #5b**: 위 3개 연언항 누락 | **FIXED & PASS** (3개 연언항 전부 복원) |
| 9 | `LinkS` / `LinkS_at` / `linkS_selH` (`GlobalTheoremInputs.lean:145-156`, `ThmSOwn.lean:925`) | `LinkS`는 `C0 : ℝ` 자유(별도 `1 ≤ C0` 없음); `1 ≤ C0`는 `linkS_selH`에 속함 | **결함 #5c**: `1 ≤ C0`를 `LinkS` 자체 가설로 오기 | **FIXED & PASS** (`LinkS` vs `linkS_selH` 정확 구분) |
| 10 | `PI.BesselMapUniq.BesselMapUniq` (`BesselMapUniq.lean:50-59`) | `IsHCParam lam`, `IsDSHpk`, `inWb k r z`, `0 < Tz k r z`, `∀ a, c a ≠ 0`, `IsHCTypeW` | **결함 #6a**: `inWb`, `0 < Tz`, `IsHCTypeW` 3조건 누락 | **FIXED & PASS** (3조건 전부 복원) |
| 11 | `PoincareSetting.{InHH, Pu}` (`PoincareInHH.lean:194-218`) | `InHH`는 `Prop`; `Pu`는 `hD : IsReps`, `hin : InHH`, `hlin : PuLinear`를 받아 선형사상 `Cu →ₗ[ℂ] HHX` 구성 | **결함 #6b**: `InHH` 성격 및 `Pu`의 `IsReps`/`InHH`/`PuLinear` 전제 미명시 | **FIXED & PASS** (전제·타입 정확 서술) |
| 12 | `WuDecayOfGap` / `GlobalTheory.wuDecayOfGap` (`WuDecayAll.lean:25-27, 1058`; `FlagMeasures/WuDecayOfGap.lean:7`) | 조건부 10-가설 정리(`WuDecayAll.lean:1058`) vs 0-가설 완결 정리(`FlagMeasures/WuDecayOfGap.lean:7`) | **결함 #6c**: 조건부 정리와 최종 무가설 완결 정리 구분 모호 | **FIXED & PASS** (두 위치 명시 분리) |
| 13 | `Formalism.GaloisCohomology.{Sha, shaLen, VLen, PTCoker, PTSha}` (`GaloisCohomology/Statement.lean:75-116`) | `shaLen`/`VLen : ℕ∞`, Poitou–Tate `PTCase : l ≠ 2 ∨ nrRealPlaces F = 0` | 결함 없음 (Weak Vandiver / Lichtenbaum $H^1$/$H^2$ 실체 정확 포착) | **PASS** |
| 14 | `UpperTheory.Top.VVle` & `SmallClassNumbers.{Bound, Large}` (`ExistsPageN.lean:14`, `ClassNumberThree.lean:17-20`, `LenEqZeroIff.lean:65-68`) | `shaLen ≠ ⊤` (`ENat.toNat ⊤ = 0` 방지 핵심!), `1 ≤ e`, `Even e`, `5 ≤ l`, `¬(l-1 ∣ 2e)`, `len ≠ ⊤`, `eO = 1` | **결함 #7**: `rosetta_stone.md`에서 `shaLen ≠ ⊤` 및 `SmallClassNumbers` 전제조건 누락 | **FIXED & PASS** (유한성·산술 전제 전부 복원) |
| 15 | `UpperTheory.V.HV.Core.of_four_alt` (`HVCore.lean:18-21`) | `LiteratureRankNHypothesis`, `∃ CK, LemmaK CK`, `CountI..CountIII`, `CountV` → `VWin` | 결함 없음 (Ferrero–Washington 경유 조합 정확) | **PASS** |
| 16 | `UpperTheory.Lit.Rallis.RallisIPProof.rallis_of_dm` & `rallis_inner_product_big_theta_lift` (`RallisDM.lean:24-25`, `BigThetaNormEqRallisInnerProduct.lean:47`) | `DM → SiegelWeilUnitaryConvergent → WeilThetaConvergence → RallisInnerProductConvergent`; 빅 세타 리프트는 `ThetaLocalInputs` 하 `∃ P, ν, 𝓕, c` 존재 진술 | **결함 #9**: `rallis_inner_product_big_theta_lift`의 존재양화사 및 `ThetaLocalInputs` 전제 미명시 | **FIXED & PASS** (존재 진술 및 전제 명시) |
| 17 | `GlobalTheory.Unf.Chain` & `Row0b`/`PropsB` (`IsThetaFam.lean:149-205`, `RowSrc.lean:6`, `WeightsConjBis.lean:55-73`) | 귀납 체인 `Chain.{last, step}` + `Row0b`/`PropsB` 6개 필드(`weights` 포함) | **결함 #10**: `PropsB` 필드 목록에서 `weights` 누락 | **FIXED & PASS** (6/6 필드 완비) |
| 18 | `weighted_von_mangoldt_sum_identity` & `meanSqK` & `recTExists` (`WeightedVonMangoldtSumIdentity.lean:227`, `meanSqK.lean:51`, `RecTExists.lean:20`) | `0 < a`, `0 < w`, `⌊a/w⌋₊ ≤ M`; `meanSqK` 소인수 분기 `≤ Y^(ε/5) ∨ (Y^K)^400 < p`; `recTExists` 12필드 완결 | **결함 #8** *(연관)*: `O2` 모듈 수 오기(`10` → DuckDB 정확치 `4` 대소문자구분 / `5` 비구분 `Two2`) 및 `GL5LogLValueBoundByZeta` 선언 감사 보강 | **FIXED & PASS** (정확 계수 + 선언 감사 추가) |

### 3.2 아홉 가지 이름 대조

- **키워드-부재 오류("keyword absent = concept absent") 차단 통과**:
  - Round 1의 키워드 검색 0건 오판을 실제 Lean `def`/`theorem` 시그니처 분석으로 정면 번복한 **⑦ Bost (기울기 부등식)** (`Formalism.HN.{muDef, TheoremF, TheoremFSharp}` + `MeanBoundSecondForm`) 및 **⑨ Weak Vandiver / Lichtenbaum $H^1$/$H^2$** (`Formalism.GaloisCohomology.{Sha, shaLen, VLen, PTCoker, PTSha}` + `UpperTheory.Top.{VVle, VWin}`) 매핑은 원시 코드와 100% 정합하다.
  - `GL1..GL6`(`Formalism.LocalToGlobal.GlobalTheory.*`)이 $\mathrm{GL}_5$ 6중 덮개가 아닌 **Global Lemma/Layer** 계층이며 `GL5`는 `GenusMassVolumes`(유니타리 Siegel–Weil 질량비)임을 파일·선언 단위(`GL5LogLValueBoundByZeta` 포함)로 입증했다.
  - 9개 항목 전부 원시 코드 근거 없는 추측이 없으며, `rh_proof_explained.md`의 전체 의존성 Mermaid `flowchart TD` 문법도 유효하다.

---

## 4. Track C (`compression`) 6-샘플 섀도우 딥-디프 감사, `RingObjects` 무결성 및 v1→v2 수정 루프

### 4.1 `capelli_shadow/` 6-샘플 딥-디프 및 버그 수정 대상 파일 감사표 (5-샘플 요건 초과)

| # | 대상 파일 (`CapelliIdentities.*`) | 원본 → v2 섀도우 (줄 / LF바이트 / `@` 토큰) | v1 적발 버그 (`#32`) | v2 원시 디프 최종 검증 결과 (`#33` 재검증) | 판정 |
| ---: | :--- | :--- | :--- | :--- | :---: |
| 1 | `FixPiIff.lean` | `8,029L → 37L` (-99.5%) / `732,359 → 3,451B` / `@: 9,300 → 12` | 없음 (`local instance` 필요성 정직 문서화 확인) | `fix_pi_iff` 원문 100% 보존, `mem_UC` 바인더·유니버스·명시적 값 인자(`ρ`, `C`, `m`) 완전 보존, 잔여 12개 `@`는 안전 Tier-2 | **PASS** |
| 2 | `CovariantDegrees.lean` | `6,170L → 248L` (-96.0%) / `504,790 → 29,009B` / `@: 15,334 → 145` | **치명 버그 #2**: `KwF`의 팬텀 암묵 바인더 `{E}` 31회 탈락(원본 수동 증명이 `KwF (E := E) j` 명시) | v2 전이적 추론 가능성 고정점 엔진으로 **`KwF (E := E) j` 36/36 (100%) 보존**, 미명명 `KwF` 호출 0건, 29/29 선언 보존 | **FIXED & PASS** |
| 3 | `MemOfClosed.lean` | `5,746L → 155L` (-97.3%) / `478,050 → 11,139B` / `@: 10,016 → 29` | 없음 | `key`·`mem_of_closed` 택틱 증명 원문 보존, `aux1`..`linIndep` 12/12 선언·값 인자·`Classical.choose` 정확 보존 | **PASS** |
| 4 | `MulMemIntA.lean` | `4,969L → 76L` (-98.5%) / `405,284 → 8,425B` / `@: 6,368 → 24` | 없음 | `intAf_mul`·`mul_mem_intA` (`AddSubgroup.closure_induction₂`) 원문 보존, `evalV`·`intAf`·`intA` 9/9 선언 정확 보존 | **PASS** |
| 5 | `FreeModuleQuotient.lean` | `2,516L → 91L` (-96.4%) / `207,153 → 4,392B` / `@: 4,159 → 0` | 없음 | `aux` 81줄 증명 원문 보존, `freeN_quot` 시그니처 `@` 100% 제거에도 바인더·`⧸` 몫모듈 노테이션 무결 | **PASS** |
| 6 | `HloweqTransfer.lean` (`Re4`) | `3,658L → 217L` (-94.1%) / `282,214 → 26,224B` / `@: 3,585 → 194` | **치명 버그 #1**: `ContinuousLinearMap` 13-인자 오프바이원(`args[9]` 사용)으로 12개 `→L[Complex]` 공역이 `@UniformSpace.toTopologicalSpace ...`로 파손 | `args[8]` 교정 후 13/13 `→L[Complex]` 전부 `(L2 ε) →L[Complex] (L2 ε)` / `H →L[Complex] H` 정상 출력, 누수 0건 | **FIXED & PASS** |
| 7* | `ComplexNormedInstanceCompat.lean` (`Re3`) | `3,669L → 228L` (-93.8%) / `283,079 → 27,089B` / `@: 3,584 → 193` | **치명 버그 #1**: 동일 오프바이원 12개소 | 13/13 `→L[Complex]` 전부 정상 복구, 누수 0건 | **FIXED & PASS** |
| 8* | `SelectionLemmas.lean` | `3,547L → 390L` (-89.0%) / `252,719 → 31,813B` / `@: 5,343 → 254` | **치명 버그 #2**: `hcompl` 1회·`loc` 2회 `{K}` 팬텀 암묵 바인더 탈락 | `hcompl (K := K)` (L111), `loc (K := K)` (L120 ×2) 복구 | **FIXED & PASS** |
| 9* | `SquareOfApproximation.lean` | `658L → 246L` (-62.6%) / `43,667 → 15,839B` / `@: 617 → 46` | **치명 버그 #2**: `IsSplit` 1회 `{E}` 팬텀 암묵 바인더 탈락 | `IsSplit (E := E) v` (L241–242) 복구 | **FIXED & PASS** |

- **전체 82개 파일 일괄 검증 (`verify_round2.py --capelli-shadow` + `capelli_batch_manifest.json` 대조)**:
  - 총 `75,221L → 13,612L (-61,609L, -81.90%)`, LF 기준 `5,825,527B → 1,008,203B (-4,817,324B, -82.69%)` *(Windows CRLF 디스크 파일 크기 합은 `1,021,815B = +13,612B`, 줄당 1바이트 차이로 정상)*, `@` 토큰 `96,892 → 5,314`, `@`-라인 `58,365 → 2,498`.
  - 선언명 보존 **`1,542 / 1,542` (100%)**, 괄호 균형 **`82 / 82` (100%)**, 금지 토큰(`sorry`/`axiom`/`admit`/`unsafe`/`native_decide`) **0건**, `notation_instance_leaks` **0건** (`check_notation_instance_leaks()` 가드 내장 확인), `phantom_named_preserved = 116` (스캔 시 의심/인스턴스 오삽입 **0건**), 수동 `@` 31개 파일 **0바이트 무변경 보존**.

### 4.2 `golfed_RingObjectsOfMatrixData.lean` 명제 동치성 및 택틱 무결성 판정

- **문자 단위 100% 시그니처 일치 검증 (`verify_round2.py --check-golf`)**:
  - `theorem ring_objects_of_matrix_data (hEM : StatEMat) (hSP : StatSplitPts) (hKO : StatIdemKO) : RingObjectsExist := by` — 원본 `RingObjectsOfMatrixData.lean:109`와 **문자 단위 100% 일치** (가설 추가 0, 결론 약화 0).
  - 공개 보조정리 `theorem rank_block` 및 `theorem eDiag'` 역시 원본과 **100% 일치**.
  - 금지 토큰(`sorry`, `axiom`, `admit`, `unsafe`, `native_decide`, `lcProof`, `implemented_by`, `sorryAx`) **0건**, 괄호 균형 오류 **0건**.
- **택틱 건전성 적대적 검증 및 `#32` 버그 수정**:
  - v1 감사 중 `mkRingInst` L357의 `show ρπ (f • a) i.1 j.1 • ...`가 추상 함수 `ρk`에 대해 정의적 동치를 가정하여 Lean 4에서 실패(`exit 1`)하고 `hρk`가 미사용 상태임을 Lean `v4.34.1` 축소 재현기로 직접 적발(`#32`).
  - v2에서 `rw [hρk, hρk, hsm, mul_smul]`으로 교정되었으며, 동일 패턴을 `elan run leanprover/lean4:v4.34.1 lean --stdin`으로 독립 실행하여 **`exit 0`** 확인 완료.
  - 기타 의심 구간(`omega` Fin 동치 L596, `simp [hbd _ i j hij]` L441, `hf ▸` L573)은 모두 Lean `v4.34.1` 테스트에서 합법적임을 사전 검증하여 오탐 0건 유지.
- **정량 지표 정합성**:
  - 목표 정리 본문: `477L → 220L (-53.9%)` (코드 본문 `473L → 208L, -56.0%`; 스팬 `478L → 221L`).
  - 본문 내 `have`/`haveI`: 선두 `92 → 51 (-44.6%)` / 전체 토큰 `98 → 53 (-45.9%)` (`have` 52 + `haveI` 1).
  - `by_cases`: `17 → 5 (-70.6%)`, `let`/`letI`: `35 → 30 (-14.3%)`, 파일 전체: `588L → 598L` (순 코드 `576L → 549L, -4.7%`), 16개 `private` 격리 헬퍼 추출.
  - Mathlib `v4.33.1` 의존 API(`Algebra.adjoin` 오기 교정 완료) 및 실제 `maxHeartbeats` 측정 경계가 정직하게 분리 명기됨.

### 4.3 `UnitaryGroupMassFormula` 3중 클론 분석 및 통합 PoC 감사

- 448모듈 / 57,658L 중 143개 트립릿(55,593L; 61개 3자 100% + 54개 2자 100% + 115/143 선언명 집합 100% 일치)을 가르는 3개 직교 축(`dimBound`: `a+2≤M` vs `2a<M`, `archExtra`: `True` vs `IsSmoothCc`, `swInput`: `SWc1` vs `StabilizerFirstChernCompatibility` vs `SWc1W`)과 단조성(`1 ≤ a → 2a < M → a + 2 ≤ M`)이 원시 파일 근거와 정확히 부합.
- [UnifiedSWeqOm.lean](../poc/UnifiedSWeqOm.lean) 실측 **251L (코드 187L)** — v2에서 헤더(L12–16) 및 [unitary_dedup_plan.md](unitary_dedup_plan.md#L93)와 1줄 오차 없이 동기화 완료 (`sorry`/`axiom` 0건).
- [verify_unitary_unified_core.lean](../harnesses/verify_unitary_unified_core.lean) (221L) 독립 Lean `v4.34.1` 컴파일 **`exit 0`** (0 err, 0 warn, 0 `sorry`, 0 `axiom`).

---

## 5. 수정 루프 이력 (Revision Loop Changelog)

| 트랙 | 피드백 보드 번호 | 수정 보고 번호 | 수정 완료 항목 요약 | 재검증 상태 |
| :--- | :---: | :---: | :--- | :---: |
| **Track A** (`audit`) | — | `#24` | 1차 감사에서 원시 코드·stdlib·DuckDB 대조 결함 0건 | **1차 PASS → 통과** |
| **Track B** (`proof notes`) | `#26` | `#27` | 10/10 결함 수정: `level_of_tiedWin` `eD,eL∈ℝ`, `WindowTwo`/`OrbitOne` 귀속, `SizesTextAt` 상하한 분리, `TheoremF` 블록 결합·`MeanBoundSecondForm` `Nonempty U0`, `LinkDIV_at`/`LinkG_at`/`LinkS` 누락항·`1≤C0` 분리, `BesselMapUniq`/`PoincareSetting.Pu`/`WuDecayOfGap` 전제·위치 분리, `VVle` `shaLen≠⊤` 및 `SmallClassNumbers` 전제, `O2` 계수(`4`/`5`)·`GL5LogLValueBoundByZeta`, `rallis_inner_product_big_theta_lift` 존재양화사, `PropsB`의 `weights` 필드 추가 | **재검증 100% PASS (`#28`) → 통과** |
| **Track C** (`compression`) | `#32` | `#33` | 4/4 항목 수정: (1) `ContinuousLinearMap` 13-인자 오프바이원(`args[9]→args[8]`) 수정 + `check_notation_instance_leaks()` 가드 도입(`0/82` 누수), (2) 팬텀 암묵 바인더 전이적 추론 가능성 고정점 보존(`phantom_named_preserved=116`, `KwF` 36/36·`hcompl`/`loc` 3/3·`IsSplit` 1/1), (3) `golfed_RingObjectsOfMatrixData.lean:357` `mkRingInst` defeq 버그를 `rw [hρk, hρk, hsm, mul_smul]`으로 교정(`v4.34.1 exit 0`), (4) `Subalgebra.adjoin → Algebra.adjoin` 및 `UnifiedSWeqOm.lean` (`251L`/`187L`)·`tactic_golf_report.md` 지표 동기화 | **재검증 100% PASS (7/7 하네스 `exit 0`) → 통과** |

---

## 6. 확인한 것

`verify_round2.py`, 시그니처 덤프, 섀도우 diff, Lean v4.34.1 재컴파일을 이 노트들에 돌렸다. 증명 노트와 압축 노트는 한 번 고친 뒤 다시 확인했다.

- 감사 (`meta_audit_verdict.md`): 통과
- 증명 노트 (`rosetta_stone.md`, `rh_proof_explained.md`): 통과
- 압축 (`capelli_batch_report.md`, `unitary_dedup_plan.md`, `tactic_golf_report.md`): 통과
