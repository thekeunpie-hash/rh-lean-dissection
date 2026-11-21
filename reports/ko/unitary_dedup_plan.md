# Track C — Task 2: `UnitaryGroupMassFormula` 3중 디렉토리 클론 통합 설계 블루프린트

> **프로파일러 스크립트**: [profile_unitary_clones.py](../scripts/profile_unitary_clones.py) → 원시 데이터 [unitary_clone_profile.json](../out/unitary_clone_profile.json)  
> **대표 3중 트립릿 통합 PoC (Mathlib 드롭인)**: [UnifiedSWeqOm.lean](../poc/UnifiedSWeqOm.lean) (`SWeqOm.lean` × 3 → 단일 매개변수화 모듈)  
> **순수 Lean 4.34.1 코어 검증 하네스**: [verify_unitary_unified_core.lean](../harnesses/verify_unitary_unified_core.lean) (**`exit 0`, 오류 0, 경고 0, `sorry` 0, `axiom` 0**)

---

## 1. 대상 3개 디렉토리 전수 정량 현황

`lean_index.duckdb` 조회 결과 `Formalism.PeriodIntegrals.UnitaryGroupMassFormula.*` 하위 3개 디렉토리는 총 **448개 모듈 / 57,658라인 / 2,812,506바이트** 규모이며, 그중 **143개 파일명이 3개 디렉토리 전부에 공통 출현(트립릿)** 한다.

| 디렉토리 (`Formalism.PeriodIntegrals.UnitaryGroupMassFormula.*`) | 주 네임스페이스 | 전체 모듈 수 | 전체 라인 수 | 바이트 수 | 3중 공유(트립릿) | 2중 공유(페어) | 고유 파일 | 외부 임포트 간선 수 |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **1. `StabilizerOrbitVolume`** | `PI.VolStabSW` (129모듈) | 147 | 19,387L | 944,694B | 143 (18,799L) | 1 (`HformSmulRight`) | 3 (`FibInfEx`, `LocDensHG`, `TopoAFTop`) | — |
| **2. `StabilizerVolume`** | `PI.VolStabS` (133모듈) | 155 | 19,855L | 969,952B | 143 (18,766L) | 2 (`HformSmulRight`, `AdmCpt`) | 10 (`VolStabFromSWS`, `SiegelWeilNarrowOfWide`, `InVolumesAtOfSWS`, `ExStabNu` 등) | — |
| **3. `WeilStabilizerVolume`** | `PI.VolStabW` (129모듈) | 146 | 18,416L | 897,860B | 143 (18,028L) | 1 (`AdmCpt`) | 2 (`VolStabFromSWW`, `HformSmulLeft`) | 31 간선 |
| **합계** | 3개 평행 네임스페이스 | **448** | **57,658L** | **2,812,506B** | **429파일 (55,593L)** | **4파일** | **15파일 (2,065L)** | 외부 소비 분산 |

---

## 2. 143개 트립릿 전수 유사도 분포 및 쌍별(Pairwise) 복제 구조

단순 3자 최소 유사도(`norm_min`)만 보면 40개 트립릿이 `divergent (<50%)`로 보이지만, **3개 쌍 `(Orbit–Stab, Orbit–Weil, Stab–Weil)`을 분해**하고 DuckDB 선언명 집합을 교차 대조한 결과 훨씬 결정적인 구조가 드러났다:

### 2.1 정규화(디렉토리·네임스페이스 치환) 기준 3자 유사도 구간별 분포

| 구간 (3자 최소 정규화 유사도 `norm_min`) | 트립릿 수 | 3벌 합계 라인 | 1벌 통합 시 잉여 라인 (`sum - max`) | 대표 파일 예시 (`[Orbit / Stab / Weil]` 라인) |
| :--- | ---: | ---: | ---: | :--- |
| **`exact_100pct` (3벌 전원 100.0% 일치)** | **61** | 16,024L | **10,682L** | `ExStabSt` [186/186/186], `FinTheta`, `Unimod`, `Witt` 등 |
| **`near_identical_95_99` (95% ~ 99.9%)** | **11** | 6,220L | **4,130L** | `SdDual` [510/510/498], `SdTestInf` [344/344/344], `LocDensCnt` [342/354/342], `ExistsUnifFv` [219/214/214], `DensAAOf` [90/90/90] |
| **`high_similar_80_95` (80% ~ 95%)** | **14** | 4,892L | **3,201L** | `LocDensVolS` [345/363/331], `PosNear` [247/267/247], `DensInfCo` [189/180/180], `TopoNuFin` [164/174/164], `UnifVSpec` [137/137/137], `SWeqOm` [71/74/71], `VolStabFromSWOf` [47/47/47] |
| **`moderate_50_80` (50% ~ 80%)** | **17** | 9,914L | **6,453L** | `SdUniq` [404/429/393], `TensTop` [244/246/255], `DensVNA` [175/145/141], `ESSymmApply` [166/175/164] |
| **`divergent_lt50` (< 50%)** | **40** | 18,543L | **11,624L** | `LocDensHF` [401/408/408], `LocDensHH` [396/379/396], `DensGen` [286/263/256], `LocDensCntQ` [125/147/125] |
| **합계** | **143** | **55,593L** | **36,090L** | — |

### 2.2 쌍별 100% 일치 및 선언명 집합 교차 검증 (핵심 구조 발견)

| 쌍별 / 선언 일치 분류 | 트립릿 수 | 비중 (143 대비) | 구조적 원인 |
| :--- | ---: | ---: | :--- |
| **3벌 모두 100.0% 정규화 일치** (`all3 == 1.0`) | **61** | **42.7%** | 3개 매개변수 축과 무관한 순수 공통 보조정리 (완전 원문 일치도 58/143) |
| **3벌 중 2벌이 100.0% 일치** (`2-of-3 == 1.0`) | **54** | **37.8%** | 아래 3개 축 분기에 따른 정확한 2:1 클러스터링: |
| ├─ `Orbit == Weil == 1.0` (`Stab`만 상이) | 32 | 22.4% | `Orbit`·`Weil`은 비매끄러움 `IsAdm` 공유, `Stab`만 `IsAdmS` (`IsSmoothCc`) 사용 |
| ├─ `Stab == Weil == 1.0` (`Orbit`만 상이) | 18 | 12.6% | `Stab`·`Weil`은 차원 조건 `2 * a < M` 공유, `Orbit`만 `a + 2 ≤ M` 사용 |
| └─ `Orbit == Stab == 1.0` (`Weil`만 상이) | 4 | 2.8% | `Weil` 고유 `SWc1W` 의존 경로 (`SdDual`, `DensVSt` 등) |
| **3벌 모두 ≥ 90% 유사 (미세 diff)** | **7** | **4.9%** | `InCtx` 시그니처 2줄 차이(`DensAAOf`, `UnifVSpec`, `VolStabFromSWOf`, `ExChar` 등) |
| **2벌 ≥ 90% 유사** | **2** | **1.4%** | 부분 리팩토링 차이 |
| **3벌 모두 < 90% (독립 택틱 생성)** | **19** | **13.3%** | 단, `DensGen`·`LocDensHH`·`LocDensCntQ` 실 diff 확인 결과 **동일한 수학적 정리 시그니처를 서로 다른 택틱 스타일(`have h` vs `have h0`, `calc` vs `unfold`)로 독립 재증명**한 경우가 다수 |
| **선언명 집합 3자 100% 동일 (DuckDB 교차 확인)** | **115 / 143** | **80.4%** | 나머지 28/143도 부분 교집합 보유 — 사실상 전체 디렉토리 구조가 동일 DAG의 3벌 복제본 |

---

## 3. 3개 디렉토리를 가르는 정확한 수학적·타입 매개변수 축 (Diff 실증)

대표 컨텍스트 파일(`StabilizerOrbitVolume/FibInfEx.lean`, `StabilizerVolume/VolStabFromSWS.lean`, `WeilStabilizerVolume/VolStabFromSWW.lean`) 및 `SWeqOm.lean`, `PosTest.lean`, `ExChar.lean`, `DensAAOf.lean`, `UnifVSpec.lean`, `VolStabFromSWOf.lean`을 직접 대조한 결과, **3개 디렉토리를 구분하는 차이는 정확히 3개의 직교 축(Orthogonal Parameter Axes)** 으로 귀결된다:

| 매개변수 축 (`VolStabCfg` 필드) | 1. `StabilizerOrbitVolume` (`PI.VolStabSW`) | 2. `StabilizerVolume` (`PI.VolStabS`) | 3. `WeilStabilizerVolume` (`PI.VolStabW`) | 소스 Diff 근거 |
| :--- | :--- | :--- | :--- | :--- |
| **축 1: 차원 안정 조건 (`dimBound a M`)** | `a + 2 ≤ M` | **`2 * a < M`** | **`2 * a < M`** | `FibInfEx.lean:16` vs `VolStabFromSWS.lean:19` vs `VolStabFromSWW.lean:47`; `ExChar.lean:15` (`0 + 2 ≤ M` vs `2 * 0 < M`); `DensAAOf.lean:81` (`ha2` vs `by omega`, 왜냐하면 `1 ≤ a → 2*a < M → a + 2 ≤ M`) |
| **축 2: 아르키메데스 시험함수 정칙성 (`archExtra Φinf`)** | `True` (`IsAdm`: `Continuous ∧ HasCompactSupport`) | **`IsSmoothCc F E Φinf`** (`IsAdmS`: `IsAdm ∧ IsSmoothCc`, 망각 사상 `IsAdmS.adm`) | `True` (`IsAdm`: `Continuous ∧ HasCompactSupport`) | `VolStabFromSWS.lean:39-50`, `SWeqOm.lean:47-49` (`hsm` 추가), `PosTest.lean:36` (`hadm.adm`), `ExChar.lean:27` (`isSmoothCc_empty`), `VolStabFromSWOf.lean:32` |
| **축 3: Siegel–Weil 해석적 입력 가설 (`swInput F E σ M J`)** | **`SWc1 F E σ M J`** (`a + 2 ≤ M` 범위 Siegel–Weil) | **`StabilizerFirstChernCompatibility F E σ M J`** (`2 * a < M`, `IsSmoothCc` 제한 Siegel–Weil, `SiegelWeilNarrowOfWide` 경유) | **`SWc1W F E σ M J`** (`2 * a < M`, `RapidDecay` Siegel–Weil) | `FibInfEx.lean:16`, `VolStabFromSWS.lean:19`, `VolStabFromSWW.lean:16-38, 47`; 세 가설 모두 동일한 아델 세타 평균 오일러 곱 등식으로 귀결(`sw_eval`) |

### 단조 계층 관계 (핵심 수학적 통찰)
- `1 ≤ a`일 때 **`2 * a < M → a + 2 ≤ M`** 이 항상 성립한다(`omega`로 1줄 증명; `a = 1`일 때 `3 ≤ M`으로 동치, `a ≥ 2`일 때 `2a + 1 ≥ a + 2`).
- 따라서 **`SWc1 → SWc1W → StabilizerFirstChernCompatibility`** 순서로 가정이 점진적으로 약화되며(즉 결론의 적용 범위가 넓어지거나 입력 요구조건이 좁아짐), 3개 디렉토리는 **동일한 아델 궤도 적분·국소 밀도·Siegel–Weil 분해 증명 파이프라인**을 이 3가지 설정(`cfgOrbit`, `cfgStab`, `cfgWeil`)에 대해 통째로 3번 복붙한 구조다.

---

## 4. 단일 매개변수화 통합 설계 및 절감 규모 정량 추정

### 4.1 제안 모듈 아키텍처 (`Formalism.PeriodIntegrals.UnitaryGroupMassFormula.Common.*`)
1. **`Common.Config`** (~140L, 1회 정의): `structure VolStabCfg`, `InCtx cfg`, `IsAdmCfg cfg`, `IsAdmCfg.toBase`, `DensFibInf cfg`, `DensFibV cfg`, `SWeqOm cfg`, `Unfold cfg`, `PosTest cfg` 및 3개 구체 인스턴스 `cfgOrbit`, `cfgStab`, `cfgWeil` 정의.
2. **`Common.PureShared.*`** (61개 `exact_100pct` 트립릿): 매개변수 없이 1회만 정의(`ExStabSt`, `FinTheta`, `Unimod`, `Witt`, `TopoGram`, `RestrProdG` 등) → 3개 디렉토리에서는 얇은 `abbrev`/re-export 또는 직접 임포트 치환.
3. **`Common.ParamPipeline.*`** (54개 `2-of-3 == 1.0` + 28개 변형 트립릿): `(cfg : VolStabCfg)`를 받는 단일 정리로 통합(`sWeqOm_of cfg`, `posTest_of cfg`, `exChar_holds cfg`, `volStabFromSW_of cfg`, `densAAOf cfg`, `unifVSpec cfg` 등). `DensGen`·`LocDensHH`·`LocDensCntQ`처럼 동일 정리를 다른 택틱으로 증명한 19개 트립릿은 가장 짧고 깔끔한 1개 증명을 채택.
4. **호환성 얇은 파사드 (3개 디렉토리 진입점)**: 외부 31+ 임포터(`NcXBoxSteps`, `NcXLocSB`, `DecoratedLatticeProofs.*` 등)가 깨지지 않도록 각 디렉토리 루트/진입 파일(`Assembly`, `VolStabFromSWS`, `VolStabFromSWW`)에서 `abbrev`로 기존 심볼 재노출.

### 4.2 정적 라인 절감 정량 추정 (3단계 시나리오, 전체 57,658L / 트립릿 55,593L 기준)

| 통합 시나리오 | 대상 범위 | 정적 예상 절감 라인 | 3개 디렉토리(57,658L) 대비 | 비고 |
| :--- | :--- | ---: | ---: | :--- |
| **보수적 하한 (100% 기계 일치만 제거)** | 3자 100% 일치 61트립릿(2벌 제거: 10,682L) + 2자 100% 일치 54트립릿(1벌 제거: 8,386L) | **-19,068L** | **-33.1%** | 코드 로직 변경 0%, 순수 중복 복사본만 제거 |
| **권장 매개변수 통합 (`VolStabCfg`, 유사도 ≥ 80%)** | 61 + 54 + 고/근사유사 트립릿 단일화 (어댑터 오버헤드 10~15L/파일 차감 반영) | **-30,224L** | **-52.4%** | `VolStabCfg` 3축 통합 + 얇은 1줄 인스턴스화 |
| **완전 통합 상한 (143트립릿 전수 단일화)** | 동일 선언명 집합(115/143) 및 택틱 스타일만 다른 19개 트립릿까지 최단 증명 1벌로 통합 | **-36,090L** *(어댑터 ~500L 제외 시 ~35,500L)* | **-62.6%** *(실효 ~61.6%)* | 15개 디렉토리 고유 파일(2,065L)은 그대로 보존 |

---

## 5. 대표 트립릿 통합 PoC 결과 (`SWeqOm.lean` × 3 → 1개 통합 모듈)

### 5.1 정적 리팩토링 수치 ([UnifiedSWeqOm.lean](../poc/UnifiedSWeqOm.lean))
- **선택 트립릿**: `SWeqOm.lean` — 3개 축(`dimBound`, `archExtra`/`IsSmoothCc`, `swInput`/`SWc1`·`StabilizerFirstChernCompatibility`·`SWc1W`)을 **모두 동시에 사용하는** 가장 대표적인 트립릿.
  - 원본 3파일: `StabilizerOrbitVolume/SWeqOm.lean` (71L) + `StabilizerVolume/SWeqOm.lean` (74L) + `WeilStabilizerVolume/SWeqOm.lean` (71L) = **216L** (그중 `Decay` 33L × 3 = 99L은 완전 동일 복붙).
  - 통합 `SWeqOm` 본체 (`Decay` + 통합 `sWeqOm_of` + 인스턴스화 래퍼): **73L** (**-143L, -66.2%**).
  - 자기완결 PoC 파일 전체(`UnifiedSWeqOm.lean`, 143개 트립릿 전체에 1회만 정의되는 `VolStabCfg`·`InCtx`·`IsAdmCfg`·`DensFib*`·`SWeqOm`·3개 `cfg*` 포함): **251L (코드 187L)** — 3개 `SWeqOm.lean`(216L) + 3개 컨텍스트 파일(`FibInfEx` 123L + `VolStabFromSWS` 148L + `VolStabFromSWW` 163L = 434L) 합계 **650L → 251L (-399L, -61.4%)** 절감.
  - 코드 내 `sorry` 0건, `axiom` 0건, `admit` 0건.

### 5.2 Lean 4.34.1 단독 코어 하네스 컴파일 검증 완료치
- **파일**: [verify_unitary_unified_core.lean](../harnesses/verify_unitary_unified_core.lean) (221L, Mathlib 임포트 0)
- **명령**: `elan run leanprover/lean4:v4.34.1 lean ../harnesses/verify_unitary_unified_core.lean`
- **결과**: **`exit code 0` (오류 0, 경고 0, `sorry` 0, `axiom` 0)**
- **기계적 검증 항목**:
  1. `two_mul_lt_implies_add_two_le : 1 ≤ a → 2 * a < M → a + 2 ≤ M` (`omega`)
  2. `IsAdmCfg.toBase` (모든 설정에서 `IsAdmS.adm` 일반화)
  3. 단일 통합 정리 `sWeqOm_of (cfg : VolStabCfg C)` 증명 및 3개 디렉토리 구체 인스턴스(`PI_VolStabSW_sWeqOm_of`, `PI_VolStabS_sWeqOm_of`, `PI_VolStabW_sWeqOm_of`) 복원
  4. 단조 계층 정리 `swc1_implies_swc1W` 및 `swc1W_implies_swFirstChern` 형식 증명
