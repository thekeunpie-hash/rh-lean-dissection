# `ring_objects_of_matrix_data` 증명을 줄인 기록

- **원본 대상**: [RingObjectsOfMatrixData.lean](../lean/src/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/RingObjectsOfMatrixData.lean) (`Formalism.RepresentationBoundsCohomology.ringDataObjects.ring_objects_of_matrix_data`, L109–588, `set_option maxHeartbeats 8000000`)
- **Round 1 스텁 입력**: [stub_RingObjectsOfMatrixData.lean](../out/poc_golfing/stub_RingObjectsOfMatrixData.lean)
- **리팩토링 Mathlib 드롭인 산출물**: [golfed_RingObjectsOfMatrixData.lean](../poc/golfed_RingObjectsOfMatrixData.lean)
- **순수 Lean 4.34.1 코어 검증 하네스**: [verify_RingObjectsOfMatrixData_core.lean](../harnesses/verify_RingObjectsOfMatrixData_core.lean)

---

## 1. 전후 정량 비교 (정적 리팩토링 절감치 vs 코어 하네스 컴파일 검증치 엄격 분리)

### 1.1 정적 리팩토링 수치 (`RingObjectsOfMatrixData.lean` → `golfed_RingObjectsOfMatrixData.lean`)

| 측정 지표 | 원본 (`RingObjectsOfMatrixData.lean`) | 리팩토링 (`golfed_RingObjectsOfMatrixData.lean`) | 증감 | 변화율 |
| :--- | ---: | ---: | ---: | ---: |
| **목표 정리 시그니처 일치 여부** | `theorem ring_objects_of_matrix_data (hEM : StatEMat) (hSP : StatSplitPts) (hKO : StatIdemKO) : RingObjectsExist := by` | **완전 일치 (문자 단위 100% 동일)** | — | **100% 보존** |
| **공개 보조정리 시그니처 보존** | `rank_block`, `eDiag'` | **완전 일치 (문자 단위 100% 동일)** | — | **100% 보존** |
| **`ring_objects_of_matrix_data` 본문 줄 수 (코드 본문)** | **477L** (`L110–586`; 스팬 `L109–586` 478L, `set_option` 포함 479L / 코드 본문 **473L**) | **220L** (`L377–596`; 스팬 `L376–596` 221L, `set_option` 포함 222L / 코드 본문 **208L**) | **-257L (코드 -265L)** | **-53.9% (코드 -56.0%)** |
| **목표 정리 내 `have`/`haveI` 수 (선두 / 전체 토큰)** | **92회** (전체 토큰 **98회**) | **51회** (전체 토큰 **53회**) | **-41회** (토큰 **-45회**) | **-44.6%** (토큰 **-45.9%**) |
| **목표 정리 내 `let`/`letI` 수** | **35회** | **30회** | **-5회** | **-14.3%** |
| **목표 정리 내 `by_cases` 분기 수** | **17회** | **5회** | **-12회** | **-70.6%** |
| **파일 전체 코드 라인 (주석·공백 제외)** | **576L** (총 588L) | **549L** (총 598L, 16개 격리 헬퍼 시그니처 + 주석 포함) | **코드 -27L** (총 +10L) | **코드 -4.7%** |
| ├─ `rank_block` | 38L (L11–48) | 28L (L20–47) | -10L | -26.3% |
| ├─ `eDiag'` | 57L (L50–106) | 34L (L49–82) | -23L | -40.4% |
| └─ 추출된 `private` 격리 헬퍼 | 0개 | **16개** (각 3~41L, 독립 소형 문맥) | +16 모듈화 | 문맥 격리 |
| **`set_option maxHeartbeats`** | `8000000` (기본 200K의 40배) | `2000000` *(보수적 상한 설정; Mathlib 풀빌드 실측 대기)* | **-75% 상한 축소 목표** | 문맥 격리 해소 |
| **코드 내 `sorry` / `admit` / `axiom`** | **0건** | **0건** | 0 | **무결성 100% 유지** |

> [!NOTE]
> 파일 전체 줄 수(588L → 598L, 순 코드 576L → 549L)가 소폭만 줄어든 이유는, 거대 단일 택틱 본문(477L)을 16개의 `private` 최상위 선언으로 분리할 때 각 선언마다 독립적인 타입클래스·변수 시그니처 헤더가 명시되기 때문이다. 반면 Lean 4 커널/엘라보레이터의 `maxHeartbeats`를 결정짓는 핵심 지표인 **단일 택틱 상태의 본문 길이(-53.9%, 코드 -56.0%), 동시 `have` 수(선두 -44.6%, 토큰 -45.9%), `by_cases` 분기 수(-70.6%)** 가 대폭 축소되었다.
>
> **v2 수정 내역 (검수 메모 #32 반영)**: `mkRingInst` L357에서 추상 파라미터 `ρk`를 정의적 동치(`show ρπ ...`)로 가정하던 부분을 명제적 등식 치환 `rw [hρk, hρk, hsm, mul_smul]`으로 수정하고 Lean `v4.34.1`에서 해당 패턴의 커널 통과(`exit 0`)를 직접 확인했다. 또한 코어 하네스 및 본 보고서의 `Subalgebra.adjoin` 오기를 실제 임포트/원본 API인 `Algebra.adjoin`으로 교정했다.

### 1.2 Lean 4.34.1 단독 코어 하네스 컴파일 검증 완료치

- **검증 명령**:
  ```powershell
  elan run leanprover/lean4:v4.34.1 lean harnesses/verify_RingObjectsOfMatrixData_core.lean
  ```
- **실행 결과**: **`exit code 0` (오류 0, 경고 0, 코드 내 `sorry` 0, `axiom` 0, `admit` 0, Mathlib 임포트 0)**.
- **기계적 검증 완료 범위 (272줄 순수 Lean 4 코어 모델)**:
  1. `map_diagonal_ite`: `if P a then v a else 0` 대각행렬의 `RHom` 매핑(원본 L350–363 2중 중복 제거 패턴)
  2. `block_inj_of_ne_zero`: 기수 1 파이버 `Subsingleton` 기반 단사성(원본 L117–121, L489, L515 3중 중복 제거)
  3. `liftEvalHom`: 단사 `ι : O →+* K` 역상(`Classical.choose`)을 통한 행렬 대수 준동형 5대 공리 격리 구성(원본 L221–247)
  4. `restrictBlock_diag_entry`: `toSquareBlock` 대각 성분 보존(원본 L256–275)
  5. `listSum_ite_eq` & `blockRep_smul_of_diag`: 대각 행렬의 블록 표현 스칼라 작용(`a • m = w • m`, 원본 L378–387)
  6. `listProd_eq_zero_of_mem`, `mem_tail_range`, `valEval_eq_zero_of_zero`, `valEval_eq_delta_of_one`, `valEval_eq_zero_of_ge_two`: 특수 파이버 `E.1 π'` 대각 고유값 3분기(`bl a = 0`, `bl a = 1`, `bl a ≥ 2`) 완전 증명(원본 L367–377)
  7. `splitPts_fiber_unique_core` & `basis_lin_indep_pullback_core`: `RingDef` 최종 `refine` 내부 중첩 서브골 분리 패턴(원본 L537–566)

---

## 2. `maxHeartbeats 8000000` 폭증 원인 진단

원본 `RingObjectsOfMatrixData.lean:109–588`이 기본 한도(200,000)의 **40배(8,000,000)** 를 요구한 근본 원인은 4가지 구조적 병목이다:

1. **단일 엘라보레이션 문맥 폭증 (120+ 동시 바인딩)**: `intro` 26개 인자 + `obtain` 21개 가설 + `let`/`letI` 35개 + `have` 92개가 **하나의 `by` 블록**에 누적된다. 후반부(L440–587)에서 `simp`, `rw`, `ext`, 타입클래스 합성(`Algebra T' R'`, `Module T' (EvalSp ...)`, `IsScalarTower`, `SMulCommClass`)이 호출될 때마다 3개의 로컬 `letI` 인스턴스와 26개의 투명 `let` 정의(`K`, `ι`, `X0`, `P`, `X'`, `p`, `T'`, `rr`, `rK`, `R'`, `ρπ`, `ρk`, `E`, `δ`, `τ`, `D`)를 반복 탐색·전개하는 이차 비용이 발생한다.
2. **거대 22-필드(`RingDef`) + 21-필드(`RingTop`) 동시 `refine` 단일화 병목 (L530–587)**: 투명 `let D : RingData ... := { ... }` 직후 `refine ⟨D, ⟨...⟩, ⟨...⟩, i3, ?_⟩` 안에 4개의 인라인 서브골(L537–566)과 5개의 `RingTop` 서브골(L572–586)이 매달려 120개 로컬 바인딩을 끌고 다니며 의존 필드를 동시 단일화한다.
3. **문맥 독립적인 `AlgHom` 및 `RingInst` 구성의 인라인 매립 (L221–275, L440–468)**: `ρπ`(27L), `ρk`(20L), `finite_splitPts`(15L), `i1..i5`(29L), `hsurj`(27L), `hKO1`(12L)가 외부 가설과 수학적으로 독립임에도 거대 택틱 상태 내부에서 매번 `ext i j; simp`를 실행한다.
4. **기계적 코드 중복**:
   - 대각행렬 `.map ι` 증명(`ext i j; by_cases hij : i = j ...`) 2회 복붙 (L350–356 vs L357–363).
   - `Fintype.card_le_one_iff_subsingleton.mp (le_of_eq (hc1 ...))` 3회 복붙 (L119, L489, L515) 및 `Fintype.card_pos_iff.mp` 2회 복붙 (L410, L491).
   - `liftEvalAlgHom` 내부 `ext i j; apply hι; rw [hent]` 5회 반복 및 `restrictBlockAlgHom` 내부 `i.1 ≠ j.1` 분기 2회 반복.
   - `tSpan` 풀백(`hpull`, L153–158)과 정수성(`hint`, L159–164)의 동일 `Finset.sum_congr` 증명.

---

## 3. 추출 헬퍼 분해표 (16개 `private` 선언)

| # | 추출 선언명 | 대응 원본 구간 (줄 수) | 역할 및 격리 효과 |
| ---: | :--- | :--- | :--- |
| 1 | `map_diagonal_ite` | L350–363 (14L 중복) | `if P a then v a else 0` 대각행렬의 `RingHom.map` 단일화 → `hEπ` 19L → 4L 축약 |
| 2 | `block_subsingleton` | L119, L489, L515 (3중 반복) | 기수 1 비영 블록 파이버의 `Subsingleton` 변환 공통화 |
| 3 | `block_nonempty` | L410, L491 (2중 반복) | 기수 1 비영 블록 파이버의 `Nonempty` 변환 공통화 |
| 4 | `block_inj_of_ne_zero` | L117–121 (5L) | 비영 블록 단사성 보조정리 |
| 5 | `tSpan_pullback` | L153–158 (6L) | `tSpan T r₀ → tSpan T' rK` 풀백 보존 분리 |
| 6 | `tSpan_entries_integral` | L159–164 (6L) | `tSpan T' rK` 원소의 `O`-행렬 정수성 분리 |
| 7 | `blockPoly_diag_spec` | L186–216 (31L) | 특수 파이버 `blockPoly (eB π) (X0 π) = ∏ (X - C (γ i))` 계산 완전 격리 |
| 8 | `liftEvalAlgHom` | L221–247 (27L) | `Classical.choose` 기반 `ρπ : R' →ₐ[O] Matrix d d O` 5대 공리 증명을 외부 문맥과 완전 격리 |
| 9 | `restrictBlockAlgHom` | L256–275 (20L) | 블록 제한 `ρk k` 5대 공리 격리 (`RankDiagIte.lean:67–87`과도 공용화 가능) |
| 10 | `finite_splitPts` | L425–439 (15L) | `Finite (SplitPts t P)` 독립 증명 (`R'`·`E`·`ρπ` 무관) |
| 11 | `blockRep_smul_of_diag` | L378–387 (10L) | 대각 스칼라 작용(`a • m = w • m`) 범용 헬퍼 — `hEblk`, `he1blk`, `hu1` 공통 기반 |
| 12 | `blockAlgHom_surjective` | L471–497 (27L) | `k = 0` (`ontoSpan`) 및 `k ≠ 0` (`block_subsingleton`) 전사성 증명 격리 |
| 13 | `range_e1_equiv_KO` | L499–510 (12L) | `hKO` + `rank_block`을 통한 `range e₁' ≃ₗ[O] KO O` 존재성 격리 |
| 14 | `splitPts_fiber_unique` | L537–547 (11L) | `RingDef` 제2항(분할점 파이버 유일성)을 최종 `refine` 외부로 분리 |
| 15 | `mkRingInst` | L440–468 (29L) | `RingInst` 5개 인스턴스(`IsNoetherian`, `IsScalarTower`×3, `SMulCommClass`)를 전용 로컬 인스턴스 스코프에서 일괄 구성 |
| 16 | `basis_lin_indep_pullback` | L560–566 (7L) | `RingDef` 제21항(기저 선형독립성 풀백)을 최종 `refine` 외부로 분리 |

---

## 4. 검증 경계 및 `v4.33.1` 정식 검증 절차

- **정직한 검증 경계 명시**:
  - **로컬 검증 완료 (Lean `v4.34.1` exit 0)**: 7개 핵심 추출 헬퍼 패턴(`map_diagonal_ite`, `block_inj_of_ne_zero`, `liftEvalHom`, `restrictBlock_diag_entry`, `blockRep_smul_of_diag`, `valEval` 3분기, `splitPts_fiber_unique_core`, `basis_lin_indep_pullback_core`)을 순수 Lean 4 코어로 구현·증명한 `verify_RingObjectsOfMatrixData_core.lean` (272L)의 `exit 0` 컴파일, 그리고 `golfed_RingObjectsOfMatrixData.lean`의 공개 시그니처 100% 문자 일치 및 `sorry`/`axiom`/`admit` 0건 검증.
  - **Mathlib `v4.33.1` 의존 미검증 영역**: `Polynomial`, `FractionRing`, `IsFractionRing`, `IsDiscreteValuationRing`, `Algebra.adjoin`, `IsNoetherian`, `Matrix.rank`, `LinearMap.range`, `IsLocalRing.residue`, `eta_determinant_comparison`, `ontoSpan`, `noeth`, `rootsInt`, 그리고 실제 `maxHeartbeats` 감소율(8,000,000 → 실측치)은 `downloads/lean/.lake/`에 `v4.33.1` Mathlib `.olean` 캐시가 없으므로 로컬 측정이 불가하다.
- **`v4.33.1` 정식 검증 및 하트비트 실측 명령어**:
  ```powershell
  elan toolchain install leanprover/lean4:v4.33.1
  cd ../lean
  elan run leanprover/lean4:v4.33.1 lake exe cache get
  elan run leanprover/lean4:v4.33.1 lake build Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.FinrankRangeEq
  elan run leanprover/lean4:v4.33.1 lake env lean -Dprofiler=true `
    ../poc/golfed_RingObjectsOfMatrixData.lean
  ```
