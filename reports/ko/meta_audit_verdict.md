# Lean 4.33.1 RH/GRH 트리의 메타프로그래밍과 경계 조건

- **범위**: 메타프로그래밍, 특수 선언, RH/GRH 경계 조건
- **감사 대상**: `../lean/src/` (Lean `v4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, 총 175,187개 모듈)
- **기초 산출물 및 인덱스**:
  - `../out/lean_index.duckdb`
  - `../out/deep_audit.md`
  - `../out/deep_audit_results.json`
  - Lean 4 커널/엘라보레이터 내부 호출 사슬 대조 참조: 로컬 공식 `v4.34.1` 표준 라이브러리(`../lean-toolchain/src/lean/Lean/{AddDecl,Environment,LibrarySuggestions/Basic}.lean`)
- **원칙 준수 확인**: 원본 `downloads/lean/src/` 무변경, `lake build` 미실행, `src/` 전역 `rg`/`grep` 미실행, 모든 판단에 파일 경로·행 번호·원문 발췌 명시.

---

## 0. 결과

### **결과: `CLEAN` — 정적 사각지대 0건 (메타프로그래밍 · 특수 선언 · RH/GRH 경계조건 감사 통과)**

Round 1 스캐너(`deep_audit.py`)에서 0건 초과로 탐지된 **모든** 메타프로그래밍 및 비일상 선언·옵션을 100% 원문 행단위로 열람하고, `Main.lean` 5개 최종 정리의 해석적 수론 경계조건과 `SmallClassNumbers.CorGKOf` 격리 여부를 교차 검증한 결과, **Lean 4 신뢰 커널 타입체커를 우회하거나 숨겨진 공리를 주입하는 경로는 0건이며, RH/GRH 명제와 환원 증명에도 수학적 허점(vacuous loophole)이 0건**임을 확인하였다.

| 감사 영역 | 전체 건수 | 열람률 | 커널 우회 / 공리 주입 가능성 | `Main` / `MainTheorems` 원뿔 포함 여부 | 판정 |
| :--- | ---: | ---: | :--- | :--- | :--- |
| `CutCptCopy.lean` (`addDecl` 2건, `partial def` 1건, `elab` 1건) | 1모듈 (91줄) | **100%** | **불가** (`.defnDecl`/`.thmDecl`만 제출 → C++ `lean_add_decl` 검증; `debug.skipKernelTC` 0건) | 모듈 원뿔 포함 (`Main` 깊이 17, `MainTheorems` 깊이 14); **동적 생성 정리(`block_growth_bound_of_compact_coefCpt`)는 `FinalS.lean:61`에서 실제 소비** | **CLEAN** |
| `BuildAid/D1..D5.lean` (`run_cmd` / `modifyEnv` 각 5건) | 5모듈 (각 4줄) | **100%** | **불가** (`LibrarySuggestions.nameDenyListExt`에만 문자열 추가, 커널 상수 테이블 비접근) | 모듈 원뿔 포함 (깊이 5–18 from `MainTheorems`), 선언 0개, 증명항 기여 0건 | **CLEAN** |
| 전체 저장소 `elab` (3모듈) | 4건 | **100%** | **불가** (`cpt_copy_thms`·`kexactB`·`kcopy` 모두 최종 커널 검사 통과 필수; `#kcopy_probe`는 읽기 전용 미호출 진단 명령) | 모듈 원뿔 포함 (`Imports` 깊이 4, `OwnStruct` 깊이 6, `CutCptCopy` 깊이 14 from `MainTheorems`), 증명항 내 엘라보레이터 코드 미포함 | **CLEAN** |
| 전체 저장소 `partial def` (2모듈) | 2건 | **100%** | **불가** (컴파일타임 메타 함수 전용; Lean 4 `partial def` 자체도 커널 `opaque`로 건전) | 모듈 원뿔 포함, 커널 증명항 출현 **0건** | **CLEAN** |
| 전역 `macro` (19모듈) | 22건 | **100%** | **불가** (22건 전원 `: tactic =>` 전술 단축어, 섀도잉 0건) | 19/19 모듈 `MainTheorems` 원뿔 포함 | **CLEAN** |
| `allowUnsafeReducibility` | 37건 | **100%** | **불가** (37/37건 전부 `attribute [local irreducible]` 부여용, 엘라보레이터 투명도 옵션) | 모듈 원뿔 포함 (`DB_Rch` 37/37) | **CLEAN** |
| `hygiene` | 31건 | **100%** | **불가** (31/31건 전부 `set_option hygiene false in` + `local notation` 22 / `local macro` 8 / `scoped macro` 1) | 모듈 원뿔 포함 (`DB_Rch` 31/31) | **CLEAN** |
| 기타 비일상 `set_option` (`quotPrecheck` 7, `smartUnfolding` 3, `Elab.async` 1, `genSizeOf` 1, `warn.classDefReducibility` 1) | 13건 | **100%** | **불가** (전체 33종 88,139건 중 `debug.skipKernelTC`/`debug.proofAsSorry` **0건**) | 모듈 원뿔 포함 | **CLEAN** |
| RH/GRH 수학적 경계조건 (`Main` 등 8+개 파일) | 5개 최종 정리 | **100%** | — (`s=0`, `s=-2(n+1)`, `s=1`, `[NeZero N]`, `χ=1` vs `χ≠1`, 비원시 오일러 인자, `Re(s)=0,1` 전원 엄밀 검증) | `Main.lean` 5개 정리 일치 | **CLEAN** |
| `MainTheoremsAll` → `SmallClassNumbers.CorGKOf` 격리 | 4개 부가 모듈 | **100%** | — (`MainTheorems` 원뿔에서 4개 모듈 0건 임포트, 완전 격리) | `Main`에만 포함, **`MainTheorems` 원뿔 외** | **CLEAN** |

> **감사 범위 경계**: 본 보고서는 로컬에 `leanprover/lean4:v4.33.1` 툴체인과 `.lake/` 빌드 캐시가 부재한 환경에서 수행된 **100% 정적·원문 행단위·커널 구조 감사**이다. 실제 바이너리 레벨의 형식 인증을 위해서는 추후 `v4.33.1` 환경에서 `lake build Main` 및 5개 최종 정리 대상 `#print axioms` 실행이 필요하다.

---

## 제1부. 메타프로그래밍 및 특수 선언 행단위 감사

### 1.1 `CutCptCopy.lean` 감사 (`addDecl` 2건 · `partial def` 1건 · `elab` 1건)

- **대상 파일**:
  - 본체(전문 91줄): `../lean/src/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean`
  - 유일 호출부: `../lean/src/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutMainCpt.lean` (`L1-2`, `L944-945`)
  - 하위 소비부: `../lean/src/Formalism/HermitianCurvature/HermitianCurvatureProofs/CptCopy2.lean` (`L1-159`), `../lean/src/CompanionTheory/AutomorphicTheory/CompactTopologicalForms/FinalS.lean` (`L1-200`)

#### (a) 행단위 동작 분석 및 핵심 원문 발췌

`CutCptCopy.lean`은 이미 증명된 `Formalism.FourierDecayAlt.*` 계열 정리들의 의존 DAG를 순회하여, 3개의 기반 정리(`pb_formPos`, `list_duality_level_group`, `vector_isomorphism_levels`)를 콤팩트 지지(compact support) 버전 정리로 치환한 복제 정리(`...Cpt` 접미사)를 자동 등록하는 명령 엘라보레이터 `cpt_copy_thms`를 정의한다.

1. **임포트 (`L1-10`)**: 기존 정리 원천 모듈 6개(`CutLimENFMain`, `CutGermDone`, `CutNFTopFormDone`, `CutNFIdPairPtw`, `CutNFIdPolAll`, `CutNFTopPtw`)와 콤팩트 지지 대체 정리 모듈 4개(`ModuleFormPosCompactSupport`, `VectorIsomorphismCompactSupport`, `SizeStandardCompact`, `ExistsNormBoundThreeFamilies`)를 임포트한다.
2. **치환 사양 (`L16-36`)**:
   - `special` (`L16-19`): 3개 기반 정리를 콤팩트 지지 버전으로 1:1 매핑:
     ```lean
     def special : List (Name × Name) :=
       [(`Formalism.FourierDecayAlt.P.pb_formPos, `Formalism.FourierDecayAlt.P.module_form_pos_compact_support),
        (`Formalism.FourierDecayAlt.P.list_duality_level_group, `Formalism.FourierDecayAlt.P.size_standard_compact),
        (`Formalism.FourierDecayAlt.P.vector_isomorphism_levels, `Formalism.FourierDecayAlt.P.vector_isomorphism_compact_support)]
     ```
   - `manual` (`L21-26`): 수동으로 `...Cpt` 버전이 작성된 14개 경계 선언 목록(`ThmPActual`, `SizeStd`, `VIso`, `FormPos`, `standard_pairing_of_heads`, `FormNonneg`, `form_re_nonneg`, `form_cs`, `formNonneg_of`, `posAt_of_cpt`, `integral_three_at_place_of_parts`, `integral_four_at_place_of_parts`, `truncated_limit_positivity_holds`, `glGram`; 이들은 `CutMainCpt.lean:1`이 임포트하는 `CutCptManual.lean` 등에 대응).
   - `roots` (`L28-30`): 복제 탐색의 최상위 루트 6개:
     ```lean
     def roots : List Name :=
       [`Formalism.FourierDecayAlt.P.CutBP.thmBpAt_main4, `Formalism.FourierDecayAlt.P.CutBP.germ_truncation_positive, `Formalism.FourierDecayAlt.P.CutBP.block_growth_bound_of_compact_coef,
        `Formalism.FourierDecayAlt.P.CutBP.nFTopFormAll_of_ptw, `Formalism.FourierDecayAlt.P.CutBP.top_identity_of_domination_limits, `Formalism.FourierDecayAlt.P.CutBP.nfPolFormAll_of_top]
     ```
   - `terminal` (`L32`): `manual.contains n || (special.lookup n).isSome` — 탐색 중단 경계 판정.
   - `suffixed` (`L34-36`): 선언 이름 끝에 `"Cpt"` 접미사 부착.
3. **상수 수집 및 후위 위상정렬 DFS (`L38-56`)**:
   ```lean
   def proposals (ci : ConstantInfo) : Array Name :=
     ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])

   partial def go (env : Environment) (n : Name) (st : NameSet × NameSet × Array Name) : NameSet × NameSet × Array Name :=
     let (seen, tainted, order) := st
     if seen.contains n || terminal n then st else
     let seen := seen.insert n
     match env.find? n with
     | none => (seen, tainted, order)
     | some ci =>
       let us := proposals ci
       let (seen, tainted, order) :=
         us.foldl (fun s c => if (`Formalism).isPrefixOf c then go env c s else s) (seen, tainted, order)
       if us.any (fun c => terminal c || tainted.contains c) then (seen, tainted.insert n, order.push n)
       else (seen, tainted, order)

   def toCopy (env : Environment) : NameSet × Array Name :=
     let (_, tainted, order) := roots.foldl (fun s r => go env r s) ({}, {}, #[])
     (tainted, order)
   ```
   - `proposals` (`L38-39`)의 `allowOpaque := true`는 **읽기 전용** 의존 상수 수집에만 사용되며, 실제 환경 등록(`L76-84`)에서 `.opaqueInfo`는 명시적으로 거부된다.
   - `go` (`L41-52`)는 `Formalism` 접두사 하위 상수만 재귀 방문하며, `terminal`에 직·간접 의존하는 상수들만 `tainted` 집합과 위상정렬 배열 `order`에 축적한다.
4. **식 치환 및 선언 등록 (`L58-89`)**:
   ```lean
   def mapName (tainted : NameSet) (n : Name) : Name :=
     match special.lookup n with
     | some m => m
     | none => if manual.contains n || tainted.contains n then suffixed n else n

   def subst (tainted : NameSet) (e : Expr) : Expr :=
     e.replace fun
       | .const n ls => some (.const (mapName tainted n) ls)
       | _ => none

   def copyAll (defsOnly : Bool) : CoreM Nat := do
     let (tainted, order) := toCopy (← getEnv)
     let mut k := 0
     for n in order do
       let env ← getEnv
       let n' := mapName tainted n
       if env.contains n' then continue
       let some ci := env.find? n | throwError "missing {n}"
       match ci with
       | .defnInfo d =>
         addDecl (.defnDecl { d with name := n', type := subst tainted d.type, value := subst tainted d.value })
         k := k + 1
       | .thmInfo t =>
         if defsOnly then continue
         addDecl (.thmDecl { t with name := n', type := subst tainted t.type, value := subst tainted t.value })
         k := k + 1
       | _ => throwError "cannot copy {n}"
     return k

   elab "cpt_copy_thms" : command => do
     let k ← liftCoreM (copyAll false)
     logInfo m!"copied {k} declarations"
   ```
   - **유일 호출부 (`CutMainCpt.lean:944-945`)**:
     ```lean
     set_option maxHeartbeats 0 in
     cpt_copy_thms
     ```
   - **실제 생성·소비 실증 확인**: DuckDB `decls` 대조 결과, 6개 `roots` 중 `thmBpAt_main4Cpt`는 `CutMainCpt.lean:475`에 이미 정적 선언되어 있어 `L74` (`if env.contains n' then continue`)로 건너뛴다. 반면 나머지 5개 루트 대응 정리(`germ_truncation_positiveCpt`, `block_growth_bound_of_compact_coefCpt`, `nFTopFormAll_of_ptwCpt`, `top_identity_of_domination_limitsCpt`, `nfPolFormAll_of_topCpt`)는 정적 소스에 존재하지 않고 **`CutMainCpt.lean:945`의 `cpt_copy_thms`가 동적 생성**한다. 그리고 `FinalS.lean:61`이 실제로 `block_growth_bound_of_compact_coefCpt`를 직접 호출한다:
     ```lean
     -- CompanionTheory/AutomorphicTheory/CompactTopologicalForms/FinalS.lean:60-61
     ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn (apx (D.cutF p.T.base χ F ε) n) Y K N := fun _ hε n =>
       block_growth_bound_of_compact_coefCpt hA p nn _ Y K N Cb hCb (cptCoef_apx P p.T.base hχ hF hε n) hnn
     ```

#### (b) Lean 4 커널/엘라보레이터 우회 불가 기술 근거

1. **신뢰 C++ 커널 타입체커 강제 경유**: `CutCptCopy.lean:78,82`가 호출하는 `Lean.addDecl`은 엘라보레이터 편법이 아니라 Lean 4의 모든 `def`/`theorem`이 사용하는 정규 등록 API이다. Lean 4 표준 라이브러리 소스(`Lean/AddDecl.lean`, `Lean/Environment.lean`) 기준 정확한 호출 사슬은 다음과 같다:
   - `Lean.addDecl` (`AddDecl.lean:229-230`) → `addDeclCore` (`AddDecl.lean:101-194`)
   - `doAdd` 내부에서 `(← getEnv).addDeclAux (← getOptions) decl ...` 호출 (`AddDecl.lean:188`)
   - `Environment.addDeclAux` (`AddDecl.lean:30-33`) → `env.addDeclCore ... (!debug.skipKernelTC.get opts)`
   - `Environment.addDeclCore` (`Environment.lean:701-711`): `doCheck = true`일 때 `addDeclCheck` → `Kernel.Environment.addDeclCore` (`@[extern "lean_add_decl"]`, `Environment.lean:296-298`), 즉 **C++ 신뢰 커널 타입체커**를 호출한다.
   - 참고로 `addDeclCore`의 `catch ex => addAsAxiom; throw ex` (`AddDecl.lean:191-194`)는 커널 검증 실패 시 IDE 후속 오류 폭주 방지용 임시 등록 직후 예외 `ex`를 **즉시 재발생(rethrow)**하므로 커널 검사를 통과하지 못한 선언은 컴파일 오류로 실패한다.
2. **커널 검사 우회 경로 전면 차단 확인**:
   - 커널 무검사 등록 API `addDeclWithoutChecking` (`Environment.lean:307-308`): 전체 175,187개 파일 **0건**.
   - 커널 검사 비활성화 옵션 `debug.skipKernelTC`: 전체 88,139건의 `set_option`(33종) 및 `lakefile.toml` **0건**.
   - `CutMainCpt.lean:944`의 `set_option maxHeartbeats 0 in`은 단일 명령 안에서 다수 정리를 연쇄 타입체킹할 때의 타임아웃 한도만 해제하며, `doCheck` 플래그나 커널 타입체킹 규칙에는 전혀 영향을 주지 않는다.
3. **공리/불투명 상수 주입 원천 차단**: `copyAll` (`L76-84`)은 오직 `.defnInfo` → `Declaration.defnDecl` (`L78`)과 `.thmInfo` → `Declaration.thmDecl` (`L82`)만 제출하며, `.axiomInfo`/`.opaqueInfo`/`.inductInfo`/`.quotInfo` 등 그 외 모든 케이스는 `L84` (`| _ => throwError "cannot copy {n}"`)로 오류 종료한다. 또한 `subst tainted`로 치환된 `type`과 `value` 사이에 단 하나의 타입 불일치나 우주(universe) 불일치가 있어도 C++ 커널 `lean_add_decl`이 즉시 `(kernel) declaration type mismatch`로 거부한다.

#### (c) 정확한 의존성 풋프린트

- **모듈 임포트 원뿔**: `Main` 도달(깊이 **17**), `Supplements.Kernels.MainTheorems` 도달(깊이 **14**).
  - `MainTheorems` 기준 최단 경로 (14홉):
    `Supplements.Kernels.MainTheorems` → `Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion` → `Development.AutomorphicArithmetic.CharacterBoxes.RiemannHypothesisOfEveryCharacter` → `Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowMainEqPOfSiegelWeil` → `CompanionTheory.AutomorphicTheory.UniformLocalFormulas.Closed` → `CompanionTheory.AutomorphicTheory.BesselWaveGrids.ThmBFinal` → `...WeightedBoundRotatedUniformOfHypsG` → `...WeightedBoundRotatedUniformOfCubicThreshold` → `...EndpointDifferentTypesThreshold` → `CompanionTheory.AutomorphicTheory.CompactTopologicalForms.NormalFormTopDomination` → `...FinalC` → `...FinalS` → `Formalism.HermitianCurvature.HermitianCurvatureProofs.CptCopy2` → `...CutMainCpt` → `...CutCptCopy`
- **커널 증명항 원뿔 구분**: `CutCptCopy`의 메타프로그래밍 함수(`go`, `copyAll`, `cpt_copy_thms`) 자체는 `Main` 5개 정리의 증명항에 전혀 등장하지 않는다. 반면 `cpt_copy_thms`가 `CutMainCpt.lean:945`에서 생성한 `block_growth_bound_of_compact_coefCpt` 등은 `FinalS.lean:61`을 거쳐 `Main` 5개 정리의 증명항 원뿔에 실제 포함되며, 모든 생성 정리는 개별적으로 C++ 커널 `lean_add_decl`의 정식 검증을 통과해야만 환경에 진입한다.

---

### 1.2 `BuildAid/D1.lean` – `BuildAid/D5.lean` 감사 (`run_cmd` / `modifyEnv` 각 5건)

DuckDB 조회 결과 `BuildAid` 디렉터리에는 정확히 `D1.lean`–`D5.lean` 5개 파일만 존재하며, 각 파일은 정확히 4줄, 선언 수(`decl_count`) 0개이다.

#### (a) 5개 파일 전문 원문 및 행단위 동작

- `../lean/src/BuildAid/D1.lean` (`L1-4`):
  ```lean
  import Lean.LibrarySuggestions.Basic
  import Lean.Elab.Command

  run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "CompanionTheory"
  ```
- `../lean/src/BuildAid/D2.lean` (`L1-4`):
  ```lean
  import Lean.LibrarySuggestions.Basic
  import Lean.Elab.Command

  run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "CrystallineSemistableComparison"
  ```
- `../lean/src/BuildAid/D3.lean` (`L1-4`):
  ```lean
  import Lean.LibrarySuggestions.Basic
  import Lean.Elab.Command

  run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "GlobalTheory"
  ```
- `../lean/src/BuildAid/D4.lean` (`L1-4`):
  ```lean
  import Lean.LibrarySuggestions.Basic
  import Lean.Elab.Command

  run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PositivityTheory"
  ```
- `../lean/src/BuildAid/D5.lean` (`L1-4`):
  ```lean
  import Lean.LibrarySuggestions.Basic
  import Lean.Elab.Command

  run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "UpperTheory"
  ```

이는 Lean 4 표준 라이브러리 `Lean/LibrarySuggestions/Basic.lean:311-320`의 **공식 문서 주석에 기재된 관용구와 문자 그대로 일치**한다:
```lean
/--
A premise whose name has one of the following components is not retrieved.

Use `run_cmd modifyEnv fun env => nameDenyListExt.addEntry env name` to add a name to the deny list.
-/
builtin_initialize nameDenyListExt : SimplePersistentEnvExtension String (List String) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.cons)
    addImportedFn := mkStateFromImportedEntries (·.cons) ["Lake", "Lean", "Internal", "Tactic"]
  }
```
즉, 대형 내부 네임스페이스 5개가 `Lean.LibrarySuggestions`(전제 추천기) 검색 후보로 대량 노출되어 개발·자동탐색을 저해하는 것을 막는 순수 개발 편의 필터 설정이다.

#### (b) Lean 4 커널/엘라보레이터 우회 불가 기술 근거

- `Lean.LibrarySuggestions.nameDenyListExt`는 타입이 `SimplePersistentEnvExtension String (List String)`인 엘라보레이터 보조 확장(environment extension)이며, `Lean/LibrarySuggestions/Basic.lean:342`의 `isDeniedPremise` 함수에서만 참조된다.
- `nameDenyListExt.addEntry env "..."`는 오직 해당 확장 슬롯의 `List String` 앞에 문자열 하나를 `cons`할 뿐, 커널의 `Kernel.Environment.constants` 맵, 공리 목록, 타입체커 옵션, 리듀서(WHNF/isDefEq) 어디에도 접근·수정하지 않는다.

#### (c) 정확한 의존성 풋프린트

5개 모두 `Main` 및 `Supplements.Kernels.MainTheorems` 모듈 임포트 원뿔에 포함되나, 선언 수 0개이므로 **커널 증명항에는 일절 기여하지 않는다**:

| 모듈 | 등록 문자열 | 직접 임포터 수 | `Main` 깊이 | `MainTheorems` 깊이 | `MainTheorems` 최단 진입 경로 (말단) |
| :--- | :--- | ---: | ---: | ---: | :--- |
| `BuildAid.D1` | `"CompanionTheory"` | 3 | 13 | 12 | `... → EmbeddingMiddleFactorTriple → MidExact → BuildAid.D1` |
| `BuildAid.D2` | `"CrystallineSemistableComparison"` | 4 | 12 | 11 | `... → HtOf → Half1 → H1LiftNaturality → BuildAid.D2` |
| `BuildAid.D3` | `"GlobalTheory"` | 25 | 8 | 5 | `MainTheorems → MainConclusion → RiemannHypothesisOfEveryCharacter → BkLawEntriesStatement → NonzeroPlacesOverPrimesLifts → BuildAid.D3` |
| `BuildAid.D4` | `"PositivityTheory"` | 5 | 8 | 6 | `MainTheorems → MainConclusion → EveryCharacterOfLiteratureOfVWin → LanglandsMultisegmentsOfSeg → EmbeddingMiddleFactorTriple → MidExact → BuildAid.D4` |
| `BuildAid.D5` | `"UpperTheory"` | 1 | 19 | 18 | `... → ThetaLiftOfZel → ImportsAlt → MNolow → MFront → BuildAid.D5` |

---

### 1.3 전체 저장소 `elab` 4건 감사 (3개 파일 전문 열람)

Round 1 스캔(`deep_audit_results.json`) 기준 전체 175,187개 파일의 `elab` / `elab_rules` 총합은 **정확히 4건(3개 모듈)**이다. (`elab_rules` 0건, `syntax` 0건.)

#### (1) `CutCptCopy.lean:87-89` — `elab "cpt_copy_thms" : command`
- 위 제1.1절에서 전문 감사 완료 (**CLEAN**).

#### (2) `Formalism/LocalToGlobal/IndefiniteReal/HeckeNonvanishing/Imports.lean:1-8` — `elab "kexactB " e:term : tactic`

- **(a) 전문 원문 및 행단위 동작**:
  ```lean
  import Lean

  open Lean Elab Tactic Meta

  elab "kexactB " e:term : tactic => withMainContext do
    let g ← getMainGoal
    let v ← Term.elabTermAndSynthesize e none
    g.assign (← instantiateMVars v)
  ```
  - `L5`: `kexactB <term>` 전술 정의. `withMainContext`로 현재 메인 목표의 지역 문맥(`LocalContext`)에 진입.
  - `L6`: 현재 메인 목표 메타변수 `g : MVarId` 획득.
  - `L7`: `Term.elabTermAndSynthesize e none`으로 기대 타입(`expectedType? := none`) 없이 항 `e`를 정규 엘라보레이션 및 타입클래스 합성.
  - `L8`: 메타변수 인스턴스화 후 `g.assign`으로 목표 메타변수 `g`에 항 `v`를 직접 대입.
  - **실제 호출 사례 확인**:
    - `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/PlaceModelImp.lean:27`: `scoped macro:max "kc% " e:term:max : term => `((by kexactB $e))`
    - `Development/AbelianVarietyTheory/Proofs/TwistedOperators/TwoLeMOf.lean:72-79`: `local macro:max "kd% " e:term:max : term => `((by kexactB $e))` 및 구조체 필드 전송(`isom := (by kexactB ($d).isom)` 등)
    - `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ECure.lean:58`: `by kexactB LinearIsometryEquiv.refl ℂ (ColT (h.shInj u))`

- **(b) Lean 4 커널/엘라보레이터 우회 불가 기술 근거**:
  - 일반 `exact e`는 엘라보레이터의 `Meta.isDefEq`로 `inferType v`와 `g.getType`의 동치를 사전 검사하므로, 거대한 중첩 구조체에서는 엘라보레이터 하트비트가 폭발할 수 있다. `kexactB`는 이 **엘라보레이터 단계의 사전 `isDefEq` 검사만 생략**하고 `MetavarContext`에서 `g := v`를 대입한다.
  - 그러나 해당 전술이 속한 `theorem`/`def`의 엘라보레이션이 끝나면, Lean 4는 조립된 최종 증명항 전체를 `Lean.addDecl` → C++ 커널 `lean_add_decl`로 제출한다. C++ 커널은 엘라보레이터의 `MetavarContext`나 `g.assign` 이력을 신뢰하지 않고 최종 폐쇄항(closed `Expr`)의 타입을 처음부터 독립 검증하며, `v`의 타입이 목표 타입과 커널 `is_def_eq` 기준 불일치하면 즉시 `(kernel) declaration type mismatch` 오류로 거부한다.
  - `kexactB`는 `Environment`를 전혀 수정하지 않고 `sorryAx` 생성 API도 호출하지 않으며, 입력 `e`는 `Term.elabTermAndSynthesize`로 정상 엘라보레이션된다.

- **(c) 정확한 의존성 풋프린트**:
  - 직접 임포터 **45개** 모듈.
  - `Main` 깊이 **7**, `Supplements.Kernels.MainTheorems` 깊이 **4**:
    `MainTheorems` → `MainConclusion` → `RiemannHypothesisOfEveryCharacter` → `TwoLeMOf` → `Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports`.
  - 모듈은 임포트 원뿔에 포함되나, 전술 엘라보레이터 `kexactB` 자체는 커널 증명항에 남지 않는다.

#### (3) & (4) `Formalism/LocalToGlobal/NumberFieldFamilies/OwnStruct.lean:1-66` — `elab "kcopy "` (`L53-58`) 및 `elab "#kcopy_probe "` (`L60-64`)

- **(a) 전문 요약 및 핵심 원문 발췌**:
  - `kdefeq` (`L7-13`): `a`, `b`에 미해결 메타변수가 없을 때 `Kernel.isDefEq (← getEnv) (← getLCtx) a b`를 **읽기 전용**으로 호출해 커널 정의적 동치 여부(`Bool`)를 반환한다.
  - `ownStruct` (`L15-16`): `isStructure env S`이면서 루트 네임스페이스가 `Formalism`이거나 핵심 튜플/논리 구조체 7종(``And``, ``Prod``, ``PProd``, ``Sigma``, ``PSigma``, ``Subtype``, ``Iff``)인지 판정한다.
  - `partial def copyAt` (`L18-51`): (상세 분석은 제1.4절 참조) 목표 타입 `tgt`가 함수형(`.forallE`)이면 `withLocalDecl` + `mkLambdaFVars`로 $\eta$-전개하고, `ownStruct env S`이면 구조체 생성자 `mkConst ctor.name us`에 파라미터를 적용한 뒤 각 필드를 `Expr.proj S i e`로 꺼내 재귀적으로 재조립한다(연료 `fuel`은 64에서 감소; `probe = true`일 때만 `kdefeq`와 `whnf`로 미일치 경로를 진단 배열에 기록).
  - 두 `elab` 선언 (`L53-64`):
    ```lean
    elab "kcopy " t:term : tactic => withMainContext do
      let g ← getMainGoal
      let tgt ← instantiateMVars (← g.getType)
      let e ← instantiateMVars (← Term.elabTermAndSynthesize t none)
      let (v, _) ← (copyAt false e tgt "" 64).run #[]
      g.assign (← instantiateMVars v)

    elab "#kcopy_probe " t:term " : " ty:term : command => Command.runTermElabM fun _ => do
      let tgt ← instantiateMVars (← Term.elabType ty)
      let e ← instantiateMVars (← Term.elabTermAndSynthesize t none)
      let (_, bad) ← (copyAt true e tgt "" 64).run #[]
      logInfo m!"kcopy_probe: {bad.size} refused: {bad.toList}"
    ```
  - **4개 직접 임포터 확인**:
    - `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsKeptChoiceUpperLattice.lean:26`: `by kcopy n.tp`, `by kcopy n.tie`, `by kcopy n.chrPsi`
    - `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FormsRe.lean:20`: `by kcopy T`
    - `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HermRe.lean:19`: `by kcopy H`
    - `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsColsTiedSym.lean:4`: 임포트만 존재
    - **`#kcopy_probe`는 저장소 전체에서 호출 0건** (순수 디버깅 진단용으로 남겨진 미호출 명령).

- **(b) Lean 4 커널/엘라보레이터 우회 불가 기술 근거**:
  - `kcopy`는 `copyAt false`로 순수한 핵심 커널 표현식(`.lam`, `.app`, `.const`, `.proj`)만을 합성해 `g.assign`으로 목표 메타변수에 대입한다. `kexactB`와 동일하게 `Environment`를 변경하지 않으며, 생성된 $\eta$-전개 증명항 전체가 최종 선언 등록 시 C++ 커널 `lean_add_decl`의 독립 타입체킹을 반드시 통과해야 한다. 만약 `e`와 `tgt`의 구조체 타입/필드가 호환되지 않으면 커널이 즉시 거부한다.
  - `#kcopy_probe`는 `Command.runTermElabM`으로 `copyAt true`를 실행하고 진단 문자열을 `logInfo`로 출력할 뿐 환경에 어떠한 선언도 추가하지 않으며, 실제 호출도 0건이다.

- **(c) 정확한 의존성 풋프린트**:
  - 직접 임포터 **4개** 모듈.
  - `Main` 깊이 **9**, `Supplements.Kernels.MainTheorems` 깊이 **6**:
    `MainTheorems` → `MainConclusion` → `RiemannHypothesisOfEveryCharacter` → `LinkOfClosedAtFamily` → `ExistsKeptChoiceUpperLatticeStatement` → `ExistsKeptChoiceUpperLattice` → `Formalism.LocalToGlobal.NumberFieldFamilies.OwnStruct`.
  - 모듈은 임포트 원뿔에 포함되나, `kcopy`·`#kcopy_probe`·`copyAt`·`kdefeq` 모두 커널 증명항에는 포함되지 않는다.

---

### 1.4 전체 저장소 `partial def` 2건 감사 (2개 파일 전문 열람)

`deep_audit_results.json` 기준 전체 175,187개 파일의 `partial def`(및 `partial abbrev`/`instance`/`theorem` 등 모든 `partial` 선언) 총합은 **정확히 2건**이다.

| # | 파일 및 행 번호 | 선언 시그니처 | 용도 및 종료 보장 구조 |
| -: | :--- | :--- | :--- |
| 1 | `Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean:41-52` | `partial def go (env : Environment) (n : Name) (st : NameSet × NameSet × Array Name) : NameSet × NameSet × Array Name` | `cpt_copy_thms` 내부의 컴파일타임 상수 의존 DAG 후위 DFS (`seen : NameSet`으로 방문 노드를 즉시 차단하므로 유한 `Environment` 위에서 반드시 종료) |
| 2 | `Formalism/LocalToGlobal/NumberFieldFamilies/OwnStruct.lean:18-51` | `partial def copyAt (probe : Bool) (e tgt : Expr) (path : String) (fuel : Nat) : StateT (Array String) MetaM Expr` | `kcopy`/`#kcopy_probe` 내부의 컴파일타임 구조체 $\eta$-전개기 (명시적 연료 인자 `fuel : Nat := 64`가 매 재귀 호출마다 `fuel - 1`로 감소하며 `fuel = 0`에서 즉시 반환) |

#### Lean 4 커널 건전성 논증 및 의존성 풋프린트

1. **Lean 4 커널에서 `partial def`의 본질적 건전성**: Lean 4는 `partial def f : α → β := body`를 논리 커널에 비종료 재귀 공리로 추가하지 않는다. 대신 공역 `β`의 `Inhabited`/`Nonempty` 증인을 요구하여 **`opaque` 상수**로 커널에 등록하므로(따라서 `Empty`나 `False`의 원소를 절대 생성할 수 없음), 커널은 `f`의 재귀 방정식을 전혀 전개할 수 없으며 `body`는 오직 컴파일러/VM 실행(엘라보레이터 메타코드 등)에만 쓰인다.
2. **메타 레벨 완전 격리**: 더 나아가 본 저장소의 `partial def` 2건은 모두 수학적 타입(`ℂ`, `DirichletCharacter` 등)과 무관한 **순수 컴파일타임 메타 함수**(`Environment`/`NameSet` 및 `MetaM Expr`)이며, `Main` 5개 최종 정리의 커널 증명항에는 **단 1회도 출현하지 않는다**.
3. **모듈 임포트 원뿔**: `CutCptCopy` (`MainTheorems` 깊이 14) 및 `OwnStruct` (`MainTheorems` 깊이 6) 경유로 모듈 원뿔에는 포함되나, 커널 증명항 원뿔과는 무관하다.

---

### 1.5 전역 `macro` 22건 · `allowUnsafeReducibility` 37건 · `hygiene` 31건 · 기타 비일상 `set_option` (100%) 감사

Round 1 샘플링을 넘어, 본 감사에서는 `deep_audit_results.json`에 수록된 **전역 `macro` 22건 (22/22)**, **`allowUnsafeReducibility` 37건 (37/37)**, **`hygiene` 31건 (31/31)**, 그리고 **기타 비일상 `set_option` 13건 (13/13)**의 원문 컨텍스트를 디스크에서 직접 100% 열람 검증하였다.

#### (1) 전역 `macro` 22/22건 검증 표 (19개 모듈, 전원 `MainTheorems` 원뿔 포함)

22건 **전원이 `: tactic =>` 전술 단축어**이며, 용어(`: term`)·명령(`: command`)·표기 매크로는 **0건**이다. 어떤 매크로도 Lean/Mathlib 기본 키워드나 `Statements.lean`/`Main.lean` 식별자를 섀도잉하지 않으며, 전개 결과는 일반 전술(`simp`, `omega`, `ring`, `grind`, `linarith`, `module`, `apply`, `erw`, `exact` 등)로 귀결되어 커널 타입체킹을 정식 통과한다.

| # | 파일 경로 (`src/...`) | 행 | 매크로명 | 카테고리 | 전개 핵심 내용 (원문 확인) |
| -: | :--- | ---: | :--- | :--- | :--- |
| 1 | `Development/AbelianVarietyTheory/Definitions/GaloisGeometry/NegOnePowBoundaryTermsCancel.lean` | 114 | `fin_index_simp` | `: tactic` | `simp (disch := ... omega) only [Fin.val_*, ...]; try omega` |
| 2 | `Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsProperOfFiniteType.lean` | 30 | `lbt` | `: tactic` | `repeat (first \| assumption \| apply pull_isLB)` |
| 3 | `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RigidFrameSymmetricRatioSeries.lean` | 49 | `jet_tac` | `: tactic` | `refine jet_ext ...; simp only [...]; refine congrArg _ ?_; simp [...]; try ring` |
| 4 | `Development/AutomorphicSpectrum/Proofs/BlockDecomposition/Cup1CoboundaryMemBoundaries.lean` | 96 | `fin_order` | `: tactic` | `apply Fin.ext; simp only [OrderHom.comp_coe, ...]; grind` |
| 5 | `Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleCup1FormulaPositiveDegree.lean` | 29 | `fin_order'` | `: tactic` | `apply Fin.ext; simp only [OrderHom.comp_coe, val_sI, ...]; grind` |
| 6 | `Development/EtaleCohomology/EtaleSheaves/ChasePf.lean` | 105 | `meq` | `: tactic` | `first \| (apply pullback.hom_ext <;> rw [← cancel_mono ...] <;> simp [...]) \| ...` |
| 7 | `Development/WeilBound/CoreStatements/HodgeTatePoints/CbBase.lean` | 34 | `zz` | `: tactic` | `repeat' with_reducible first \| assumption \| exact Z_pt _ \| ...` |
| 8 | `Development/WeilBound/CoreStatements/HodgeTatePoints/CbBase.lean` | 81 | `evs` | `: tactic` | `simp (disch := zz) only [evm, eva, ...] $[$loc]?` |
| 9 | `Development/WeilBound/CoreStatements/HodgeTatePoints/CcBase.lean` | 42 | `ztac` | `: tactic` | `repeat' (first \| assumption \| exact ZZ_nil \| ...)` |
| 10 | `Development/WeilBound/CoreStatements/HodgeTatePoints/CcBase.lean` | 81 | `evs at h` | `: tactic` | `simp (disch := ztac) only [FGLaw.add, ...] at $h:ident` |
| 11 | `Development/WeilBound/CoreStatements/PadicHodgeComparison/EtaleCohomologyComparison/CechPairings/FaceMapCompSuccAboveCastSucc.lean` | 227 | `fin_tac` | `: tactic` | `funext x; first \| (apply Fin.ext; simp only [...]; split_ifs <;> omega) \| ...` |
| 12 | `Formalism/EllipticTorsion/EllipticTorsionProofs/Change.lean` | 66 | `change_aux_intm` | `: tactic` | `repeat (first \| assumption \| apply ofNatB \| apply add_mem \| ...)` |
| 13 | `Formalism/HermitianCurvature/HermitianCurvatureProofs/RttUpperRelationsFromDescent.lean` | 30 | `distrib_module` | `: tactic` | `simp only [mul_sub, sub_mul, ..., smul_smul]; module` |
| 14 | `Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/FunctionalLowerBoundOfConditionsNumeric.lean` | 231 | `pos_tac` | `: tactic` | `(repeat' (first \| positivity \| apply mul_nonneg \| ...)) <;> linarith` |
| 15 | `Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/FunctionalLowerBoundOfConditionsNumeric.lean` | 234 | `onele_tac` | `: tactic` | `(repeat' (first \| exact one_le_pow₀ ... \| apply one_le_mul_of_one_le_of_one_le)) <;> assumption` |
| 16 | `Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/NonsingularNorm.lean` | 70 | `integ` | `: tactic` | `repeat' (first \| assumption \| exact i_ofNat _ \| apply i_add \| ...)` |
| 17 | `Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PFibreBoundV.lean` | 175 | `nbt` | `: tactic` | `simp only [unipotentBlockMatrix, Matrix.of_apply]; split_ifs <;> ...` |
| 18 | `Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaussianUniqueness/MulMApply.lean` | 12 | `lvo` | `: tactic` | `intro a b c h1 h2; (try dsimp only at h1 h2 ⊢); omega` |
| 19 | `Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaC.lean` | 7 | `fIwasawa_omega` | `: tactic` | `(try simp only [Fin.lt_def, ..., not_true_eq_false] at *) <;> omega` |
| 20 | `Formalism/SharpRestriction/Divisibility/LocalNonemptiness/SubsingletonRankIndicatorIff.lean` | 276 | `exists_prescribed_local_data` | `: tactic` | `intros; first \| trivial \| rfl \| exact Subsingleton.elim _ _ \| simp` |
| 21 | `ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExistsRosatiGen.lean` | 34 | `secTac` | `: tactic` | `simp [Sum.forall, Fin.forall_fin_succ, Over.w, ..., Matrix.cons_val_succ]` |
| 22 | `ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/Theta1.lean` | 25 | `ones` | `: tactic` | `repeat (first \| erw [map_one] \| erw [one_zpow] \| ... \| erw [_root_.one_mul])` |

*(참고: 나머지 국소/스코프 `macro` 65건 역시 `kc%`/`kq%`/`kd%`/`tr_via`/`obt`/`opens_le`/`tie_cases`/`pre_cases` 등 지역 전술·표현식 축약어만 포함하며, 모두 엘라보레이션 후 커널 검증을 통과한다.)*

#### (2) `allowUnsafeReducibility` 37/37건 검증 결과

37건 **전원이 타 모듈 정의에 `attribute [local irreducible]` 속성을 부여하기 위한 용도**이며, 단 1건도 `[reducible]` 강제 전환이나 전역 속성 변조가 아니다:
- **30건** (`IsCrisP.lean:49`, `AlgClosureTensorBcrisToBdRInjective.lean:67`, `ExistsPowNorm.lean:86` 등 `InertiaEigenvalues`/`IwasawaDecomposition` 26개 모듈): `attribute [local irreducible] Per.Acris Per.Bcris` (또는 `Per.Acris` 단독). 참고로 유일하게 `in` 없이 파일 스코프로 선언된 `ExistsPowNorm.lean:86-87`도 직후 `attribute [local irreducible] Per.Acris Per.Bcris` 1줄만 존재하고 이후 일반 정리(`homog_eq`, `untilt_zero`, `gauss_l` 등)만 이어짐을 직접 확인했다.
- **1건** (`ExistsFormFamilyHypothesesChangedSecondNorm.lean:38-40`): `attribute [local irreducible] _root_.NumberField.RingOfIntegers _root_.CommRing.toCommSemiring _root_.NumberField.instCommRingRingOfIntegers _root_.AddCommGroup.toAddCommMonoid`.
- **6건** (`AutomorphicInSphericalLevel.lean:218,315`, `CongLev.lean:177`, `EigGen.lean:154`, `FinOrbSubgroupOf.lean:213`, `LevUnion.lean:78`): `attribute [local irreducible] cv Kv Ov DX KD RP SA Lsq ...`.
- **커널 무관성**: `irreducible` 속성은 엘라보레이터의 `Meta` 투명도(transparency) 힌트일 뿐 C++ 커널은 `irreducible` 속성을 무시하고 모든 `def`의 정의적 동치를 동일하게 검사하므로, 건전성(soundness)에 영향을 줄 수 없다.

#### (3) `hygiene` 31/31건 검증 결과

31건 **전원이 `set_option hygiene false in` (단일 선언 스코프 한정)**이며, 직후 대상은 정확히 다음 3종뿐이다:
- `local notation` **22건** (예: `ExistsOrderTwoTranslateEvenCubicalBundle.lean:376-377` `local notation "𝔪" => ...`, `PNormalModelPlace.lean:174-189` `𝒜, ℬ, 𝒪, 𝒪̄, 𝒯, 𝒦, ℱ, 𝔏`, `PJoinDivCycle.lean:53-59` `ψ, ε`, `LocUnrSplit.lean:120-121` `𝟙` 등 — 섹션 변수를 표기 내부에서 직접 참조하기 위함).
- `local macro` **8건** (`FormGroupsModelsActionsMeasuresBasesCharacterise.lean:28,79`, `ReferenceTupleWeilDatumVectorPolynomialMapEnlarg.lean:23,159,211`, `ThetaLiftAtReferenceTupleOverEnlargedBase.lean:51,70,181` — `tie_cases`, `pre_cases`, `pre_sub`, `coef_cases` 전술 매크로가 호출부의 지역 가설명 참조).
- `scoped macro` **1건** (`RingSpecNormalisedCharacterEq.lean:73-75` — `scoped macro "copy_cases " h:ident D:ident D':ident : tactic`).
- **커널 무관성**: 매크로 위생(hygiene)은 파싱·매크로 전개 단계의 식별자 이름 포착 규칙에만 관여하며, 전개된 최종 증명항은 일반 코드와 동일하게 커널 타입체커를 통과한다.

#### (4) 기타 비일상 `set_option` 13/13건 및 전체 33종(88,139건) 점검

- `quotPrecheck false` **7/7건**: 전부 `local notation` 사전 구문검사 억제(`ExistsUniqueVectorFieldOfGlobalOneFormValues.lean:36`, `TwistedOrbitalSwapConvolution.lean:26,28`, `TuplesP.lean:1433`, `MeasFr.lean:90`, `MeasLev.lean:23`, `SatisfiesGlRelationsBilinearLeft.lean:43` — `section ops` 내부 `local notation "D"`, `"Mx"`).
- `smartUnfolding false in` **3/3건**: `ECure.lean:18`, `BuDefQEta.lean:123,136` — 엘라보레이터 WHNF 전개 휴리스틱 비활성화(커널 무관).
- `Elab.async false in` **1/1건**: `Decomp.lean:167` — 비동기 엘라보레이션을 끄고 **동기 커널 타입체킹**을 강제함(커널 우회와 정반대).
- `genSizeOf false` **1/1건**: `IsFirstChernClassInJAlt.lean:9` — 구조체 `SizeOf` 자동 보일러플레이트 생성 억제.
- `warn.classDefReducibility false in` **1/1건**: `BaseChangeMapMemLattice.lean:34` — `def bTop`의 린터 경고 억제.
- **전체 33종 `set_option` (88,139건) 최종 확인**: `maxHeartbeats`(57,556), `autoImplicit`(11,203), `maxSynthPendingDepth`(7,478), `synthInstance.maxHeartbeats`(7,381), `backward.isDefEq.respectTransparency`(+`.types`, 1,966), `linter.*`(14종 1,987), `genSizeOfSpec`/`genInjectivity`/`genSizeOf`(361), `synthInstance.maxSize`/`maxRecDepth`(85), `allowUnsafeReducibility`(37), `backward.defeqAttrib.useBackward`(33), `hygiene`(31), `pp.fullNames`(9), `quotPrecheck`(7), `smartUnfolding`(3), `Elab.async`(1), `warn.classDefReducibility`(1)가 전부이며, **`debug.skipKernelTC`, `debug.proofAsSorry`, 커널 검사 우회 옵션은 0건**이다.

---

## 제2부. 해석적 수론 경계조건 감사 (Mathematical Edge-Case Audit)

### 2.1 `Main.lean` 5개 최종 정리와 `Statements.lean` · Mathlib 정의적 일치성 검증

`Statements.lean` (`L1`: `import Mathlib` 단독) 및 `Main.lean` (`L1-12`) 전문과 호출 사슬 핵심 파일(`MainTheorems.lean`, `HalfPlane.lean`, `ClaimStrip.lean`, `CritLine.lean`, `RhOfRight.lean`, `EveryCharacter.lean`, `Imprimitive.lean`)을 대조한 결과는 다음과 같다:

| `Main.lean` 정리 | 선언 타입 (`Statements.lean` / Mathlib) | 증명항 (`MainTheorems.lean`) | 정의적 동치 검증 근거 |
| :--- | :--- | :--- | :--- |
| `Main.riemannHypothesis` (`L4`) | `RiemannHypothesis` (Mathlib 표준) | `rhOfAll` (`L9`) | Mathlib `RiemannHypothesis` 직접 반환 |
| `Main.riemannZeta_eq_zero_re` (`L6`) | `RiemannZetaZerosOnLine` (`Statements.lean:3-4`) | `rhOfAll` (`L9`) | `rhOfAll : RiemannHypothesis`를 변환 없이 직접 대입 + `ClaimStrip.lean:102` `theorem zeta_iff : Zeta ↔ RiemannHypothesis := Iff.rfl` |
| `Main.LFunction_ne_zero_of_half_lt_re` (`L8`) | `DirichletLNonvanishingRightOfHalf` (`Statements.lean:6-8`) | `allChi` (`L7`) | `UpperTheory.EveryCharacter` (`EveryCharacter.lean:13-14`) 및 `Claim.HalfPlane` (`HalfPlane.lean:3-4`)와 문자·타입 **완전 일치** |
| `Main.LFunction_eq_zero_re` (`L10`) | `DirichletLZerosOnLine` (`Statements.lean:10-12`) | `claimAll.2.1` (`L15-16`) | `Claim.Strip` (`HalfPlane.lean:6-7`)와 문자·타입 **완전 일치** |
| `Main.LFunction_eq_zero_re_of_isPrimitive` (`L12`) | `PrimitiveDirichletLZerosOnLine` (`Statements.lean:14-16`) | `critAll` (`L11-13`) | `Formalism.VW.critLine` (`CritLine.lean:11-27`)의 출력 타입과 **완전 일치** |

---

### 2.2 리만 제타 함수 $\zeta(s)$ 경계조건 감사

`Statements.lean:3-4` 원문:
```lean
def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2
```

1. **자명한 영점 $s = -2, -4, -6, \dots$ 제외의 정확성**:
   - Lean 4의 `ℕ`은 `0`부터 시작하므로 `n : ℕ`에 대해 `n + 1`은 정확히 $\{1, 2, 3, \dots\}$를 순회하며, `-2 * ((n : ℂ) + 1)`은 정확히 음의 짝수 $\{-2, -4, -6, \dots\}$만 가리킨다.
   - `ClaimStrip.lean:102` (`theorem zeta_iff : Zeta ↔ RiemannHypothesis := Iff.rfl`)와 `Main.lean:4,6`의 직접 항 공유로 Mathlib `0df444a3`의 공식 `RiemannHypothesis` 정의와 정의적으로 100% 동일함이 보장된다.
2. **$s = 0$ 경계조건 (제외되지 않고 비영임을 직접 증명)**:
   - `¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)`은 **`s = 0`을 제외하지 않는다**. 만약 `s = 0`을 허술하게 제외했다면 부적절한 약화가 되지만, 실제로는 **3개의 독립된 증명 경로 모두** Mathlib의 `riemannZeta_zero` ($\zeta(0) = -1/2 \neq 0$)로부터 `s ≠ 0`을 직접 도출한다:
     - `Formalism/GammaFactorNonvanishing/RhOfRight.lean:11-14`:
       ```lean
       have hs0 : s ≠ 0 := by
         rintro rfl
         rw [riemannZeta_zero] at hs
         norm_num at hs
       ```
     - `Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:77`:
       ```lean
       have hs0 : s ≠ 0 := fun e => by rw [e, riemannZeta_zero] at hz; norm_num at hz
       ```
     - `Development/AutomorphicArithmetic/CharacterBoxes/RiemannHypothesisOfEveryCharacter.lean:219`:
       ```lean
       have hs0 : s ≠ 0 := by rintro rfl; rw [riemannZeta_zero] at hs; norm_num at hs
       ```
   - 또한 함수형 방정식 반사 시 나타나는 감마/코사인 인자의 $s = 0$ 특이점도 빠짐없이 소거된다:
     - `RhOfRight.lean:34-59`: `Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) = 0`에서 `s = -2 * (k : ℂ)` ($k : \mathbb{Z}$)를 얻은 뒤 `lt_trichotomy k 0`으로 삼분하여, $k < 0 \Rightarrow \operatorname{Re}(s) \ge 2$ ($\operatorname{Re}(s) < 1/2$와 모순, `L45-46`), $k = 0 \Rightarrow s = 0$ (`hs0`와 모순, `L47-49`), $k > 0 \Rightarrow s = -2((k-1)+1)$ (`htriv`와 모순, `L50-58`)으로 완결 처리한다.
     - `ClaimStrip.lean:85-90` (및 `RiemannHypothesisOfEveryCharacter.lean:227-230`): `Complex.Gammaℝ_eq_zero_iff`에서 얻은 `n : ℕ` ($s = -2n$)에 대해 `rcases n with _ | n`으로 분기하여 `n = 0`은 `hs0`로(`L89`), `n + 1`은 `htriv`로(`L90`) 소거한다.
3. **$s = 1$ 극점 처리**:
   - `s ≠ 1`로 표준 RH 정의 및 Mathlib `RiemannHypothesis`와 일치하게 극점을 제외한다.
   - 추가 확인: Mathlib `0df444a3`에서 `riemannZeta 1`은 로랑 전개 상수항 $(\gamma - \log(4\pi))/2$에 해당하는 정규화 값으로 정의되어 있으며 `riemannZeta_one_ne_zero` (`Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/poleData.lean:196`에서 직접 참조) 및 `riemannZeta_ne_zero_of_one_le_re` (`ClaimStrip.lean:83,100`에서 직접 참조)가 성립한다. 즉 `s = 1`에 0이라는 junk value가 배정되어 공허한 모순을 일으킬 여지가 전혀 없다.
4. **$\operatorname{Re}(s) \ge 1$ 및 $\operatorname{Re}(s) \le 0$ 영역 완전성**:
   - `RhOfRight.lean:8-62`는 `lt_trichotomy s.re (1 / 2)`로 전 복소평면을 분할한다: $\operatorname{Re}(s) > 1/2$는 `hz s hgt hs1`로 직결(`L62`), $\operatorname{Re}(s) < 1/2$는 `riemannZeta_one_sub`의 모든 전제조건(`∀ n : ℕ, 1 - s ≠ -n` `L22-27`, `1 - s ≠ 1` `L18-21`)과 비영 인자(`h2pi`, `hG`, `hcos` `L31-59`)를 검증해 `hz (1 - s)`로 모순 도출한다.
   - `ClaimStrip.lean:75-100`은 독립적으로 $0 < \operatorname{Re}(s) < 1$ (`Claim.strip` + `LFunction_modOne_eq`), $\operatorname{Re}(s) \ge 1$ (`riemannZeta_ne_zero_of_one_le_re`), $\operatorname{Re}(s) \le 0$ (`completedRiemannZeta_one_sub` + $\operatorname{Re}(1-s) \ge 1$)의 3분할 증명을 제공한다.

---

### 2.3 디리클레 $L$-함수 $L(s, \chi)$ 경계조건 감사 (GRH)

`Statements.lean:6-16` 원문:
```lean
def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
```

#### (1) 법(modulus) $N = 0$ 제외 검증 (`[NeZero N]`)
- 3개의 디리클레 $L$-함수 정리(`Statements.lean:7,11,15`)와 내부 정의(`EveryCharacter.lean:14`, `HalfPlane.lean:4,7`, `Imprimitive.lean:6`, `CritLine.lean:11`, `PrimePairSizeCondition.lean:9`) 모두 `[NeZero N]` 타입클래스 인자를 요구한다.
- Mathlib에서 `ZMod 0 = ℤ`이므로 `DirichletCharacter ℂ 0`은 유한 법 위의 고전적 디리클레 지표가 아니다. `[NeZero N]`은 정확히 $N \ge 1$인 모든 양의 정수 법을 포괄한다.

#### (2) 극점 $s = 1$ 및 주지표($\chi = 1$) vs 비주지표($\chi \neq 1$) 분기 (`χ ≠ 1 ∨ s ≠ 1`)
- **비주지표 ($\chi \neq 1$, 원시/비원시 불문)**: `Or.inl hχ`로 `(χ ≠ 1 ∨ s ≠ 1)`이 **$s = 1$에서도 참**이 된다. 따라서 `Main.LFunction_ne_zero_of_half_lt_re`는 모든 비주지표에 대해 디리클레 비소멸 정리 $L(1, \chi) \neq 0$까지 정식으로 포함한다.
- **주지표 ($\chi = 1 \pmod N$, $N = 1$ 및 $N > 1$ 모두)**: `χ ≠ 1 ∨ s ≠ 1`은 정확히 `s ≠ 1`로 축약되어 유일한 단순극 $s = 1$만 제외하고, $\operatorname{Re}(s) > 1/2,\ s \neq 1$ 전역(직선 $\operatorname{Re}(s) = 1, \operatorname{Im}(s) \neq 0$ 포함)에서 비소멸을 보장한다.
- **핵심 미묘점 규명 (`Imprimitive.lean:10-20` vs `ExplicitFormulaErrorOfHostConditions.lean:11-18`)**:
  - 내부 정리 `Formalism.HC.ZeroFreeAll` (`ExplicitFormulaErrorOfHostConditions.lean:11-18`)은 원시 지표 구조체 `PChar`에 대해 `∀ s : ℂ, 1 / 2 < s.re → DirichletCharacter.LFunction ψ.χ s ≠ 0`으로 `s ≠ 1` 조건 없이 진술되며, `Imprimitive.lean:10`은 이를 그대로 호출한다:
    ```lean
    -- Development/AutomorphicArithmetic/CharacterBoxes/Imprimitive.lean:9-20
    haveI : NeZero χ.conductor := (PChar.of χ).ne
    have hL : DirichletCharacter.LFunction χ.primitiveCharacter s ≠ 0 := h (PChar.of χ) trivial s hs
    have hχ' : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := by
      rcases hχs with hχ | hs1
      · left
        intro h1
        apply hχ
        rw [← χ.changeLevel_primitiveCharacter, h1, DirichletCharacter.changeLevel_one]
      · exact Or.inr hs1
    have hrw := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter hχ'
    rw [χ.changeLevel_primitiveCharacter] at hrw
    rw [hrw]
    ```
  - 이것이 성립하는 정확한 이유: `PChar`는 원시 지표이므로 주지표인 경우는 오직 `PChar.one` ($N = 1, \chi = 1_1$, `PrimePairSizeCondition.lean:19`)뿐이며, 이 경우 `LFunction_modOne_eq`로 `riemannZeta`와 같아지고 Mathlib의 `riemannZeta_ne_zero_of_one_le_re` / `riemannZeta_one_ne_zero`에 의해 `s = 1`에서도 비영이다(`CharFamilyLFunctionNeZeroOfOneLeRe.lean:17-20`, `poleData.lean:196`).
  - 반면 $N > 1$인 비원시 주지표 $\chi = 1_N$에서는 $L(1_N, s) = \zeta(s) \prod_{p \mid N}(1 - p^{-s})$의 극점 $s = 1$에서 로랑 상수항이 미분항만큼 이동하므로 Mathlib의 `DirichletCharacter.LFunction_changeLevel`이 정확히 `χ.primitiveCharacter ≠ 1 ∨ s ≠ 1`을 전제조건으로 요구한다. `Imprimitive.lean:11-18`은 `χ.changeLevel_primitiveCharacter`와 `DirichletCharacter.changeLevel_one`으로 `χ ≠ 1 ∨ s ≠ 1`을 `χ.primitiveCharacter ≠ 1 ∨ s ≠ 1`로 정확히 변환해 이를 만족시킨다.

#### (3) 원시 vs 비원시 지표, 도체 $\chi.\mathrm{conductor}$, 오일러 인자 비소멸
- 임의의 법 $N \ge 1$의 지표 $\chi$에 대해 `χ.conductor_ne_zero`로 `[NeZero χ.conductor]`가 성립하고, `χ.conductor_dvd_level` 및 `χ.changeLevel_primitiveCharacter`에 의해 Mathlib의 `DirichletCharacter.LFunction_changeLevel`은 다음을 준다:
  $$L(\chi, s) = L(\chi^*, s) \prod_{p \in N.\mathrm{primeFactors}} \bigl(1 - \chi^*(p)\, p^{-s}\bigr)$$
  (여기서 $\chi^* = \chi.\mathrm{primitiveCharacter}$는 법 $q = \chi.\mathrm{conductor}$의 원시 지표이다. $p \mid q$이면 $\chi^*(p) = 0$이므로 인자는 $1$이고, $p \mid N,\ p \nmid q$이면 $|\chi^*(p)| = 1$이다.)
- **$\operatorname{Re}(s) > 0$ 전역에서 오일러 인자 비소멸 증명**:
  - `ClaimStrip.lean:7-21` (`Claim.factor_ne_zero`, $\operatorname{Re}(s) > 0$ 전체에 대해 증명) 및 `Imprimitive.lean:21-35` ($\operatorname{Re}(s) > 1/2$에 대해 증명) 모두 소수 $p \ge 2$ (`hp.one_lt`, `hp.pos`)에 대해:
    1. `Complex.norm_natCast_cpow_of_pos` + `Real.rpow_lt_one_of_one_lt_of_neg`로 $\|p^{-s}\| = p^{-\operatorname{Re}(s)} < 1$ 도출,
    2. `DirichletCharacter.norm_le_one`으로 $\|\chi^*(p)\| \le 1$ 적용,
    3. 따라서 $\|\chi^*(p) p^{-s}\| \le 1 \cdot p^{-\operatorname{Re}(s)} < 1$, 즉 $1 - \chi^*(p) p^{-s} \neq 0$을 엄밀 증명한다.
- **임계대 내 비원시 영점 → 원시 영점 환원 (`ClaimStrip.lean:23-33` `Claim.prim_zero`)**:
  - `hs1 : s.re < 1`로부터 `s ≠ 1`을 도출(`L26`)하여 주지표 $\chi = 1_N$ ($N > 1$)에 대해서도 `LFunction_changeLevel ... (Or.inr hs)`를 정당하게 적용한 뒤(`L27-28`), 오일러 인자 곱이 비영(`factor_ne_zero`, `L33`)이므로 $L(\chi^*, s) = 0$을 도출한다.

#### (4) 경계선 $\operatorname{Re}(s) = 0$ 및 $\operatorname{Re}(s) = 1$ 거동
- **$\operatorname{Re}(s) = 0$ (엄격 부등식 `0 < s.re`의 수학적 필수성)**:
  - 비원시 지표 $\chi \pmod N$ (특히 $N > 1$인 주지표 $\chi = 1_N$, $q = 1 < N$)는 $p \mid N,\ p \nmid q$인 각 소수 $p$마다 인자 $(1 - \chi^*(p)p^{-s})$가
    $$s = \frac{i\bigl(\arg \chi^*(p) + 2\pi k\bigr)}{\log p} \quad (k \in \mathbb{Z})$$
    에서 소멸하므로 **직선 $\operatorname{Re}(s) = 0$ 위에 무한히 많은 비자명 외형 영점**을 가진다(주지표 $\chi = 1_N$의 경우 $s = 2\pi i k / \log p$).
  - 또한 원시 우지표($\chi \neq 1,\ \chi(-1) = 1$) 역시 $\Gamma_{\mathbb{R}}(s)$의 $s = 0$ 극점으로 인해 $s = 0$에서 자명한 영점을 가진다.
  - 따라서 `DirichletLZerosOnLine` (`Statements.lean:12`)과 `PrimitiveDirichletLZerosOnLine` (`Statements.lean:16`)이 `0 < s.re`로 $\operatorname{Re}(s) = 0$을 엄격히 제외하는 것은 고전적 GRH 정식화와 **완벽히 일치**한다.
- **$\operatorname{Re}(s) = 1$**:
  - 임계대 명제에서는 `s.re < 1`로 제외되며, $\operatorname{Re}(s) = 1$ 위의 비소멸성(주지표의 $s = 1$ 단순극만 제외)은 이미 `Main.LFunction_ne_zero_of_half_lt_re` ($\operatorname{Re}(s) > 1/2$)에 의해 완전 포함된다.

#### (5) 임계대 $s \in (0, 1) \times i\mathbb{R}$에서 `DirichletCharacter.LFunction χ s`와 고전적 $L(s, \chi)$의 일치성 및 함수형 방정식 반사
- Mathlib `0df444a3`에서 `DirichletCharacter.LFunction χ s`는 $\operatorname{Re}(s) > 1$에서 디리클레 급수 $\sum_{n=1}^{\infty} \chi(n) n^{-s}$ (`LSeries`)와 일치하는 유일한 해석적 연속(비주지표는 전해석 함수, 주지표는 $s = 1$에서만 단순극)이며, $s \neq 0$ 전역에서 `DirichletCharacter.LFunction_eq_completed_div_gammaFactor` ($\Lambda(\chi, s) / \gamma_\chi(s)$)을 만족한다.
- 열린 임계대 $0 < \operatorname{Re}(s) < 1$에는 극점 $s = 1$도 감마 인자 극점 $s \in \{0, -1, -2, \dots\}$도 포함되지 않으므로 Mathlib의 junk value가 일절 개입하지 않으며, **점별(pointwise)로 고전적 $L(s, \chi)$와 완전 일치**한다.
- **임계대 반사 증명 검증 (`ClaimStrip.lean:35-73` 및 `CritLine.lean:6-27`)**:
  - 감마 인자 비소멸(`Claim.gamma_ne_zero` `L35-40`, `Formalism.VW.gammaFactor_ne_zero` `L6-9`): `χ.even_or_odd`로 분기하여 우지표는 $\Gamma_{\mathbb{R}}(s)$ ($\operatorname{Re}(s) > 0$), 기지표는 $\Gamma_{\mathbb{R}}(s + 1)$ ($\operatorname{Re}(s + 1) > 1 > 0$)에 `Complex.Gammaℝ_ne_zero_of_re_pos`를 적용.
  - 함수형 방정식 반사(`Claim.prim_reflect` `L42-57`, `Formalism.VW.critLine` `L11-27`): 원시 지표 $\psi$에 대해 `ψ⁻¹.IsPrimitive` (`isPrimitive_def`, `conductor_inv`)를 증명한 뒤 `hψ'.completedLFunction_one_sub s`를 적용하여 $\Lambda(\psi, s) = 0 \Rightarrow \Lambda(\psi^{-1}, 1 - s) = 0$, 다시 `1 - s ≠ 0` (`s.re < 1`로부터 도출)과 `LFunction_eq_completed_div_gammaFactor`로 $L(\psi^{-1}, 1 - s) = 0$을 도출한다.
  - 최종 모순(`ClaimStrip.lean:69-71`, `CritLine.lean:25`): `0 < s.re`로부터 `s ≠ 0` → `1 - s ≠ 1`을 도출하여 `Or.inr ht`를 충족시키고, $\operatorname{Re}(1 - s) > 1/2$에서 `HalfPlane`/`EveryCharacter`를 호출해 모순을 완결한다.

---

### 2.4 `MainTheoremsAll.lean` → `SmallClassNumbers.CorGKOf` 격리 검증

`Main.lean`의 임포트 계층을 말단까지 추적하면 다음과 같다:
1. `Main.lean:1-2`: `import Statements`, `import Supplements.Kernels.MainTheoremsAll`.
2. `Supplements/Kernels/MainTheoremsAll.lean:1-2` (선언 0개):
   ```lean
   import Supplements.Kernels.MainTheoremsCritical
   import Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.CorGKOf
   ```
3. `Supplements/Kernels/MainTheoremsCritical.lean:1-4` (선언 0개):
   ```lean
   import Supplements.Kernels.MainTheorems
   import Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.ClassNumberThree
   import Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.LenEqZeroIff
   import Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.OnePoint
   ```
4. `Supplements/Kernels/MainTheorems.lean:1-16`: 오직 `CritLine`, `ClaimStrip`, `MainConclusion`만 임포트하며 `Main.lean`의 5개 정리가 사용하는 4개 증명항(`allChi`, `rhOfAll`, `critAll`, `claimAll`) 전부를 정의한다.

**격리성 수학적·데이터베이스 완전 검증**:
- 4개 `SmallClassNumbers` 모듈(`CorGKOf`, `ClassNumberThree`, `LenEqZeroIff`, `OnePoint`)의 모듈명은 **전부 순수 ASCII 문자열**이다. Round 1에서 규명된 `index_lean.py:21`의 유니코드 `₂` 절단 버그는 오직 `dst_module`에 `₂`가 포함된 간선만 유실시키므로, 전체 175,187개 파일(유니코드 `₂` 모듈 394개 포함)에서 위 4개 모듈을 향하는 모든 `import` 간선은 DuckDB `imports` 테이블에 100% 누락 없이 수록되어 있다.
- DuckDB `imports` 조회 결과:
  - `SmallClassNumbers.CorGKOf`의 유일한 임포터: `['Supplements.Kernels.MainTheoremsAll']`
  - `SmallClassNumbers.LenEqZeroIff`의 유일한 임포터: `['Supplements.Kernels.MainTheoremsCritical']`
  - `SmallClassNumbers.OnePoint`의 유일한 임포터: `['Supplements.Kernels.MainTheoremsCritical']`
  - `SmallClassNumbers.ClassNumberThree`의 임포터: `['...CorGKOf', '...LenEqZeroIff', 'Supplements.Kernels.MainTheoremsCritical']`
  - 기존 DB 미도달 420개 모듈 중 `SmallClassNumbers.*`를 임포트하는 모듈: **`[]` (0건)**.
- **결론**: `Main` 전체(175,187개 모듈)와 `Supplements.Kernels.MainTheorems` 의존 원뿔(175,179개 모듈)의 차집합은 정확히 8개 모듈(`Main`, `Statements`, `MainTheoremsAll`, `MainTheoremsCritical`, 및 `SmallClassNumbers` 4개 모듈)뿐이다. `SmallClassNumbers.{CorGKOf, ClassNumberThree, LenEqZeroIff, OnePoint}`는 동일한 보형/갈루아 기반(`RowSrc`, `TopMainZj`, `DefiniteNHolds`) 위에서 유수 1 이차체 $K^*_3$ (`classNumber_three : classNumber (Kstar 3) = 1`)의 셀머/샤파레비치-테이트 군 길이 상계(`UpperTheory.V.SmallClassNumbers.corGK`, `bound`, `large_of`, `onePoint`)를 추가로 증명해 `MainTheoremsAll`에 묶어 둔 동반(companion) 정리들이며, **`Main.lean`의 5개 RH/GRH 최종 정리의 명제·증명항·의존 공리에 미치는 영향은 정확히 0**이다.

---

## 제3부. 최종 종합 요약 및 사후 동적 검증 절차

1. **메타프로그래밍 사각지대 0건**: `CutCptCopy.lean`(`addDecl` 2건), `BuildAid/D1..D5`(`run_cmd`/`modifyEnv` 5건), 전체 `elab` 4건(`cpt_copy_thms`, `kexactB`, `kcopy`, `#kcopy_probe`), 전체 `partial def` 2건(`go`, `copyAt`), 전역 `macro` 22/22건, `allowUnsafeReducibility` 37/37건, `hygiene` 31/31건, 기타 비일상 `set_option` 13/13건을 원문에서 행마다 검증 완료하였으며, 단 1건의 커널 우회·공리 주입·심볼 섀도잉도 존재하지 않는다.
2. **수학적 경계조건 사각지대 0건**: `Main.lean`의 5개 정리(`riemannHypothesis`, `riemannZeta_eq_zero_re`, `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive`)는 자명한 영점($-2,-4,\dots$), $s=0$ 비영 증명(`riemannZeta_zero`), 극점 $s=1$, `[NeZero N]`, 주지표/비주지표 분기(`χ ≠ 1 ∨ s ≠ 1`), 비원시 지표 오일러 인자 비소멸($\operatorname{Re}(s) > 0$), 경계선 $\operatorname{Re}(s) = 0, 1$ 거동, 그리고 Mathlib `0df444a3` `DirichletCharacter.LFunction`의 임계대 일치성까지 고전적 RH/GRH 정의와 100% 부합한다. `SmallClassNumbers.CorGKOf`는 `MainTheorems` 원뿔 외부에 완전 격리되어 있다.
3. **최종 동적 커널 인증(후속 권장)**: 로컬에 공식 `leanprover/lean4:v4.33.1` 툴체인 및 Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` 캐시 확보 후 `lake build Main` 및 5개 정리 `#print axioms` 실행을 통해 허용 표준 공리(`propext`, `Classical.choice`, `Quot.sound`) 외 0건임을 최종 동적 확정한다.
