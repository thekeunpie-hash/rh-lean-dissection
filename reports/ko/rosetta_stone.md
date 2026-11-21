# RH / GRH Lean 4.33.1 증명 로제타 스톤 (`rosetta_stone.md`)

> **작성자**: `@math_translator` (Track B — Round 2)  
> **분석 대상**: `../lean/src/` (175,187 모듈 / 17,374,215줄 / 1,061,425 선언, Lean `v4.33.1`, Mathlib rev `0df444a360eaa60ab8c11dca51a86af692955474`, 유니코드 DAG 기준 175,187/175,187 전수 도달)  
> **핵심 방법론 (Anti-Fallacy 원칙)**: 문자열 키워드 부재(`Stepanov`, `Bost`, `Vandiver`, `Lichtenbaum`, `2/3` 등)를 곧바로 수학적 개념의 부재로 단정하는 오류를 배제하고, `lean_index.duckdb` 색인과 실제 Lean 소스 파일의 `def`·`structure`·`theorem` 타입 시그니처 및 정의 본문(증명 `by ...` 제외)을 1:1 대조하여 Levent Alpöge 발표문의 9대 핵심 개념을 다음 3범주로 엄밀 판정하였다.
> - **`[개념 동일·명칭만 변경]`**: 발표문의 수학적 정의·정리·공식이 실제 Lean 코드에 본질적으로 동일하게 구현되어 있으며 식별자·모듈명만 다르다.
> - **`[구조 변형·우회]`**: 발표문의 문제의식·핵심 도구가 코드 내에 실재하되, 군·표현·스펙트럼 기법이 다른 아키텍처로 변형되거나 일부 하위 개념이 대체·우회되어 결합되어 있다.
> - **`[실제 코드에 미사용·대체됨]`**: 발표문의 해당 수학적 대상 자체는 코드베이스에 존재하지 않으며, 근본적으로 다른 메커니즘이 그 역할을 대체한다.

---

## 0. 9대 개념 총괄 판정표 (Executive Matrix)

| # | Levent Alpöge 발표문 핵심 개념 | 최종 판정 | Round 1 키워드 함정(문자열) | 실제 Lean 코드의 수학적 실체 | 핵심 검증 앵커 (모듈 :: 선언) |
| :-: | :--- | :--- | :--- | :--- | :--- |
| **①** | **Stepanov 논증(중복도 모방) & $O(2,n)$ 보형적 행렬식(중복도 2)** | **`[실제 코드에 미사용·대체됨]`** | `Stepanov`=0건, `O2`=4모듈(대소문자 무시 5모듈, 구조층 `HO2`·`Two2`뿐) | $O(2,n)$ 및 Stepanov 다항식 행렬식은 부재. 대신 **CM체 에르미트 공간·유니타리군 $U(X_j)/U(Y_j)/U(W_j)$ + Bost/HN 앙상블 기울기 부등식 + 비분해 소수 거듭제곱 가분성 증폭·$p$-진 jet(`ThetaJet`)·쌍행렬식(`bidetSpan`)**으로 전면 대체. | `Formalism.LocalRingCardinality.DataSpaces` :: `Formalism.BasicNotions.Spaces`<br>`Formalism.SharpRestriction.GlobalTheoremInputs` :: `Formalism.MainNotions.LinkG_at`<br>`Formalism.LocalRingCardinality.DataJet` :: `Formalism.BasicNotions.ThetaJet` |
| **②** | **von Mangoldt 가중합 $\sum_{n \le X} \Lambda(n)(X/n - 1)_+ - X\log X + (1+\gamma)X$** | **`[개념 동일·명칭만 변경]`** | `vonMangoldt`=16모듈/79선언 | **수식 100% 문자 그대로 일치.** `Sz`/`Gz`/`Schi`/`Gchi` 및 순환군 가중합 `Level.Gm`으로 직접 정의되며, `AskMainBalance`·`FormBAt`·`level_of_tiedWin`·`GrowthSizeBound`로 `ZeroFreeAll`을 닫는다. | `Formalism.StatementOC` :: `Formalism.Gz`<br>`Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions` :: `Formalism.HC.Level.Gm`<br>`Formalism.GL3MeanSquares.HookFormulaTorsion.WeightedVonMangoldtSumIdentity` :: `Formalism.HermitianLattices.ZeroFreeRegionGL2.weighted_von_mangoldt_sum_identity` |
| **③** | **반복 세타 올림 $U(X_0) \to \dots \to U(X_m)$ ($m \sim \sqrt{X}$)** | **`[개념 동일·명칭만 변경]`** | `ThetaLift`=1,321모듈, `ThetaPair`=3,061모듈 | **공간열·사슬 길이 모두 완전 일치.** 정칙 에르미트 공간열 $X_0,\dots,X_m$ (계수 $N(j)=k+j(t+1)$)과 교대 Bessel↔Fourier–Jacobi 사슬 `GlobalTheory.Unf.Chain`, 커널 사슬 `ColumnChain.col`이 정확히 $x^{1/2-\varepsilon/16} \le m \le 2x^{1/2-\varepsilon/16}$에서 작동. | `Formalism.LocalRingCardinality.Params` :: `Formalism.BasicNotions.Ranks`<br>`Formalism.LocalRingCardinality.DataKernels` :: `Formalism.BasicNotions.ColumnChain.col`<br>`Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam` :: `GlobalTheory.Unf.Chain`<br>`Formalism.SizeWindowBrackets.SChain` :: `Formalism.LFunctionChainParameters.LChain.SizesTextAt` |
| **④** | **시소 관계 & Rallis / Hecke 지표 무관 Bessel 주기** | **`[개념 동일·명칭만 변경]`** | `Seesaw`=452모듈, `Rallis`=91모듈, `Bessel`=1,188모듈 | **전 요소 실재.** 시소 항등식·Fubini, Rallis 내적 공식(`rallis_of_dm`, `rallis_inner_product_big_theta_lift`), 중복도 1 Bessel 유일성(`BesselMapUniq`, `BesselId`), Siegel–Weil(`WeilSiegelCM`, `SiegelWeilAnisotropicHermitian`), 그리고 세타 노름·높이 무관성(`ThetaNormIndependent`, `LinkDIV_at` L87–89)이 완비됨. | `Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.RallisDM` :: `UpperTheory.Lit.Rallis.RallisIPProof.rallis_of_dm`<br>`Formalism.PeriodIntegrals.BesselMapUniq` :: `PI.BesselMapUniq.BesselMapUniq`<br>`Formalism.SharpRestriction.GlobalTheoremInputs` :: `Formalism.MainNotions.BesselId`<br>`Formalism.LocalToGlobal.GlobalTheory.GL3.Statement` :: `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.ThetaNormIndependent` |
| **⑤** | **$2/3$ 장벽 돌파 (Hecke 지표 평균화 & 상대 추적 공식 반평면 논증)** | **`[구조 변형·우회]`** | `TwoThird`=0, `Kuznetsov`=0, `RelativeTrace`=2모듈(2차체 대각합) | 문자 그대로의 $2/3$ 장벽·Kuznetsov·RTF 반평면 논증은 없다. 대신 (a) $m \sim \sqrt{x}$ 균형(`SizeWindows`: $x/m$과 $m$의 균형 $\Rightarrow x^{1/2}$), (b) 평행이동·단어 앙상블 평균(`topExcess`, `MeanBoundSecondForm`, `QH.meanSqK`), (c) **부정치 $U(p,q)$ Bessel Poincaré 급수의 이중 잉여류 전개·행렬계수 감쇠(`PoincareInHH`, `WuDecayOfGap`, `LinkS_at`)** 및 Siegel Eisenstein 반평면 접속으로 우회·달성. | `Formalism.SizeWindowBrackets.GrowthBoundGivesRiemannHypothesis` :: `Formalism.LFunctionChainParameters.ThickSetMeanBounds.SizeWindows`<br>`Formalism.RankGapBounds.MeanBoundSecondForm` :: `Formalism.RankGapBounds.WeightedMeanData.Data.MeanBoundSecondForm`<br>`Development.AutomorphicArithmetic.MeanSquareBounds.meanSqK` :: `QH.meanSqK` |
| **⑥** | **$\mathrm{GL}_5$ 6중 피복 위 $\mu$ 보형성 & 사영된 Poincaré 급수의 Cauchy–Schwarz 상한** | **`[구조 변형·우회]`**<br>*(전반부 미사용·대체 / 후반부 개념 동일)* | `GL5`=15모듈(실제: **Global Lemma 5**), `SixFold`=0, `Metaplectic`=43모듈(2중 피복 $\mathrm{Mp}_{2n}$) | **전반부 미사용**: `GL1`~`GL6`은 $\mathrm{GL}_n$이 아니라 Global Lemma/Layer 버킷이며 `GL5`는 유니타리 Siegel–Weil 질량·부피 공식(`GenusMassVolumes`)이다. 6중 피복·$\mu$ 보형성은 전수 0건.<br>**후반부 완전 실재**: $U(p,q)$ 이산계열 부분공간 `HHX`로 사영된 Bessel Poincaré 급수 `Pu`와 그 프레임 연산자 $Q$의 **Cauchy–Schwarz/HS 상한**(`FrameLA1`, `TheoremF`, `TheoremSSelected`, `LinkS_at`)이 정확히 작동. | `Formalism.LocalToGlobal.GlobalTheory.GL5.Statement` :: `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.WeilSiegelCM`<br>`Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH` :: `Formalism.L2.SG.PoincareInHH.PoincareSetting.Pu`<br>`Formalism.HarderNarasimhan.StatementFrameF` :: `Formalism.HN.FrameLA1` / `Formalism.HN.TheoremF` |
| **⑦** | **Iwasawa 탑 & Bost 기울기 부등식** | **`[개념 동일·명칭만 변경]`** | `Bost`=3모듈(`...BoStatement` 오탐), `Iwasawa`=8,141모듈(중 7,769모듈은 $G=NAK$) | **양쪽 모두 완전 실재.** (a) Bost 기울기 부등식은 `Formalism.HN.SlopeIneq`·`SizeIneq`·`SlopeIneqMean`·`TheoremF`로 Arakelov 에르미트 격자에 그대로 구현됨. (b) $G=NAK$ 분해와 별개로, 실제 **최대실 $2$-거듭제곱 원분 탑 $\mathbb{Q}(\zeta_{2^{e+2}})^+$ (`OrdGrp s`, `IsChiField`)**, 이와사와 대수 $\Lambda=\mathbb{Z}_p[[X]]$, 그리고 **Ferrero–Washington 정리($\mu=0$)**가 핵심에 사용됨. | `Formalism.HarderNarasimhan.StatementPl` :: `Formalism.HN.SlopeIneqMean` / `Formalism.HN.SizeIneq`<br>`Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN` :: `UpperTheory.Top.IsChiField`<br>`Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.FerreroWashington` :: `UpperTheory.V.FW.ferreroWashington` |
| **⑧** | **Behrend 기반 탑 선택 기법** | **`[개념 동일·명칭만 변경]`** | `Behrend`=14모듈(독립 리프 섬) | **명칭·수학 모두 완전 일치.** `OrdGrp s` 위 일반화 Behrend 집합 `BehrendFree`, 하계 `BehrendBound`, 창 충돌 $\le 2$회(`WindowTwo`)·짧은 궤도 $\le 1$회(`OrbitOne`), 확률 분산 선택(`Select`), 프로베니우스 궤도 좌표 연결(`Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfM.coord`, `HostThickExists`, `Formalism.BasicNotions.Host`의 `T2`). | `Formalism.BehrendSets.Statement` :: `Formalism.BehrendSets.BehrendBound` / `WindowTwo` / `Select`<br>`Formalism.BehrendSets.TranslateMean` :: `Formalism.BehrendSets.Final.select`<br>`Formalism.FrobeniusOrbits.HostThickExists` :: `Formalism.FrobeniusOrbits.HostThickExists` |
| **⑨** | **약화된 Vandiver 추측 & Lichtenbaum 기반 $H^1$ 코호몰로지 제어** | **`[개념 동일·명칭만 변경]`** | `Vandiver`=0건, `Lichtenbaum`=0건 (**Round 1 최대 오독 해소!**) | **핵심 실재.** `Formalism.GaloisCohomology.Statement`의 `Sha D e` $= \Sha^1(\mathcal{O}_F[1/\ell], \mathbb{Q}_\ell/\mathbb{Z}_\ell(-e)) \subseteq H^1$, `VLen D e` $= \operatorname{len}_{\mathbb{Z}_\ell} H^2(\mathcal{O}_F[1/\ell], \mathbb{Z}_\ell(e+1))$, Poitou–Tate 쌍대 `VFormula`, 유군 비교 `shaLen_le_of_cl`, 창 가중 상계 `VVle`·`VWin`(접두사 `V`=Vandiver!)을 $U(3)$ 패칭·Kato 오일러계(`UpperTheory.V.HV.Core.of_four_alt`)로 증명하며 `SmallClassNumbers.{Bound, Large}`로 독립 따름정리까지 닫음. | `Formalism.GaloisCohomology.Statement` :: `Formalism.GaloisCohomology.shaLen` / `VLen` / `VFormula`<br>`Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN` :: `UpperTheory.Top.VVle` / `VWin`<br>`Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVCore` :: `UpperTheory.V.HV.Core.of_four_alt`<br>`Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.ClassNumberThree` :: `UpperTheory.V.SmallClassNumbers.Bound` |

**종합 집계**: 9개 개념 중 **`[개념 동일·명칭만 변경]` 6개**(②, ③, ④, ⑦, ⑧, ⑨), **`[구조 변형·우회]` 2개**(⑤, ⑥), **`[실제 코드에 미사용·대체됨]` 1개**(①). Round 1의 단순 키워드 탐색이 `0건`으로 오인했던 **Bost(⑦)**와 **약화된 Vandiver / Lichtenbaum $H^1$(⑨)**가 실제 타입 시그니처 대조 결과 **문자 그대로 핵심 정리에 구현되어 있음**을 확증했다.

---

## ① Stepanov 논증(중복도 모방) & $O(2,n)$ 보형적 행렬식(중복도 2)

- **최종 판정**: **`[실제 코드에 미사용·대체됨]`**

### 1. 키워드 함정과 부재 확증
DuckDB 전수 색인에서 `Stepanov`는 모듈·선언·시그니처 통틀어 **0건**이며, `Borcherds`·`SO2` 역시 $O(2,n)$ 보형 형식과 무관하다. 모듈명 `O2` 매칭은 대소문자 구분 시 **4모듈**(모두 아벨 스킴 구조층 코호몰로지 `HO2` = $H^2(\mathcal{O}_X)$를 다루는 `AbelianSchemeNoPrimitiveO2{,Statement}`·`SurjectivePullHO2OfPullHO1{,Statement}`), 대소문자 무시 시 `WeakShimuraTheory.FrobeniusFields.Two2` 포함 **5모듈**뿐이다. 별도로 `OrthogonalGroup` 5모듈(`WeilOrthogonalGroupInvariance{,Statement}`, `RowEmbeddingMemIntegralOrthogonalGroup{,Statement}`, `OrthogonalGroupLemmas`)을 확인해도, `CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilOrthogonalGroupInvarianceStatement`는 일반 이차형식 $g^\top B g = B$의 푸리에 변환 불변성이고 `Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowEmbeddingMemIntegralOrthogonalGroupStatement`는 실제로는 에르미트 공간 위 유니타리군 $U(J)$의 행렬 원소 소속 정리다. `Wronskian` 3개 모듈도 해석적 휘태커·아이젠슈타인 미분방정식 보조정리일 뿐 Stepanov 보조 다항식과 무관하다.

### 2. 실제 Lean 코드의 대체 메커니즘
유한체 위 고중복도 보조 다항식(Stepanov) 및 직교군 $O(2,n)$ 보형적 행렬식(중복도 2)이 담당하던 **"높은 소멸 차수/가분성으로 주항을 압도하여 소수 합의 상계를 강제하는 엔진"**은 실제 코드에서 다음 3단 구조로 완전히 대체되어 있다.

1. **군과 공간의 교체 — 직교군 $O(2,n)$ 대신 CM체 위 유니타리군 $U(X_j), U(Y_j), U(W_j)$**:  
   [DataSpaces.lean:77-140](../lean/src/Formalism/LocalRingCardinality/DataSpaces.lean#L77-L140)의 `Formalism.BasicNotions.Spaces`는 완전실체 $F$ 위의 2차 CM 확대 $E/F$ (`CMData F E`) 위에 에르미트 공간(`HSpace E`) 사슬을 구축한다. 정칙 에르미트 공간 $X_j$ (계수 $N(j) = k + j(t+1)$), 부정치 에르미트 공간 $Y_0$ (부호수 $(k+r_S, r_S+1)$, 여기서 $r=k+m-1$, $r_S=m/2-1$), 그리고 $W_j$ (계수 $r$, 부호수 $(k+j-1, m-j)$)가 모든 보형 사상의 무대다.
2. **행렬식 중복도 대신 Arakelov/Bost 앙상블 기울기 부등식**:  
   [Statement.lean:91-99](../lean/src/Formalism/HarderNarasimhan/Statement.lean#L91-L99)의 `Formalism.HN.SlopeIneq`, [StatementFrameF.lean:26-99](../lean/src/Formalism/HarderNarasimhan/StatementFrameF.lean#L26-L99)의 `Formalism.HN.TheoremF`·`Formalism.HN.TheoremFSharp`, 그리고 [MeanBoundSecondForm.lean:151-190](../lean/src/Formalism/RankGapBounds/MeanBoundSecondForm.lean#L151-L190)의 `Data.MeanBoundSecondForm`이 평가 사상(Bessel 주기 사상 `D.div.Bk u`)에 대해 단일 행렬식이 아닌 **에르미트 격자 기울기(공체적 로그)의 앙상블 평균 비교**를 수행한다.
3. **중복도 모방 대신 비분해 소수 거듭제곱 가분성 증폭(`LinkG_at`) + $p$-진 Jet(`ThetaJet`) + 쌍행렬식(`bidetSpan`)**:  
   - [GlobalTheoremInputs.lean:122-136](../lean/src/Formalism/SharpRestriction/GlobalTheoremInputs.lean#L122-L136)의 `Formalism.MainNotions.LinkG_at`는 비분해 소수(`InertK D p`, 즉 `signal` 또는 `inertClass`) 자리 $w$에서 격자 지수 이득 `L.gain j w - L.tau w`가 가중 von Mangoldt 잉여류 합을 하계하도록 강제한다:
     $$\sum_{j \in \mathrm{lifts}(D)} \sum_{t \in T_w} \bigl(\mathrm{vonMangoldtClassSum}(j,t,p) - \mathrm{loG}(p)\bigr) - m\cdot \mathrm{flG}(p) \;\le\; \sum_{j \in \mathrm{lifts}(D)} \mathrm{gain}(j,w) - \tau(w).$$
   - 국소 가분성 차수 계산은 [DataJet.lean:13-64](../lean/src/Formalism/LocalRingCardinality/DataJet.lean#L13-L64)의 $p$-진 형식멱급수 로그 `Formalism.BasicNotions.jetLogG` ($\sum_{e \ge 0} \ell^{-e} X_{(\nu-2e,\beta)}^{\ell^{2e}}$) 및 `Formalism.BasicNotions.ThetaJet`, 그리고 [StatementB.lean:15-69](../lean/src/Formalism/GradedWeylDivisibility/StatementB.lean#L15-L69)의 Fock 공간 쌍행렬식 `Formalism.GradedWeylDivisibility.bidetSpan`과 [FinalT.lean:11-14](../lean/src/Formalism/ThetaLogCoordinates/ResidueClassEstimates/FinalT.lean#L11-L14)의 Gelfand–Tsetlin/Weyl 차원 공식 `weylGT`가 담당한다.

---

## ② von Mangoldt 가중합 $\sum_{n \le X} \Lambda(n)(X/n - 1)_+ - X\log X + (1+\gamma)X$

- **최종 판정**: **`[개념 동일·명칭만 변경]`**

### 1. 실제 Lean 정의와의 1:1 대조
발표문에 제시된 1차 Riesz/Cesàro 가중 von Mangoldt 합은 **부호·상수·오일러-마스케로니 상수 $\gamma$까지 문자 그대로 동일하게** [StatementOC.lean:11-21](../lean/src/Formalism/StatementOC.lean#L11-L21)에 정의되어 있다:

```lean
def Sz (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1)
def Gz (x : ℝ) : ℝ := Sz x - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x
def Schi {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (χ n).re * (x / n - 1)
def Gchi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ) : ℝ :=
  Schi χ x + (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re * x
```

$1 \le n \le \lfloor x \rfloor$에서 $x/n - 1 \ge 0$이므로 `Sz x`는 정확히 $\sum_{n \le x} \Lambda(n)(x/n - 1)_+$이며, [WeightedVonMangoldtSumIdentity.lean:227-228](../lean/src/Formalism/GL3MeanSquares/HookFormulaTorsion/WeightedVonMangoldtSumIdentity.lean#L227-L228)의 `weighted_von_mangoldt_sum_identity`가 스케일 변수 $a, w > 0$에 대해 명시적 절단 형태와의 항등식을 증명한다:
$$w \sum_{n=1}^{\lfloor a/w \rfloor} \Lambda(n)\left(\frac{a/w}{n} - 1\right) \;=\; \sum_{n=1}^{M} \Lambda(n)\max\!\left(\frac{a}{n} - w,\, 0\right) \qquad (\lfloor a/w \rfloor \le M).$$

### 2. 순환 지표군 확장 및 승법 창 환원
일반 디리클레 지표 $\chi$에 대해서는 [Analytic.lean:14-24](../lean/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean#L14-L24)의 `Formalism.HC.An.G`, `Formalism.HC.An.gChi` 및 [ExplicitFormulaErrorOfHostConditions.lean:32-38](../lean/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean#L32-L38)의 `Formalism.HC.Level.Gm`이 순환 지표군 $\Lambda$ 위 가중합을 정의한다:
$$\Lambda.\mathrm{Gm}(y) \;=\; G_z(y) + \sum_{\psi \in \Lambda.\mathrm{Nt}} \Lambda.\mathrm{wt}(\psi)\,\operatorname{Re}\bigl(g_\psi(y)\bigr), \qquad \Lambda.\mathrm{wt}(\psi) \in \bigl\{1,\, (3\Lambda.o + 1)^{-1}\bigr\}.$$
이후 Pontryagin 쌍대 전개 [FirstPrimeNeSecondPrime.lean:98-101](../lean/src/Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean#L98-L101)의 `AskMainBalance` ($\mathrm{ASK} - \mathrm{MAIN} = \mathrm{De}$, 증명: [StronglyIrreducible.lean:695](../lean/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L695)의 `colour_balance`)와 [Window.lean:30-31](../lean/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Window.lean#L30-L31)의 Landau 진동 명제 `Formalism.HC.Level.FormBAt`, [TopWin.lean:68-69](../lean/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean#L68-L69)의 `Formalism.HC.level_of_tiedWin`이 무한히 많은 승법 창 $[Y, Y^\lambda]$ 위 상계 $\Lambda.\mathrm{Gm}(x) \le x^{1/2 + (e_D+e_L+7)\varepsilon}$로부터 `ZeroFreeAll` ($\operatorname{Re}(s)>1/2$ 영점 부재)을 도출한다.

---

## ③ 반복 세타 올림 $U(X_0) \to \dots \to U(X_m)$ ($m \sim \sqrt{X}$)

- **최종 판정**: **`[개념 동일·명칭만 변경]`**

### 1. 에르미트 공간열 $X_0,\dots,X_m$ 및 $m \sim \sqrt{X}$ 실증
[Params.lean:6-48](../lean/src/Formalism/LocalRingCardinality/Params.lean#L6-L48)의 `Formalism.BasicNotions.Ranks`와 [DataSpaces.lean:77-140](../lean/src/Formalism/LocalRingCardinality/DataSpaces.lean#L77-L140)의 `Formalism.BasicNotions.Spaces`는 $j = 0, 1, \dots, m$에 대해 정칙 에르미트 공간열 $X_j$ (계수 $N(j) = k + j(t+1)$, `X_def`) 및 보조 부정치 에르미트 공간열 $Y_j$ (계수 $r + jt$, $Y_m \cong X' \subset X_m$), $W_j$ (부호수 $(k+j-1, m-j)$)를 명시적으로 정의한다.

특히 사슬 길이 $m$의 점근 크기는 [SChain.lean:207-227](../lean/src/Formalism/SizeWindowBrackets/SChain.lean#L207-L227)의 `SizesTextAt`과 [GrowthBoundGivesRiemannHypothesis.lean:109-117](../lean/src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean#L109-L117)의 `SizeWindows`에 다음과 같이 고정되어 있다:
$$x^{1/2 - \varepsilon/16} \;\le\; m \;\le\; 2\,x^{1/2 - \varepsilon/16} \qquad \bigl(\text{일반 창: } x^{1/2 - \varepsilon} \le m \le x^{1/2 + \varepsilon/2}\bigr),$$
$$x^{2 + 8\varepsilon} \le n \le 2 x^{2+8\varepsilon}, \qquad b = e^{x^\varepsilon}, \qquad a = xb, \qquad k = x^{9/2 + 10\varepsilon}.$$
즉 발표문의 "$m \sim \sqrt{X}$ 단계의 반복 세타 올림 $U(X_0) \to \dots \to U(X_m)$"은 수치 지수까지 코드와 일치한다.

### 2. 두 계층의 반복 세타 사슬 구현
1. **이산 열(Column) 커널 사슬 (`ColumnChain`)**: [DataKernels.lean:14-76](../lean/src/Formalism/LocalRingCardinality/DataKernels.lean#L14-L76)의 `Formalism.BasicNotions.ColumnChain`과 [Statement.lean:52-67](../lean/src/Formalism/ThetaLiftIndependence/Statement.lean#L52-L67)의 `Formalism.ThetaLiftIndependence.chainOpM`은 각 단계 $i \in \{0,\dots,m-1\}$의 세타 커널 연산자 `Kmap i : (Y i → ℂ) →ₗ[ℂ] (Y (i+1) → ℂ)`를 안정화군 역가중치 `wt i c = |stab i c|⁻¹`로 합성하여 $m$회 반복 올림 `ColumnChain.col : (cls 0 → Y 0 → ℂ) → (cls m → Y m → ℂ)`을 정의한다. [DataRows.lean:92-100](../lean/src/Formalism/LocalRingCardinality/DataRows.lean#L92-L100)의 `Mult μ j`와 축소 사상 `io : Mult μ (j+1) →ₗ[ℂ] Mult μ j`가 그 쌍대 사슬이다.
2. **연속 아델 교대 세타 사슬 (`GlobalTheory.Unf.Chain`)**: [IsThetaFam.lean:149-206](../lean/src/Development/AbelianVarietyTheory/Definitions/LatticeFrames/IsThetaFam.lean#L149-L206)의 귀납 타입 `GlobalTheory.Unf.Chain ψ T ρ B`는 Bessel 층 `BesLev D (σ+1)`에서 `StepBF`로 Fourier–Jacobi 층 `JacLev D (σ+1)`로 이동하고, 다시 `StepFB`로 `BesLev D σ`로 내려가는 교대 세타 올림을 $\rho$회 반복하여 콤팩트 기저 에르미트 공간 $T$ (`Last`)까지 전개(`Chain.down`, `Chain.Q`, `Chain.Iter`)한다. 또한 `RowSrc` 측 갈루아 표현 구성에서도 [TLiftK.lean:12-24](../lean/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/HalfIndexLattices/TLiftK.lean#L12-L24)의 `UpperTheory.TP.TLiftK` (증명: [ThetaKernels/TLiftK.lean:4](../lean/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/TLiftK.lean#L4))가 정칙 유니타리군 간 세타 올림을 공급한다.

---

## ④ 시소 관계 & Rallis / Hecke 지표 무관 Bessel 주기

- **최종 판정**: **`[개념 동일·명칭만 변경]`**

### 1. 시소(Seesaw) 항등식과 Rallis 내적 공식
DuckDB 실측상 **시소(`Seesaw`) 452개 모듈**, **Rallis(`Rallis`) 91개 모듈**, **Siegel–Weil 1,834개 모듈**이 도달 가능 코어에 밀집해 있으며, 핵심 정리는 다음과 같이 직접 증명된다.
- **시소 Fubini & Rallis 내적 공식**: [RallisDM.lean:24-111](../lean/src/Development/AutomorphicArithmetic/ThetaCorrespondence/FockModels/RallisDM.lean#L24-L111)의 `UpperTheory.Lit.Rallis.RallisIPProof.rallis_of_dm`은 `seesaw_fubini`와 doubling 방법(`ResidueKilled.DM`) 및 수렴 구간 유니타리 Siegel–Weil(`GlobalTheory.Published.SiegelWeilUnitaryConvergent`)을 결합하여 Rallis 내적 공식 `GlobalTheory.Published.RallisInnerProductConvergent`를 증명한다:
  $$\operatorname{vol}([U(B)])^{-1}\,\langle \theta(\Phi_1, f_1),\, \theta(\Phi_2, f_2)\rangle_{U(B)} \;=\; Z_{\mathrm{dbl}}\!\bigl(s_0;\, \mathrm{swSec}(\delta(\Phi_1,\Phi_2)),\, f_1,\, f_2\bigr).$$
  구체적 바닥층 계산인 [BigThetaNormEqRallisInnerProduct.lean:19, 47](../lean/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/BigThetaNormEqRallisInnerProduct.lean#L19)의 `GlobalTheory.T.rallis_inner_product_big_theta_lift`는 국소 세타 입력 `GlobalTheory.FunPr.ThetaLocalInputs` 전제하에, 각 바닥 삼각형(`IsBottomTri`) 및 $t$마다 다항식 $P$, Haar 측도 $\nu$, 기본영역 $\mathcal{F}$, 비영 상수 $c \neq 0$이 **존재(`∃`)**하여 임의의 Hecke $L$-함수 $\Lambda$에 대해 큰 세타 올림의 $L^2$-노름 제곱이 $c \prod_{s=1-e_0}^{h_0} \Lambda(s)$와 같음을 증명한다. 시소 쌍 국소/대역 설정은 [SeesawIdentityConfigAFourthStatement.lean:12](../lean/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SeesawIdentityConfigAFourthStatement.lean#L12) (`GlobalTheory.T.seesaw_identity_config_a_fourth`) 등에 전개된다.
- **비등방 에르미트 Siegel–Weil**: [SiegelWeilAnisotropicHermitian.lean:12-41](../lean/src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/SiegelWeilAnisotropicHermitian.lean#L12-L41)의 `GlobalTheory.Published.SiegelWeilAnisotropicHermitian`은 $s_0 = (m-n)/2$에서 doubling Siegel Eisenstein 급수의 정칙값이 세타 적분 평균 $\bigl(\mathbf{1}_{n<m} + 2\cdot\mathbf{1}_{n\ge m}\bigr)\fint_{\mathcal{F}} \theta(\omega, \Phi; h, g)\,d\nu(h)$과 일치함을 정식화하며, [GL5/Statement.lean:31-67](../lean/src/Formalism/LocalToGlobal/GlobalTheory/GL5/Statement.lean#L31-L67)의 `WeilSiegelCM`, `MassRatioStd`, `VolRatioTrue`가 이를 유니타리 종족 질량·부피비로 연결한다.

### 2. Bessel 주기 중복도 1과 지표/격자 무관성
- **Bessel 사상 유일성(중복도 1)**: [BesselMapUniq.lean:50-59](../lean/src/Formalism/PeriodIntegrals/BesselMapUniq.lean#L50-L59)의 `PI.BesselMapUniq.BesselMapUniq`는 $U(p,q)$ 이산계열 $\sigma$에서 일반 Bessel 지표 $\psi_{\mathrm{gen}}$과 축소군 표현 $\pi$에 대해 연속 Bessel 범함수 공간이 최대 1차원임을 명세한다($\exists (a,b)\neq(0,0),\ a B_1 + b B_2 = 0$).
- **대역 Bessel 항등식 (`BesselId`)**: [GlobalTheoremInputs.lean:65-67](../lean/src/Formalism/SharpRestriction/GlobalTheoremInputs.lean#L65-L67)의 `Formalism.MainNotions.BesselId`는 대수적 주기 형식 `D.what₂.Bu u`가 0이 아닌 스칼라 $a \in \mathbb{C}^\times$와 유니타리 등거리 변환 $U, V$ 차이만으로 표준 Bessel 주기 `D.besS u`와 일치함을 보장한다:
  $$\forall \varphi, F,\qquad B_u(\varphi, F) \;=\; a \cdot \mathrm{besS}_u(U\varphi, VF).$$
- **격자·단어(지표) 무관성**: [GL3/Statement.lean:48-50, 74-77](../lean/src/Formalism/LocalToGlobal/GlobalTheory/GL3/Statement.lean#L48-L50)의 `ThetaNormIndependent`와 [GL3/PThIndep.lean:17](../lean/src/Formalism/LocalToGlobal/GlobalTheory/GL3/PThIndep.lean#L17)의 `theta_norm_indep_of_pair`는 허용 격자 선택에 대한 세타 노름의 불변성을 증명하고, [GlobalTheoremInputs.lean:87-89](../lean/src/Formalism/SharpRestriction/GlobalTheoremInputs.lean#L87-L89)의 `LinkDIV_at` 마지막 항은 서로 다른 단어(보조 소수 $T_u$ / 지표 패킷) $u, u'$에 대해 정규화된 평가사상 높이 $h(u) + (\sum_t a_t)\log T_u$가 오차 $C(|TT|a\Lambda_a + m B_0)$ 이내에서 **단어 $u$에 무관하게 고정**됨을 보장한다.

---

## ⑤ $2/3$ 장벽 돌파 (Hecke 지표 평균화 & 상대 추적 공식 반평면 논증)

- **최종 판정**: **`[구조 변형·우회]`**

### 1. 키워드 검증과 부재 요소
코드베이스 전수 검색에서 `TwoThird`·`Kuznetsov`·`Subconvex`는 **0건**이며, `RelativeTrace` 2개 모듈(`ExistsIntegerOfRelativeTraceNormIntegral{,Statement}`)은 이차체 원소의 대각합(trace) 보조정리다. `2 / 3` 리터럴 출현 역시 국소 $L'/L$ 영점합 반지름 `‖s - (3/2 + it)‖ ≤ 2/3` ([LogDerivDirichletLFunctionLocalZeroSum.lean:17](../lean/src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivDirichletLFunctionLocalZeroSum.lean#L17)) 또는 `threshold_arith_w_case` ([ThresholdPowerBoundOfCounts.lean:16](../lean/src/Formalism/SharpRestriction/GrowthBounds/SegmentDegree/ThresholdPowerBoundOfCounts.lean#L16))의 선형 부등식 상수일 뿐, 전통적 해석적 정수론의 $2/3$-장벽 상대추적공식(RTF)이나 반평면 해석접속 논증은 그대로 사용되지 않는다.

### 2. 실제 코드가 $X^{1/2+\varepsilon}$ 장벽을 돌파하는 변형·우회 구조
발표문이 "Hecke 지표 평균화 + 상대 추적 공식 반평면 논증으로 $2/3$ 장벽을 돌파"라고 서술한 기능은 실제 Lean 코드에서 다음 **3중 결합**으로 재설계되어 있다.

1. **$m \sim \sqrt{x}$ 세타 사슬 균형 (`SizeWindows` → `GrowthSizeBound`)**:  
   [GrowthBoundGivesRiemannHypothesis.lean:109-122](../lean/src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean#L109-L122)의 `SizeWindows`와 `GrowthSizeBound` (증명: [LipschitzWeightAndMinimum.lean:507](../lean/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean#L507)의 `proposition_size_bound`)에서 핵심 부등식은
   $$n_T m b \cdot \frac{n_{T_2}}{2n}\bigl(G_x - 4x^{1/2+\varepsilon}\bigr) \;\le\; \mathrm{Err} + \frac{2 n_T m b}{x},$$
   $$\mathrm{Err} \;\le\; x^{C\varepsilon}\left(n_T a_E\Bigl(1+\frac{m^2}{k}\Bigr) + m\Bigl(2nmb x^\varepsilon + \frac{n_{T_2} k b x^\varepsilon}{n^2 x^{-\varepsilon}}\Bigr)\right).$$
   양변을 좌변 계수 $\asymp n m b x^{-\varepsilon}$로 나누면 세 오차항은 각각 $a_E/(mb) \asymp \mathbf{x/m}$, $\mathbf{m}$, 그리고 $\mathbf{k/n^2} \le x^{1/2-\varepsilon}$가 된다. 즉 $m=1$이면 자명 상계 $x$, 중간 균형 실패 시 $x^{2/3}$급 장벽에 걸리지만, **$m \asymp x^{1/2}$와 $k \le n^2 x^{1/2-\varepsilon}$의 동시 선택**으로 세 항이 모두 $\mathbf{x^{1/2 + O(\varepsilon)}}$에서 정확히 균형을 이룬다.
2. **앙상블 평균화 및 이차 지표 평균제곱 (`topExcess`, `MeanBoundSecondForm`, `QH.meanSqK`)**:  
   - [GrowthBoundGivesRiemannHypothesis.lean:50-53](../lean/src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean#L50-L53)의 `topExcess`와 [MeanBoundSecondForm.lean:92-190](../lean/src/Formalism/RankGapBounds/MeanBoundSecondForm.lean#L92-L190)은 단일 객체 대신 **Behrend 평행이동 $u_0 \in H$에 대한 균일 평균(`umean`)**과 **단어/지표 패킷 $u \in W(u_0)$에 대한 가중 평균(`wmean`)**을 취해 국소 편차를 소거한다.
   - 보조 소수쌍 $(q,d)$ 선택과 얇은 스케일(`ThinScales`, `ValuesAtX`) 통제에서는 [MeanSqAbs.lean:8-14](../lean/src/Development/AutomorphicArithmetic/MeanSquareBounds/MeanSqAbs.lean#L8-L14)의 `QH.meanSq_abs` 및 [meanSqK.lean:51-54](../lean/src/Development/AutomorphicArithmetic/MeanSquareBounds/meanSqK.lean#L51-L54)의 `QH.meanSqK`가 이차 야코비 지표 합의 평균제곱 상계를 증명한다.
3. **RTF 대신 $U(p,q)$ Bessel Poincaré 급수의 이중 잉여류 전개 & 이산계열 감쇠**:  
   상대 추적 공식 대신 부정치 유니타리군 $U(p,q)$ 위 Bessel Poincaré 급수(`Formalism.L2.SG.PoincareInHH.PoincareSetting.Pser`)의 내적/그람 연산자(`hsDiagFull`, `hsSq`)를 이중 잉여류(`FoldBound`, `BruhatCellsKronecker`)로 전개하고, [WuDecayAll.lean:25, 1058](../lean/src/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/WuDecayAll.lean#L25)의 `WuDecayOfGap` (아키메데스 이산계열 행렬계수의 가중 $L^1$ 감쇠)로 비대각항을 지수적으로 억제(`LinkS_at`: $\eta_0, \eta_1, \sqrt{e_0} \le e^{-x^{\varepsilon/8}}$)한다. 반평면 해석접속은 `SiegelEisensteinHalfPlane` (`SiegelWeilAnisotropicHermitian`: $\operatorname{Re}(s) > n/2$)에서 Siegel–Weil 공식 증명에 쓰인다.

---

## ⑥ $\mathrm{GL}_5$ 6중 피복 위 $\mu$ 보형성 & 사영된 Poincaré 급수의 Cauchy–Schwarz 상한

- **최종 판정**: **`[구조 변형·우회]`** *(전반부 "$\mathrm{GL}_5$ 6중 피복 위 $\mu$ 보형성" = **`[실제 코드에 미사용·대체됨]`**, 후반부 "사영된 Poincaré 급수의 Cauchy–Schwarz 상한" = **`[개념 동일·명칭만 변경]`**)*

### 1. 전반부 — `GL5` 오독의 완전 해소 및 6중 피복 부재 확증
코드베이스에서 `GL5`를 검색하면 정확히 15개 모듈(`Formalism.LocalToGlobal.GlobalTheory.GL5.*`)이 나타난다. 그러나 상위 디렉토리 `Formalism.LocalToGlobal.GlobalTheory.*`를 조사하면 **`GL1`(11모듈), `GL2`(3), `GL3`(67), `GL4`(70), `GL5`(15), `GL6`(72)**가 병렬로 존재하며, 이는 $\mathrm{GL}_1,\dots,\mathrm{GL}_6$ 리 군이 아니라 **"Global Lemma / Layer 1~6"**의 약어이다:
- `GL1`: 아델 격자 연결(`AdelicLatticeLinkFamily`)
- `GL2`: 보조 소수쌍 $(q, d)$, $(g_1, g_2)$, $T$ 선택(`QDGood`, `GPair`, `TGood`)
- `GL3`: `IntegralLatticeDensity` — Kronecker 극한 공식·CM 타원곡선·세타 노름 불변성(`ThetaNormIndependent`)
- `GL4`: `TraceIntegrality` — Minkowski 유한부분군, Banaszczyk 전이 부등식(`Transference`), `KudlaFamilyOfMinkowskiTransference`
- **`GL5`**: `GenusMassVolumes` — **유니타리 Siegel–Weil 종족 질량비·부피 공식**(`WeilSiegelCM`, `MassRatioStd`, `VolRatioTrue`, `HCFormalDegree`, `LandherrHasse`, `GenusMassStd`, `packet_statement_of_independence`)
- `GL6`: `LocalLatticeBases` — 국소 격자 기저·프로베니우스 연산자 관계(`FrobeniusOperatorRelations`)

나아가 전체 1,061,425개 선언을 전수 검색한 결과:
- `SixFold`·`Sextic`·`Kazhdan`–`Patterson`·`Kubota` 피복은 **0건**이다.
- `Metaplectic` 43개 모듈은 예외 없이 세타 대응의 Weil 표현을 위한 **표준 2중 메타플렉틱 피복 $\mathrm{Mp}_{2n}$** (`RealMetaplecticRepresentation`, `MetaplecticCoverWeilRepresentation`)이다.
- `GL (Fin 5)`가 등장하는 유일한 수학적 선언은 `SymmetricPowerTransfer` 내부의 $\mathrm{Sym}^4 : \mathrm{GL}_2 \to \mathrm{GL}_5$ (`SymmetricFourthPowerMatrix.lean:23`)로서, $U(3)$ 모듈러리티(`VWin`) 경로에 쓰이는 4차 대칭거듭제곱일 뿐 6중 피복 위 $\mu$ 보형성과 무관하다. (또한 `TheoremsMuLinked` 176개 모듈은 $U(3)$ 패칭의 3차원 갈루아 표현 연결용이다.)
- 선언 레벨에서 `GL5` 이름이 붙은 2건(`GL5LogLValueBoundByZeta`, [AuxiliaryNormPrimes.lean:46](../lean/src/Formalism/SharpRestriction/CuspSpanNormBounds/AuxiliaryNormPrimes.lean#L46) 및 [LocalBesselAndTopKernel.lean:522](../lean/src/Formalism/SharpRestriction/CuspSpanNormBounds/LocalBesselAndTopKernel.lean#L522)) 역시 $\forall i \ge 3,\ |\log(\mathrm{lValEta}\ E\ i)| \le f \cdot \log\operatorname{Re}\zeta(i)$라는 **Global Lemma 5(유니타리 질량비의 제타 $L$-값 상계)** 명제임이 직접 확인되어 선언 수준에서도 $\mathrm{GL}_5$ 6중 피복은 사각지대 0건이다.

### 2. 후반부 — 사영된 Poincaré 급수 & Cauchy–Schwarz/HS 상한의 완벽한 실재
반면 발표문 후반부의 **"사영된 Poincaré 급수의 Cauchy–Schwarz 상한"**은 $\mathrm{GL}_5$ 피복 대신 **부정치 유니타리군 $U(p,q)$** 위에서 문자 그대로 핵심 정리로 구현되어 있다:
1. **이산계열 공간으로 사영된 Bessel Poincaré 급수 (`PoincareInHH`)**:  
   [PoincareInHH.lean:179-219](../lean/src/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/PoincareInHH.lean#L179-L219)는 $U(p,q)(\mathbb{A})$ 위 Bessel Poincaré 급수 `Pser`를 정의하고, `InHH` 조건하에 이산계열/첨점 직교 사영 `X.B.Re (X.Rph _)`의 상 `HHX X`로 보내는 선형사상 `PoincareSetting.Pu : Cu X u hK →ₗ[ℂ] HHX X`를 구성한다.
2. **힐베르트-슈미트(HS) 준직교성 (`TheoremSSelected` / `LinkS_at`)**:  
   [ThmSOwn.lean:669-675, 923-940](../lean/src/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/ThmSOwn.lean#L669-L675)의 `Formalism.L2.SG.ThmSOwn.TheoremSSelected`·`linkS_selH`가 [GlobalTheoremInputs.lean:145-156](../lean/src/Formalism/SharpRestriction/GlobalTheoremInputs.lean#L145-L156)의 `LinkS_at`을 증명한다:
   $$\forall u \neq u',\quad \mathrm{hsSq}(u, u') \;\le\; (1+\eta_0)\frac{d_u d_{u'}}{D_*}, \qquad \forall u,\quad \|K_{u,u} - \mathrm{Id}\|_{\mathrm{HS}}^2 \;\le\; e_0 d_u, \qquad \eta_0,\eta_1,\sqrt{e_0} \le e^{-x^{\varepsilon/8}}.$$
3. **프레임 연산자에 대한 Cauchy–Schwarz 부등식 (`FrameLA1` → `TheoremF`/`TheoremFSharp`)**:  
   [StatementFrameF.lean:11-24, 51-62](../lean/src/Formalism/HarderNarasimhan/StatementFrameF.lean#L11-L24)의 `Formalism.HN.FrameLA1`과 `Formalism.HN.TheoremF` (증명: [ShiftInvariance.lean:60-61](../lean/src/Formalism/HarderNarasimhan/ShiftInvariance.lean#L60-L61)의 `theoremF`, `theoremFSharp`)는 사영된 사상족 $B_i : V_i \to H$의 프레임 연산자 $Q = \sum_i \gamma_i B_i B_i^*$가 **Cauchy–Schwarz 근사 등호 조건**
   $$\operatorname{Re}\operatorname{tr}(Q^2) \;\le\; (1+\eta)\,\frac{(\operatorname{Re}\operatorname{tr} Q)^2}{\dim_{\mathbb{C}} H}, \qquad \sum_i \|\gamma_i B_i^* B_i - \mathrm{Id}\|_{\mathrm{HS}}^2 \;\le\; e \sum_i \dim_{\mathbb{C}} V_i$$
   을 만족하면 부분공간의 여차원이 $(\eta + 4\varepsilon + 4\sqrt{e})\dim H$로 억제됨을 증명하여, 이것이 곧장 앙상블 Bost 기울기 부등식(`Formalism.RankGapBounds.WeightedMeanData.Data.SlopeIneq`)으로 흘러 들어간다.

---

## ⑦ Iwasawa 탑 & Bost 기울기 부등식

- **최종 판정**: **`[개념 동일·명칭만 변경]`**

### 1. Bost 기울기 부등식 — 문자열 0건 함정과 100% 수학적 일치
DuckDB에서 `Bost` 문자열을 검색하면 3개 모듈이 나오지만 모두 `...BoStatement`의 부분문자열 오탐이다. 그러나 실제 Arakelov 격자 부등식 모듈 [Statement.lean:91-99](../lean/src/Formalism/HarderNarasimhan/Statement.lean#L91-L99)과 [StatementPl.lean:60-72, 121-159](../lean/src/Formalism/HarderNarasimhan/StatementPl.lean#L121-L159) (증명 일괄 수출: [ShiftInvariance.lean:43, 54, 57, 60-61](../lean/src/Formalism/HarderNarasimhan/ShiftInvariance.lean#L43-L61))을 열람하면 **Jean-Benoît Bost의 에르미트 벡터다발/Arakelov 격자 기울기 부등식**이 `Formalism.HN` 네임스페이스 아래에 3가지 등가·확장 형태로 완벽히 형식화되어 있다:

- **추상 유클리드 격자형 (`Formalism.HN.SlopeIneq`, `Statement.lean:91`)**:
  $$\forall \varphi : L \to_{\mathcal{R}} M,\;\; \forall x \in L,\ \|\rho'(\varphi x)\| \le C\|\rho x\| \;\Longrightarrow\; \bigl(\varphi \neq 0 \Rightarrow \mu_{\min}(L) \le \mu_{\max}(M) + \log C\bigr) \;\wedge\; \bigl(\varphi\text{ 단사} \Rightarrow \mu_{\max}(L) \le \mu_{\max}(M) + \log C\bigr).$$
- **완전복소 수체 $K$ 위 Arakelov 기울기형 (`Formalism.HN.SlopeIneqMean`, `StatementPl.lean:148`)**:  
  사상 높이 $h(\varphi) := \mathrm{htMap}(\varphi) = \frac{1}{n_{\mathrm{pl}}(K)}\sum_{v \mid \infty} \log(\|\varphi\|_v^2)$와 정규화 기울기 $\hat{\mu}(L) := \mathrm{muDef}(L) = 2\mu(L) - \log 2 + \frac{\log |D_K|}{[K:\mathbb{Q}]}$에 대해, $\varphi(A) \subseteq B$, $\varphi(A) \neq 0$이면
  $$\hat{\mu}_{\min}(A) - h(\varphi) \;\le\; \hat{\mu}_{\min}(\varphi(A)), \qquad \hat{\mu}_{\min}(A) \;\le\; \hat{\mu}_{\max}(B) + h(\varphi).$$
- **곱셈적 크기 비율형 (`Formalism.HN.SizeIneq`, `StatementPl.lean:121`)**:
  $$\frac{\mathrm{leastSize}(B)}{\mathrm{largestSize}(A)} \;\le\; \left(\prod_{v \mid \infty} \|\varphi\|_v\right)^{1 / n_{\mathrm{pl}}(K)}.$$
- **프레임 앙상블 확장 (`Formalism.HN.TheoremF` / `TheoremFSharp`, `StatementFrameF.lean:26, 64`)**: 단일 사상 대신 사상족 $\{B_i : N_i \to \mathrm{cc}\}_{i \in I}$의 가중 평균 기울기 $s$와 $\hat{\mu}(\mathrm{cc})$를 연결하는 앙상블 Bost 기울기 부등식.

### 2. Iwasawa 분별 — $G=NAK$ 분해(7,769모듈) vs 실제 원분 Iwasawa 탑 및 Ferrero–Washington
- **거대 키워드 분리**: 전체 `Iwasawa` 매칭 8,141모듈(640,819줄) 중 **7,769모듈(600,348줄, 93.7%)**은 `Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.*`로서 리 군·아델 군의 **이와사와 분해($G = NAK$)**이다.
- **실제 정수론적 Iwasawa 탑**: 증명 척추를 지탱하는 수체 탑은 **최대실 $2$-거듭제곱 원분 $\mathbb{Z}_2$-확대 탑**이다:
  - 갈루아 군: [BehrendSets/Statement.lean:9-15](../lean/src/Formalism/BehrendSets/Statement.lean#L9-L15)의 `OrdGrp s := (ZMod (2 ^ (s + 2)))ˣ ⧸ ⟨-1⟩` ($\cong \mathbb{Z}/2^s\mathbb{Z}$, 즉 $\operatorname{Gal}(\mathbb{Q}(\zeta_{2^{s+2}})^+/\mathbb{Q})$).
  - 탑의 수체 층: [ExistsPageN.lean:19-25, 39](../lean/src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean#L19-L25)의 `IsChiField ψ e q d E` (최대실 $2$-원분체 $\mathbb{Q}(\zeta_{2^{e+2}})^+$와 $\ker\psi$ 및 이차체 $\mathbb{Q}(\sqrt{-q}), \mathbb{Q}(\sqrt{-d})$의 합성체, $2^e \asymp x^{2+8\varepsilon}$).
  - 이와사와 대수 및 $\mu=0$ 정리: [SpanFinrankMaximalIdealLeTwo.lean:13, 55](../lean/src/GroundTheory/ArithmeticGeometry/IwasawaModules/SpanFinrankMaximalIdealLeTwo.lean#L13-L55)의 `GroundTheory.Arith.Iwasawa.Lambda p := PowerSeries ℤ_[p]` ($\dim_{\mathrm{Krull}}\Lambda = 2$)와, 특히 [FerreroWashington.lean:7-11](../lean/src/Development/AutomorphicArithmetic/AutomorphicVarieties/PublishedTheorems/FerreroWashington.lean#L7-L11)의 **Ferrero–Washington 정리** (`UpperTheory.V.Published.FerreroWashington`, 증명: `UpperTheory.V.FW.ferreroWashington`, [HVCore.lean:19](../lean/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/HVCore.lean#L19)에서 직접 호출!)가 원분 $\mathbb{Z}_\ell$-탑 유군 $p$-랭크 균일 유계성을 공급한다.

---

## ⑧ Behrend 기반 탑 선택 기법

- **최종 판정**: **`[개념 동일·명칭만 변경]`** *(명칭과 내용 모두 완전 일치)*

### 1. 핵심 정의와 정리 (`Formalism.BehrendSets.*` 14모듈 + `HostThickExists`)
`Formalism.BehrendSets`는 Mathlib만 직접 의존하는 14모듈(1,074줄) 독립 리프 섬이며, [Statement.lean:9-126](../lean/src/Formalism/BehrendSets/Statement.lean#L9-L126)에 다음 핵심 조합·확률 구조가 정의되어 있다:

1. **일반화 Behrend 자유 집합 (`BehrendFree`, L48–52)**:
   $$\forall \alpha,\beta,\gamma \in \mathbb{Z}\setminus\{0\},\ \alpha+\beta+\gamma=0,\ |\alpha|,|\beta|,|\gamma|\le K \;\Longrightarrow\; \bigl(\alpha x_1+\beta x_2+\gamma x_3 = 0,\ x_i \in T \;\Rightarrow\; x_1=x_2=x_3\bigr).$$
2. **Behrend 밀도 하계 (`BehrendBound`, L54–56; `ThickSet`, L58–61)**:
   $$\exists C > 0,\ \forall K, N \ge 1,\ \exists T \subseteq \{0,\dots,N-1\},\ \mathrm{BehrendFree}(K, T) \;\wedge\; |T| \;\ge\; N \exp\!\Bigl(-C\sqrt{\log N\cdot \log(K+1)}\Bigr).$$
   이는 [HostThickExists.lean:13-32](../lean/src/Formalism/FrobeniusOrbits/HostThickExists.lean#L13-L32)의 `NoRel`·`HostThickExists` (증명: `Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ThickExists` :: `hostThickExists`)로 호스트 탑 파라미터에 연결되어 `n_{T_2}/n ≥ x^{-ε}` (`SizeWindows`, `GrowthBoundGivesRiemannHypothesis.lean:112`)를 보장한다.
3. **프로베니우스 궤도 충돌 억제 (`WindowTwo`, L67–70; `OrbitOne`, L72–75)**:  
   $n \ge 1$ (`[NeZero n]`), $L \in \mathbb{N}$과 `thick n T u := {t + u mod n | t ∈ T}`에 대해:
   - `WindowTwo`는 $\forall t \in T,\ 8Lt < n$과 `BehrendFree (2L) T` 가정하에 긴 궤도($\operatorname{ord}(h) > 2L$)가 길이 $2L$인 임의의 연속 창에서 `thick n T u`와 **최대 2회**만 교차함을 보장한다.
   - `OrbitOne`은 `BehrendFree` 가정 없이 오직 $\forall t \in T,\ 8Lt < n$만으로 짧은 궤도($\operatorname{ord}(h) \le 8L$)가 `thick n T u`와 전체 궤도에서 **최대 1개 원소**에서만 만남을 보장한다.
4. **베르누이 분산 선택 (`Select`, L105–107; 증명: `Formalism.BehrendSets.Final.select`, [TranslateMean.lean:11](../lean/src/Formalism/BehrendSets/TranslateMean.lean#L11))**:  
   $2|X|\delta(1-\delta) < \lambda^2$일 때 $\exists T \subseteq X$ such that $\bigl||T| - \delta|X|\bigr| \le \lambda$ 이면서 동시에 나쁜 궤도 카운트 $Y(T) \le 2\mathbb{E}_\delta[Y]$를 만족하는 부분집합을 추출한다.
5. **탑 프로베니우스 궤도 주입**: [DifferenceStableUnderAction.lean:111-115](../lean/src/Formalism/GL3MeanSquares/HookFormulaTorsion/DifferenceStableUnderAction.lean#L111-L115)의 `Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfM.coord`가 $\operatorname{Gal}(E/\mathbb{Q})$의 프로베니우스 작용 $\varphi^i \tau$를 `ZMod (2^e)` 위 선형 궤도 $\iota(\tau) + i\cdot\iota(\varphi)$로 변환하고, [DataHost.lean:102-107](../lean/src/Formalism/LocalRingCardinality/DataHost.lean#L102-L107)의 `Formalism.BasicNotions.Host` 필드 `T2` (`second_set_no_relation : NoRel T2 Lw`)가 이를 모든 호스트 데이터 `D7`에 내장한다.

---

## ⑨ 약화된 Vandiver 추측 & Lichtenbaum 기반 $H^1$ 코호몰로지 제어

- **최종 판정**: **`[개념 동일·명칭만 변경]`** *(Round 1의 "키워드 0건" 오독을 완전히 뒤집는 본 로제타 스톤의 핵심 발견)*

### 1. 키워드 함정 해부 — `V`는 곧 **Vandiver**이며 `Sha`/`VLen`/`VFormula`는 곧 **Lichtenbaum $H^1$/$H^2$**다!
코드베이스에서 문자열 `Vandiver`·`Lichtenbaum`은 **0건**이다. 그러나 `UpperTheory.Top.VWin`, `VVle`, `HypV`, `UpperTheory.V.*`의 실제 정의를 [GaloisCohomology/Statement.lean:13-142](../lean/src/Formalism/GaloisCohomology/Statement.lean#L13-L142)까지 추적하면 다음과 같은 **정확한 에탈/갈루아 코호몰로지 실체**가 드러난다:

- **계수 모듈**: `QZ l := ℚ_[l] ⧸ ZlSub l` $= \mathbb{Q}_\ell / \mathbb{Z}_\ell$ (이산 위상 $\mathbb{Z}_\ell$-가군).
- **갈루아 군과 분기 자리**: `D.S = Above F l` ($\ell$ 위의 소아이디얼 집합 $S_\ell$), `GS Ω D.S` $= G_{F, S_\ell} = \pi_1(\operatorname{Spec}\mathcal{O}_F[1/\ell])$.
- **원분 꼬임 표현 (`qzTw`, `zlTw`, L67–73)**:
  $$\mathrm{qzTw}(D, e) \;=\; (\mathbb{Q}_\ell/\mathbb{Z}_\ell)(-e), \qquad \mathrm{zlTw}(D, e+1) \;=\; \mathbb{Z}_\ell(e+1).$$
- **$H^1$ 테이트-샤파레비치 군과 길이 (`Sha`, `shaLen`, L75–78)**:
  $$\mathrm{Sha}(D, e) \;:=\; \Sha^1\!\bigl(G_{F, S_\ell},\, (\mathbb{Q}_\ell/\mathbb{Z}_\ell)(-e)\bigr) \;\subseteq\; H^1\!\bigl(\mathcal{O}_F[1/\ell],\, \mathbb{Q}_\ell/\mathbb{Z}_\ell(-e)\bigr), \qquad \mathrm{shaLen}(D, e) \;=\; \operatorname{length}_{\mathbb{Z}_\ell}\bigl(\mathrm{Sha}(D, e)\bigr).$$
- **Lichtenbaum $H^2$ 길이 (`VLen`, L80) 및 Poitou–Tate 쌍대 공식 (`VFormula`, L138–141; 증명: [VFormula.lean:16](../lean/src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/GaloisCohomologyLength/VFormula.lean#L16)의 `UpperTheory.V.LDataCardLeFinrank.vFormula`)**:
  $$\mathrm{VLen}(D, e) \;=\; \operatorname{length}_{\mathbb{Z}_\ell}\, H^2\!\bigl(G_{F, S_\ell},\, \mathbb{Z}_\ell(e+1)\bigr),$$
  $$\mathrm{VLen}(D, e) + \operatorname{length}_{\mathbb{Z}_\ell} H^0\bigl((\mathbb{Q}_\ell/\mathbb{Z}_\ell)(-e)\bigr) \;=\; \mathrm{shaLen}(D, e) + \sum_{v \mid \ell} \operatorname{length}_{\mathbb{Z}_\ell} H^0\bigl(G_{F_v},\, (\mathbb{Q}_\ell/\mathbb{Z}_\ell)(-e)\bigr).$$
  Lichtenbaum/Quillen–Lichtenbaum 추측의 프레임워크에서 $K_{2e}(\mathcal{O}_F) \otimes \mathbb{Z}_\ell \cong H^2(\mathcal{O}_F[1/\ell], \mathbb{Z}_\ell(e+1))$ (Vandiver 추측의 고차 $K$-이론·에탈 코호몰로지 확장)이며, Kummer 이론 연결 정리인 [MinusLenLeOfCl.lean:129-136](../lean/src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/KummerTheory/MinusLenLeOfCl.lean#L129-L136)의 `shaLen_le_of_cl`은 `shaLen D e`를 원분체 $\mathbb{Q}(\zeta_{\ell^n})$ 유군의 등변 부분 `ClEq` 길이로 직접 상계한다!

### 2. 약화된 Vandiver 창 상계 (`VVle` / `VWin`)와 $U(3)$ 패칭 증명
1. **창 가중 상계 (`VVle`, `VWin`)**: [ExistsPageN.lean:12-49](../lean/src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean#L12-L49)는 모든 원시 지표 $\psi$와 원분 합성체 $E$ (`IsChiField ψ (e x) q d E`)에 대해 다음 약화된 Vandiver 창 상계를 요구한다:
   $$\mathrm{VVle}(E, t, B) \;:\Longleftrightarrow\; \Bigl(\forall p \text{ prime},\ \forall e,\ 0 < e < t \Rightarrow \mathrm{shaLen}(E, p, e) \neq \top\Bigr) \;\wedge\; \Bigl(\forall S \subset_{\mathrm{fin}} \mathbb{P},\ \sum_{\ell \in S} \log \ell \sum_{1 \le e < t} \mathrm{shaLen}(E, \ell, e).\mathrm{toNat} \;\le\; B\Bigr),$$
   $$\mathrm{VWin} \;:=\; \forall \psi,\;\mathrm{VWinAt}\;\psi\;401 \qquad \bigl(t = \lfloor x^{401} \rfloor,\; B = \sqrt{e^{x^\varepsilon}}\bigr).$$
   *(참고: Lean `ℕ∞`에서 `ENat.toNat ⊤ = 0`이므로 첫 번째 유한성 연언절 `shaLen ≠ ⊤`는 무한 길이가 합에서 0으로 소거되는 것을 막는 필수 조건이다.)*
2. **$U(3)$ 패칭 + Kato 오일러계 + Ferrero–Washington으로의 증명**: [HVCore.lean:18-22](../lean/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/HVCore.lean#L18-L22)의 `UpperTheory.V.HV.Core.of_four_alt`는 `LiteratureRankNHypothesis` + `LemmaK` + `FW.ferreroWashington` + 4대 카운팅 정리 `CountI`·`CountII`·`CountIII`·`CountV` ([Counts.lean:53-70](../lean/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/Counts.lean#L53-L70))로부터 `VWin`을 닫는다. 특히 핵심 사례 `CountI`는 [KatoUse.lean:13-65](../lean/src/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/KatoUse.lean#L13-L65)의 `KatoUse`(Bloch–Kato Selmer 소멸), `OneChar`(3차원 갈루아 표현 $\rho : G_K \to \mathrm{GL}_3(\overline{\mathbb{Q}}_\ell)$로의 대각합 합동 상계), `PropGK`·`CorGK`, 그리고 `PatchingModules`·`GreenbergWiles`·`WachLatticeTwists`로 증명된다.
3. **주축 주입 및 독립 따름정리 (`SmallClassNumbers`)**: [DivinNOfHypV.lean:117-130](../lean/src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean#L117-L130)의 `UpperTheory.Top.divinN_of_hypV`가 `HypV` + `LinkN` + `SmallLevelRankEq`에서 `DIVinN`을 뽑아 비분해 소수 가분성 오차 `etaSum`을 닫는다. 별도로 [ClassNumberThree.lean:16-20](../lean/src/Development/AutomorphicArithmetic/AutomorphicVarieties/SmallClassNumbers/ClassNumberThree.lean#L16-L20), [CorGKOf.lean:25-27](../lean/src/Development/AutomorphicArithmetic/AutomorphicVarieties/SmallClassNumbers/CorGKOf.lean#L25-L27), [LenEqZeroIff.lean:65-84](../lean/src/Development/AutomorphicArithmetic/AutomorphicVarieties/SmallClassNumbers/LenEqZeroIff.lean#L65-L84)은 $\mathbb{Q}(\sqrt{-3})$의 유수 1(`classNumber_three`)과 `corGK`로부터 $\mathbb{Q}$ 위 약화된 Vandiver 따름정리 `Bound` ($\exists C, A \in \mathbb{N}$, 모든 짝수 $e \ge 1$과 소수 집합 $L_s$ [$\forall \ell \in L_s,\ \ell \ge 5 \wedge (\ell-1) \nmid 2e$]에 대해 $\forall \ell \in L_s,\ \mathrm{len} \neq \top$ 및 $\sum_{\ell \in L_s} \log\ell \cdot (\mathrm{len}.\mathrm{toNat}/e_{\mathcal{O}}.\mathrm{toNat}) \le C(e+1)^A$)와 대형 소수 소멸 `Large` (위 조건에 $e_{\mathcal{O}}(\ell, (c\ \ell).O) = 1$ 및 $\log \ell > C(e+1)^A$가 추가되면 $\mathrm{Vanish}\ \Omega\ \ell\ (c\ \ell)\ e$)을 무조건 증명한다.

---

## 부록: 검증된 핵심 앵커 색인표

| 개념 | Lean 모듈 (`Module`) | 선언명 (`declName`) | 상대 경로 (`.lean`) | 줄 |
| :-: | :--- | :--- | :--- | ---: |
| ① | `Formalism.LocalRingCardinality.DataSpaces` | `Formalism.BasicNotions.Spaces` | `Formalism/LocalRingCardinality/DataSpaces.lean` | 77 |
| ① | `Formalism.LocalRingCardinality.DataJet` | `Formalism.BasicNotions.jetLogG` / `ThetaJet` | `Formalism/LocalRingCardinality/DataJet.lean` | 13, 48 |
| ① | `Formalism.GradedWeylDivisibility.StatementB` | `Formalism.GradedWeylDivisibility.bidetSpan` | `Formalism/GradedWeylDivisibility/StatementB.lean` | 15 |
| ② | `Formalism.StatementOC` | `Formalism.Sz` / `Formalism.Gz` / `Formalism.Gchi` | `Formalism/StatementOC.lean` | 11, 13, 20 |
| ② | `Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions` | `Formalism.HC.Level.Gm` / `Formalism.HC.ZeroFreeAll` | `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean` | 38, 18 |
| ② | `Formalism.GL3MeanSquares.HookFormulaTorsion.WeightedVonMangoldtSumIdentity` | `Formalism.HermitianLattices.ZeroFreeRegionGL2.weighted_von_mangoldt_sum_identity` | `Formalism/GL3MeanSquares/HookFormulaTorsion/WeightedVonMangoldtSumIdentity.lean` | 227 |
| ② | `Formalism.SizeWindowBrackets.FirstPrimeNeSecondPrime` | `Formalism.LFunctionChainParameters.characterSumData.AskMainBalance` | `Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean` | 98 |
| ③ | `Formalism.LocalRingCardinality.Params` | `Formalism.BasicNotions.Ranks` | `Formalism/LocalRingCardinality/Params.lean` | 6 |
| ③ | `Formalism.LocalRingCardinality.DataKernels` | `Formalism.BasicNotions.ColumnChain.col` | `Formalism/LocalRingCardinality/DataKernels.lean` | 70 |
| ③ | `Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam` | `GlobalTheory.Unf.Chain` | `Development/AbelianVarietyTheory/Definitions/LatticeFrames/IsThetaFam.lean` | 149 |
| ③ | `Formalism.SizeWindowBrackets.SChain` | `Formalism.LFunctionChainParameters.LChain.SizesTextAt` | `Formalism/SizeWindowBrackets/SChain.lean` | 207 |
| ④ | `Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.RallisDM` | `UpperTheory.Lit.Rallis.RallisIPProof.rallis_of_dm` | `Development/AutomorphicArithmetic/ThetaCorrespondence/FockModels/RallisDM.lean` | 24 |
| ④ | `Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BigThetaNormEqRallisInnerProduct` | `GlobalTheory.T.rallis_inner_product_big_theta_lift` | `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/BigThetaNormEqRallisInnerProduct.lean` | 47 |
| ④ | `Formalism.PeriodIntegrals.BesselMapUniq` | `PI.BesselMapUniq.BesselMapUniq` | `Formalism/PeriodIntegrals/BesselMapUniq.lean` | 50 |
| ④ | `Formalism.SharpRestriction.GlobalTheoremInputs` | `Formalism.MainNotions.BesselId` | `Formalism/SharpRestriction/GlobalTheoremInputs.lean` | 65 |
| ④ | `Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian` | `GlobalTheory.Published.SiegelWeilAnisotropicHermitian` | `Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/SiegelWeilAnisotropicHermitian.lean` | 12 |
| ④ | `Formalism.LocalToGlobal.GlobalTheory.GL3.Statement` | `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.ThetaNormIndependent` | `Formalism/LocalToGlobal/GlobalTheory/GL3/Statement.lean` | 48 |
| ⑤ | `Formalism.SizeWindowBrackets.GrowthBoundGivesRiemannHypothesis` | `Formalism.LFunctionChainParameters.ThickSetMeanBounds.SizeWindows` / `GrowthSizeBound` | `Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean` | 109, 119 |
| ⑤ | `Formalism.RankGapBounds.MeanBoundSecondForm` | `Formalism.RankGapBounds.WeightedMeanData.Data.MeanBoundSecondForm` | `Formalism/RankGapBounds/MeanBoundSecondForm.lean` | 187 |
| ⑤ | `Development.AutomorphicArithmetic.MeanSquareBounds.meanSqK` | `QH.meanSqK` | `Development/AutomorphicArithmetic/MeanSquareBounds/meanSqK.lean` | 51 |
| ⑥ | `Formalism.LocalToGlobal.GlobalTheory.GL5.Statement` | `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.WeilSiegelCM` / `MassRatioStd` | `Formalism/LocalToGlobal/GlobalTheory/GL5/Statement.lean` | 31, 45 |
| ⑥ | `Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH` | `Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH` / `Pu` | `Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/PoincareInHH.lean` | 194, 208 |
| ⑥ | `Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn` | `Formalism.L2.SG.ThmSOwn.TheoremSSelected` / `linkS_selH` | `Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/ThmSOwn.lean` | 669, 923 |
| ⑥ | `Formalism.HarderNarasimhan.StatementFrameF` | `Formalism.HN.FrameLA1` / `TheoremF` / `TheoremFSharp` | `Formalism/HarderNarasimhan/StatementFrameF.lean` | 11, 26, 64 |
| ⑦ | `Formalism.HarderNarasimhan.Statement` | `Formalism.HN.SlopeIneq` | `Formalism/HarderNarasimhan/Statement.lean` | 91 |
| ⑦ | `Formalism.HarderNarasimhan.StatementPl` | `Formalism.HN.SizeIneq` / `SlopeIneqMean` | `Formalism/HarderNarasimhan/StatementPl.lean` | 121, 148 |
| ⑦ | `Formalism.HarderNarasimhan.ShiftInvariance` | `Formalism.HN.slopeIneq` / `slopeIneqMean` / `sizeIneq` / `theoremF` | `Formalism/HarderNarasimhan/ShiftInvariance.lean` | 43, 54, 57, 61 |
| ⑦ | `Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.FerreroWashington` | `UpperTheory.V.FW.ferreroWashington` | `Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean` | 104 |
| ⑦ | `GroundTheory.ArithmeticGeometry.IwasawaModules.SpanFinrankMaximalIdealLeTwo` | `GroundTheory.Arith.Iwasawa.Lambda` / `ringKrullDim_eq_two` | `GroundTheory/ArithmeticGeometry/IwasawaModules/SpanFinrankMaximalIdealLeTwo.lean` | 13, 55 |
| ⑧ | `Formalism.BehrendSets.Statement` | `Formalism.BehrendSets.BehrendBound` / `WindowTwo` / `OrbitOne` / `Select` | `Formalism/BehrendSets/Statement.lean` | 54, 67, 72, 105 |
| ⑧ | `Formalism.BehrendSets.TranslateMean` | `Formalism.BehrendSets.Final.select` | `Formalism/BehrendSets/TranslateMean.lean` | 11 |
| ⑧ | `Formalism.FrobeniusOrbits.HostThickExists` | `Formalism.FrobeniusOrbits.HostThickExists` | `Formalism/FrobeniusOrbits/HostThickExists.lean` | 30 |
| ⑨ | `Formalism.GaloisCohomology.Statement` | `Formalism.GaloisCohomology.Sha` / `shaLen` / `VLen` / `VFormula` | `Formalism/GaloisCohomology/Statement.lean` | 75, 78, 80, 138 |
| ⑨ | `Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.VFormula` | `UpperTheory.V.LDataCardLeFinrank.vFormula` | `Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/GaloisCohomologyLength/VFormula.lean` | 16 |
| ⑨ | `Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.MinusLenLeOfCl` | `UpperTheory.V.Kum.shaLen_le_of_cl` | `Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/KummerTheory/MinusLenLeOfCl.lean` | 129 |
| ⑨ | `Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN` | `UpperTheory.Top.VVle` / `IsChiField` / `VWin` | `Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean` | 12, 19, 49 |
| ⑨ | `Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVCore` | `UpperTheory.V.HV.Core.of_four_alt` | `Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/HVCore.lean` | 18 |
| ⑨ | `Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.ClassNumberThree` | `UpperTheory.V.SmallClassNumbers.Bound` / `classNumber_three` | `Development/AutomorphicArithmetic/AutomorphicVarieties/SmallClassNumbers/ClassNumberThree.lean` | 16, 32 |
| ⑨ | `Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.LenEqZeroIff` | `UpperTheory.V.SmallClassNumbers.Large` / `large_of` | `Development/AutomorphicArithmetic/AutomorphicVarieties/SmallClassNumbers/LenEqZeroIff.lean` | 65, 70 |
