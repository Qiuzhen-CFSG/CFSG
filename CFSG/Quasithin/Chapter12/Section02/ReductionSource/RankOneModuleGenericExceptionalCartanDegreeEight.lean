module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalDegreeEight
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# Degree-eight Cartan normalization in the chosen-module setup

The original chosen module supplies the complete rank-one input. The new
order-seventeen argument completes normalization for degree eight in the
SL₃ and Sp₄ residual rows and the marked exchanged PSL₂ row whenever the
original degree divides the right field degree. No module decomposition,
central-omega torus factor, prime-exclusion callback or selected-factor
component hypothesis is added. The exchanged marking retains its actual
H-component in the quotient by core_H(M).

Source: Aschbacher–Smith 5.2.2, pp.647–649, applied to 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B : Subgroup G} (M : ChosenModule T L V)
include M

/-- The actual SL₃ residual branch at original degree eight. -/
theorem rankOne_cartan_normalizes_of_specialLinear_residual_degree_eight
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ 8))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    {f : ℕ} (hf : 1 < f) (hnf : 8 ∣ f)
    (hm : Chapter1.Section02.LocalModels.IsSL
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f)) :
    A ≤ normalizer (residual H : Set G) :=
  (M.rankOne_generic_input_of_many h hmany (by decide) hpsl).cartan_normalizes_of_specialLinear_residual_degree_eight
    hH c hcontrol hf hnf hm

/-- The actual Sp₄ residual branch constructs its own Hall-torus marking. -/
theorem rankOne_cartan_normalizes_of_symplectic_residual_degree_eight
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ 8))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    {f : ℕ} (hf : 1 < f) (hnf : 8 ∣ f)
    (hm : ClassicalGroup.IsPSp
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f)) :
    A ≤ normalizer (residual H : Set G) :=
  (M.rankOne_generic_input_of_many h hmany (by decide) hpsl).cartan_normalizes_of_symplectic_residual_degree_eight
    hH hgen c hcontrol hf hnf hm

/-- The exchanged PSL₂ branch retains the actual source component and Borel. -/
theorem rankOne_cartan_normalizes_of_exchanged_linear_degree_eight
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ 8))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    {f : ℕ} (hnf : 8 ∣ f)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ f)
    (hm : ModelBorelPair ((normalizer (L : Set G)).subgroupOf H) C
      (BenderSuzuki.Converse.PBorel F)) :
    A ≤ normalizer (residual H : Set G) :=
  (M.rankOne_generic_input_of_many h hmany (by decide) hpsl).cartan_normalizes_of_exchanged_linear_degree_eight
    hH c hcontrol hnf hC hqs hc hF hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
