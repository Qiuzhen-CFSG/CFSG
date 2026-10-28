module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeDiagramApplication
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# Diagram residuals in the chosen-module Cartan argument

The E.2.2 source marking now determines the literal residual two-core
quotient and its Sylow intersection. The field-four diagram row gives
Cartan normalization at original degree two without a selected parabolic.
The selected A₅ and smaller-Sylow rank-two applications discharge their
intrinsic residual-model premises from the same source marking.

Diagram parabolic selection, zero-core model exclusions and the remaining
normalization branches still belong to the local-to-global assembly owner.
Source: Aschbacher–Smith 5.2.2 and 12.2.2, pp.646–649,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Prime
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D R : Subgroup G} (M : ChosenModule T L V)
include M

/-- The source diagram over field four closes the original degree-two normalization branch. -/
theorem rankOne_cartan_normalizes_of_diagram_field_four
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    (hm : DiagramModel ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) 2) :
    A ≤ normalizer (residual H : Set G) :=
  (M.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl).cartan_normalizes_of_diagram_field_four hH hpar hthree c hcontrol hC hqs hc hm

/-- The nonprojective source rows use the actual residual degree without a parabolic callback. -/
theorem rankOne_cartan_normalizes_of_nonprojective_diagram_small_degree
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n f : ℕ} (hn : n = 2 ∨ n = 4 ∨ n = 8)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H) (hnf : n ∣ f)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    (hm : DiagramModel ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) f)
    (hproj : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f)) :
    A ≤ normalizer (residual H : Set G) :=
  (M.rankOne_generic_input_of_many h hmany (by omega) hpsl).cartan_normalizes_of_nonprojective_diagram_small_degree hH hpar c hcontrol hn hnf hC hqs hc hf hm hproj

/-- The selected A₅ diagram row excludes the actual prime actor at original degree two. -/
theorem rankOne_cartan_diagram_A5_prime_excluded_degree_two
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {p f : ℕ} (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (d : LocalData T L H B D R) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    (hm : DiagramModel ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) f)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) : False :=
  d.diagram_A5_prime_excluded_degree_two
    (M.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl)
    hH hpar hthree c hcontrol hd hz hC hqs hc hf hm hA5

/-- The actual smaller-Sylow rank-two container forces the source field degree and prime to three. -/
theorem rankOne_cartan_diagram_rankTwo_container_degree_three
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p f : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (d : LocalData T L H B D R)
    (hd : CartanPrimeActor A H p D) (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    {K : Subgroup G} (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hmodel : Chapter1.Section02.LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K))
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    (hm : DiagramModel ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) f) : f = 3 ∧ p = 3 :=
  d.diagram_rankTwo_container_degree_three (M.rankOne_generic_input_of_many h hmany hn hpsl)
    hH c hd hz hSyl hRK hKX hK hKn hmodel hC hqs hc hf hm

/-- The original diagram source constructs the literal left Borel and rank-one quotient. -/
theorem rankOne_cartan_diagram_prime_left_structure
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p f : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    (hm : DiagramModel ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) f) :
    ChapterF.Source.borel (D ⊔ Global.sourceS L H) (Global.sourceS L H) = Global.sourceS L H ∧
      ChapterF.Source.IsRankOneModel ((D ⊔ Global.sourceS L H : Subgroup G) ⧸
        pCore 2 (D ⊔ Global.sourceS L H : Subgroup G)) :=
  diagram_prime_left_structure (M.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hpar c hd hC hc hf hm

/-- The chosen-module source dispatcher retains the real diagram models and Sylow equality. -/
theorem rankOne_cartan_prime_pair_or_intrinsic_diagram
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    (∃ R : Subgroup G, LocalData T L H B D R) ∨
      (Global.RightDiagramSource T L H ∧
        Global.sourceS L H ⊓ residual H = (T : Subgroup G) ⊓ residual H ∧
        ∃ f : ℕ, 1 < f ∧
          (ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
           Chapter1.Section02.LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
           ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))) :=
  source_prime_pair_or_intrinsic_diagram (M.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hpar c hd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
