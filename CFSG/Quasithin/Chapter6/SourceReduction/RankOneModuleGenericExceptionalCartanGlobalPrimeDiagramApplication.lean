module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeDiagramSource
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalParabolicDegree
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeExchangedSelection

/-!
# Applying the diagram source to the original Cartan argument

The intrinsic residual marking constructed from E.2.2 discharges the model
premise in the existing field comparison and changed-Sylow exclusions. An
A₅ selected parabolic forces the marked diagram field to have order four.
For original degree two, the original PSL₃(4) exclusion leaves SL₃(4) and
Sp₄(4); their split tori give the actual Cartan normalization conclusion.
This also proves normalization directly from a diagram marking over field
four, without first selecting a parabolic. The general nonprojective rows
use the already proved degree-two, four and eight normalization when the
original degree divides the marked residual degree.

The source equality S ∩ K = T ∩ K supplies the literal left Borel and
rank-one quotient for DS. The complete source dispatcher now leaves a
diagram branch with an actual intrinsic rank-two residual model and the
proved Sylow equality. Its parabolic selection, zero-core exclusions,
remaining field comparisons and final normalization remain obligations of
qt-d-1222-rankone-cartan-local-to-global.
Source: Aschbacher–Smith 5.1.10–11 and 5.2.2, pp.634–635,646–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The nonprojective diagram rows normalize the original small-degree Cartan
when its degree divides the actual marked residual degree. -/
theorem Input.cartan_normalizes_of_nonprojective_diagram_small_degree
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G} {n f : ℕ}
    (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hn : n = 2 ∨ n = 4 ∨ n = 8) (hnf : n ∣ f)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    (hm : DiagramModel ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) f)
    (hproj : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f)) :
    A ≤ normalizer (residual H : Set G) := by
  have hr := (diagram_source_residual_quotient h.sylow_normalizes hH.1.1.2
    hC hqs hc hf hm).resolve_left hproj
  rcases hr with hr | hr
  · rcases hn with hn | hn | hn
    · exact h.cartan_normalizes_of_specialLinear_residual_small_degree hH c hcontrol (.inl hn) hf hnf hr
    · exact h.cartan_normalizes_of_specialLinear_residual_small_degree hH c hcontrol (.inr hn) hf hnf hr
    · subst n
      exact h.cartan_normalizes_of_specialLinear_residual_degree_eight hH c hcontrol hf hnf hr
  · rcases hn with hn | hn | hn
    · exact h.cartan_normalizes_of_symplectic_residual_small_degree hH hpar c hcontrol (.inl hn) hf hnf hr
    · exact h.cartan_normalizes_of_symplectic_residual_small_degree hH hpar c hcontrol (.inr hn) hf hnf hr
    · subst n
      exact h.cartan_normalizes_of_symplectic_residual_degree_eight hH hpar c hcontrol hf hnf hr

/-- At degree two and source field four, the original PSL₃(4) exclusion
closes the entire diagram row without a selected-factor hypothesis. -/
theorem Input.cartan_normalizes_of_diagram_field_four
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G}
    (h : Input κ T L W 2)
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
  h.cartan_normalizes_of_nonprojective_diagram_small_degree hH hpar c hcontrol
    (.inl rfl) (dvd_refl 2) hC hqs hc (by decide) hm hthree

namespace Prime

/-- Comparing the actual selected A₅ parabolic with the source quotient
forces field four in all three diagram covering alternatives. -/
theorem LocalData.diagram_A5_field
    {T : Sylow 2 G} {L H B D R : Subgroup G} {f : ℕ}
    (d : LocalData T L H B D R)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) (hR : R < residual H)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    (hm : DiagramModel ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) f)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) : f = 2 :=
  d.rankTwo_residual_degree_eq hTH hR hf
    (diagram_source_residual_quotient hTL hTH hC hqs hc hf hm) (m := 2) hA5

/-- The actual escaping-prime configuration in the diagram A₅ row is
impossible at original degree two; the supplied source exclusion is used literally. -/
theorem LocalData.diagram_A5_prime_excluded_degree_two
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {p f : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hd : CartanPrimeActor A H p D) (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    (hm : DiagramModel ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) f)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) : False := by
  have hf2 := d.diagram_A5_field h.sylow_normalizes hH.1.1.2
    (d.right_lt_residual hH.1.1.2 c hd hz) hC hqs hc hf hm hA5
  subst f
  exact h.prime_actor_not_normalizes hH hd (hd.le_cartan.trans
    (h.cartan_normalizes_of_diagram_field_four hH hpar hthree c hcontrol hC hqs hc hm))

/-- A rank-two overcomponent at the smaller Sylow forces the marked diagram
degree and escaping prime both to be three. No residual-model callback remains. -/
theorem LocalData.diagram_rankTwo_container_degree_three
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p f : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hmodel : Chapter1.Section02.LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K))
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    (hm : DiagramModel ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) f) : f = 3 ∧ p = 3 :=
  d.source_rankTwo_container_residual_degree_three h hH c hd hz hSyl hRK hKX hK hKn
    hmodel hf (diagram_source_residual_quotient h.sylow_normalizes hH.1.1.2 hC hqs hc hf hm)

/-- The diagram source supplies both literal left rank-one clauses before
any parabolic is selected on the right. -/
theorem diagram_prime_left_structure
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p f : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
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
        pCore 2 (D ⊔ Global.sourceS L H : Subgroup G)) := by
  have hs := diagram_sourceS_intersection_residual h.sylow_normalizes hH hpar hC hc hf hm
  exact ⟨Input.prime_left_borel h hH c hd hs,Input.prime_left_quotient h hH c hd hs⟩

/-- The original dispatcher yields either the constructed rank-one pair or
a genuine intrinsic diagram residual, together with its Sylow intersection. -/
theorem source_prime_pair_or_intrinsic_diagram
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hd : CartanPrimeActor A H p D) :
    (∃ R : Subgroup G, LocalData T L H B D R) ∨
      (Global.RightDiagramSource T L H ∧
        Global.sourceS L H ⊓ residual H = (T : Subgroup G) ⊓ residual H ∧
        ∃ f : ℕ, 1 < f ∧
          (ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
           Chapter1.Section02.LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
           ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))) := by
  rcases source_prime_pair_or_diagram h hH hpar c hd with hd | hs
  · exact Or.inl hd
  · have hs' := hs
    obtain ⟨C,f,hC,hqs,_,hf,hc,hm⟩ := hs
    exact Or.inr ⟨hs',diagram_sourceS_intersection_residual h.sylow_normalizes hH hpar hC hc hf hm,
      f,hf,diagram_source_residual_quotient h.sylow_normalizes hH.1.1.2 hC hqs hc hf hm⟩

end Prime
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
