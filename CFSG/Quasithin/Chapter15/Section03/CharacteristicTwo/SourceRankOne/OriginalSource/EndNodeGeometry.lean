module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.NaturalEight
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.Small
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.MarkedParabolic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.Supplement

/-!
# The original end-node parabolic and conjugate core geometry

The original middle-node case supplies the natural action, fixed lines and
Sylow subgroup. The proved fixed-vector calculation constructs the marked
end-node parabolic and its residual equality. The separate fixed-line residual
identity then supplies the conjugate product and the two action-kernel factors.

Source: Aschbacher–Smith15.3.32(4)–(6), printed pp.1132–1133.
-/
public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension EightGeometry
  EightGeometry.NaturalModule
variable {G : Type*} [Group G] [Finite G]

/-- The constructed local geometry at the actual end-node parabolic.
The global fixed-line residual equality is deliberately separate. -/
structure EndNodeData (d : LocalData G) (I : Subgroup G) (c : ComponentWitness d I) where
  source : SourceData KnownSimple.IsKnownSimple d c
  action : NaturalEightAction I (d.componentModule I c.L)
  core_centralizer : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2
  fixed_module : d.ZS ⊓ d.componentModule I c.L = d.ZS ⊓ d.V₂
  marking : CompatibleStarMarking d I (d.componentModule I c.L) action
  maximal : IsCoatom ((c.L ⊓ centralizer (d.ZS : Set G)).subgroupOf c.L)
  contains_sylow : d.S ⊓ c.L ≤ c.L ⊓ centralizer (d.ZS : Set G)
  sylow_normalizes : d.S ≤ normalizer ((c.L ⊓ centralizer (d.ZS : Set G) : Subgroup G) : Set G)
  model : EndNodeParabolicModel c.L (c.L ⊓ centralizer (d.ZS : Set G))
  component_image : (d.starImage I c.L).map marking.equiv.toMonoidHom = alternatingGroup (Fin 8)
  parabolic_image : (d.starImage I (c.L ⊓ centralizer (d.ZS : Set G))).map
    marking.equiv.toMonoidHom = fourStabilizer ⊓ alternatingGroup (Fin 8)
  extended_image : (d.starImage I ((c.L ⊓ centralizer (d.ZS : Set G)) ⊔ d.S)).map
    marking.equiv.toMonoidHom = fourStabilizer
  residual_eq : RankOne.threeResidualIn (c.L ⊓ centralizer (d.ZS : Set G)) =
    (pResidual 2 (c.L ⊓ centralizer (d.ZS : Set G) : Subgroup G)).map
      (c.L ⊓ centralizer (d.ZS : Set G)).subtype
  unique : Chapter4.UniqueMaximalOvergroup (d.Yplus ⊔ (d.T : Subgroup G)) d.M

/-- Construct the actual maximal S-invariant parabolic, with its natural
coordinates and every earlier local premise discharged. -/
theorem source_endNodeData
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (mark : Parabolics.MiddleNodeFlagMarking d I c.L) :
    Nonempty (EndNodeData d I c) := by
  obtain ⟨s⟩ := source_smallData hG d hempty hM hu hmany hshadow hI hf c
  obtain ⟨a,_,hC,_,hfixed,hfirst,hmodule⟩ :=
    source_lemma_15_3_32_1_2 hG d hempty hM hu hmany hshadow hI hf c mark
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hZ := d.action.card_centralInvolutions d.T d.sylow_le
  have hsecond : Nat.card (d.ZS ⊓ d.V₂ : Subgroup G) = 2 :=
    FixedGeometry.card_plane_intersection d hi hZ s.omega.2 _
  obtain ⟨b,hmax,hSL,hSN,⟨model⟩,hL,hK,hKS,hres⟩ :=
    MarkedParabolic.exists_marked_parabolic d c s.normal s.generated
      mark.toMiddleNodePermutationMarking a s.sylow s.sylow_eq hC.symm
      hfixed s.omega.2 hfirst hsecond hmodule
  have hunique : Chapter4.UniqueMaximalOvergroup (d.Yplus ⊔ (d.T : Subgroup G)) d.M := by
    obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
      hG d.T hempty hM hu hmany hZ
    have h7 := source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action hM hu hmany hne
    apply unique_yplus_join_sylow d
      (OutsideStructure.LocalBranches.second_choice_noncentral d s.facts.choice h7.1)
    intro X hTX hXM
    exact (source_lemma_15_3_2_4 d.T d.action hM hTX hXM).imp
      (fun h => h.trans inf_le_right) And.right
  exact ⟨⟨s,a,hC.symm,hmodule,b,hmax,hSL,hSN,model,hL,hK,hKS,hres,hunique⟩⟩

namespace EndNodeData
variable {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}
  (e : EndNodeData d I c)
include e

omit [Finite G] in
/-- The global residual and the two-residual of the actual end-node parabolic
agree, once the independent fixed-line residual identity is supplied. -/
theorem global_residual
    (hL : c.L = RankOne.threeResidualIn
      (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G))) :
    RankOne.threeResidualIn (centralizer (d.ZS : Set G)) =
      (pResidual 2 (c.L ⊓ centralizer (d.ZS : Set G) : Subgroup G)).map
        (c.L ⊓ centralizer (d.ZS : Set G)).subtype := by
  rw [threeResidual_fixedPlane_eq_component_intersection d hL,e.residual_eq]

/-- The actual Sylow extension has the marked four-block stabilizer. -/
theorem residual_join_marking
    (hL : c.L = RankOne.threeResidualIn
      (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G))) :
    let N := RankOne.threeResidualIn (centralizer (d.ZS : Set G)) ⊔ d.S
    (d.starImage I N).map e.marking.equiv.toMonoidHom = fourStabilizer := by
  have he := residual_join_eq_fixedPlane_centralizer_of_residual_equality d c
    e.source.normal e.source.generated ⟨e.source.sylow,e.source.sylow_eq⟩ hL e.residual_eq
  rw [fixedPlane_centralizer_decomposition d c e.source.normal e.source.generated] at he
  change (d.starImage I _).map _ = _
  rw [he]
  exact e.extended_image

/-- The original conjugate modules form the literal internal direct product. -/
theorem source_conjugate_product
    (hL : c.L = RankOne.threeResidualIn
      (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)))
    (t : G) (ht : t ∈ (d.T : Subgroup G)) (htS : t ∉ d.S) :
    let U := d.componentModule I c.L
    let N := RankOne.threeResidualIn (centralizer (d.ZS : Set G)) ⊔ d.S
    Disjoint U (U.conjBy t) ∧ N ≤ normalizer ((U ⊔ U.conjBy t : Subgroup G) : Set G) ∧
      U ≤ centralizer (U.conjBy t : Set G) ∧
      ∃ f : U × U.conjBy t ≃* ↥(U ⊔ U.conjBy t),
        ∀ u v, (f (u,v) : G) = (u : G) * (v : G) :=
  lemma_15_3_32_5_of_fixed_plane d e.source.minimal.1 c e.action e.source.sylow
    e.source.sylow_eq (d.action.planeStabilizer_index_two d.T d.sylow_le 1)
    (d.action.card_centralInvolutions d.T d.sylow_le) hL e.fixed_module t ht htS

/-- Both action centralizers generate the core of the original residual join. -/
theorem source_core_generation
    (hL : c.L = RankOne.threeResidualIn
      (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)))
    (t : G) (ht : t ∈ (d.T : Subgroup G)) (htS : t ∉ d.S) :
    let U := d.componentModule I c.L
    let N := RankOne.threeResidualIn (centralizer (d.ZS : Set G)) ⊔ d.S
    N ⊓ centralizer (U : Set G) ≤ d.S ∧
      N ⊓ centralizer (U.conjBy t : Set G) ≤ d.S ∧
      pCore 2 N = actionCentralizer N U ⊔ actionCentralizer N (U.conjBy t) := by
  have hNI := residual_join_le_of_line_centralizer d e.source.minimal.1 c hL
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  exact core_eq_actionCentralizers_of_irreducible d e.source.minimal.1 c e.source.contains
    e.source.sylow e.source.sylow_eq le_sup_right hNI
    (residual_join_normalized_by_sylow d hi) hi e.unique
    (starCoreIrreducible_of_fourStabilizer d hNI e.marking.equiv (e.residual_join_marking hL))
    e.core_centralizer t ht htS

end EndNodeData
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
