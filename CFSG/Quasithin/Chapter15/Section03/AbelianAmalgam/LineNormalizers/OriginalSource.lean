module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.SourceAssembly
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Source49.Original
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.FullAction.Kernel
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly.OriginalGeometry

/-!
# Original local data for the final singular-line argument

The original orthogonal action supplies the definite plane and central line.
Its residual action is transported through the canonical quotient comparison.
The ordinary alternative of 15.3.49 identifies both residual centralizers:
the intersection with Mc has order prime to three, so its image in the
elementary-nine quotient is trivial. The same source theorem supplies core
movement and the fixed-plane normalizer bound.

This constructs the literal input for selecting the escaping singular line.
Only the independent conclusions of 15.3.45, 15.3.50 and 15.3.65 remain
explicit, together with the separate F.6 classification in the final consumer.
Their original-source producers retain final discharge.

Source: Aschbacher--Smith, 15.3.49--50, 15.3.65--68 and the final proof of
15.3.1, printed pp.1142--1155.
-/

public noncomputable section
open Subgroup Stellmacher OrthogonalFourBinary Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizerSource
open ChapterA.Section05To06 FusionCore.CosetSetup
open TerminalSourceEndgame.OriginalSource GoldschmidtCore.LocalRelations
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem original_residual_centralizer
    (d : CharacteristicTwo.LocalData G)
    (ho : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V)
    (hMc : d.Mc = centralizer (d.Z : Set G))
    (hfactor : ∀ x ∈ d.M ⊓ d.Mc,
      ∃ c ∈ d.M ⊓ centralizer (d.V : Set G),
        ∃ t ∈ (d.T : Subgroup G), c * t = x) :
    d.Y.pCoreIn 2 = d.Y ⊓ centralizer (d.Z : Set G) := by
  have hc := ExtraspecialLocal.centralizer_three_prime_of_ordinary
    d.M d.Y d.V ho.2.2 ho.1.symm
  have hr := (lemma_15_3_49_1 d.M d.Mc d.Mc d.V d.T
    d.action.normalizes d.sylow_le le_rfl hfactor).trans inf_le_right
  have hp := ExtraspecialLocal.three_prime_of_residual_bound
    (d.M ⊓ d.Mc) d.M d.V inf_le_left hc hr
  apply le_antisymm
  · rw [ho.1]
    exact inf_le_inf_left _ (centralizer_le (le_conjugateSpanBy _ _))
  · apply ExtraspecialLocal.three_prime_subgroup_le_core _ d.Y inf_le_left
    · apply hp.of_dvd_right
      apply card_dvd_of_le
      rw [hMc]
      exact inf_le_inf_right _ (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc)
    · obtain ⟨e⟩ := ho.2.1
      apply IsPGroup.of_card (n := 2)
      rw [Nat.card_congr e.toEquiv]
      norm_num [ThreeAlternatives.ElementaryNine, Nat.card_eq_fintype_card]

/-- Construct every pre-line field from the original hypotheses and the
independent abelian-span conclusion of 15.3.50. -/
def beforeLine_from_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
    (hspan : IsMulCommutative (conjugateSpanBy d.V d.Mc)) :
    BeforeLine d.T d.M d.Mc d.V₁ := by
  letI : IsElementaryAbelian 2 d.V := Preamble.vector_elementary d.action
  let a := FusionCore.OriginalCoordinates.standardAction d.action
  let q := FusionCore.OriginalCoordinates.quadraticAction d.action
  have hP := FusionCore.OriginalCoordinates.plane_definite d.action 1
  have hf := OriginalSource.source_fusion_inputs hG d hM hfixed
  have h46 := FusionCore.lemma_15_3_46_of_earlier_inputs q hf hP
  have hMc := OriginalSource.source_partner_eq hG d hempty hM hu hmany
  have ho := Source49.ordinary_from_original hG d hempty hM hu hmany hfixed
  obtain ⟨hne, _, _⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  obtain ⟨himage, _, hproduct, _, _, _, _⟩ :=
    source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action hM hu hmany hne
  have hfactor : ∀ x ∈ d.M ⊓ d.Mc,
      ∃ c ∈ d.M ⊓ centralizer (d.V : Set G),
        ∃ t ∈ (d.T : Subgroup G), c * t = x := by
    intro x hx
    have hx' : x ∈ ((d.M ⊓ d.Mc : Subgroup G) : Set G) := hx
    rw [hproduct] at hx'
    exact hx'
  have hres : actionImage a d.Y = pResidual 2 TerminalLines.IsometryGroup := by
    let e := actorComparison a d.action
    have hm : (actionImage a d.Y).map e.toMonoidHom = d.action.image d.Y := by
      rw [actionImage, Subgroup.map_map]
      change (d.Y.subgroupOf d.M).map _ = (d.Y.subgroupOf d.M).map _
      congr 1
      apply MonoidHom.ext
      intro m
      exact actorComparison_apply a d.action m
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [hm, map_pResidual_of_surjective 2 _ e.surjective]
    exact himage.trans RankTwo.orthogonal_twoResidual_eq_pResidual
  refine {
    natural := a
    ordering := hM
    module_le := (OriginalSource.source_seed_geometry d).1
    plane_le := d.action.plane_le 1
    plane_card := d.action.card_plane 1
    plane_definite := ?_
    central_fixed := NaturalOrthogonalAction.centralInvolutions_eq_fixedPlane d.T d.sylow_le d.action
    central_card := d.action.card_centralInvolutions d.T d.sylow_le
    other_centralizer := hMc
    residual_image := hres
    residual_core_module := ho.1
    residual_core_center := original_residual_centralizer d ho hMc hfactor
    core_movement := Source49.core_movement_from_original hG d hempty hM hu hmany hfixed
    local_span_abelian := hspan
    singular_intersection := ?_ }
  · intro v hv hs
    have hn : (⟨v, d.action.plane_le 1 v.property⟩ : d.V) ≠ 1 := by
      intro he
      exact hv (Subtype.ext (congrArg (fun x : d.V => (x : G)) he))
    exact hP.2.2 ⟨v, d.action.plane_le 1 v.property⟩ v.property hn
      ((FusionCore.OriginalCoordinates.quadraticAction_singular d.action _).mpr hs)
  · intro g hg x
    exact (FusionCore.OriginalCoordinates.quadraticAction_singular d.action _).mp
      ((h46.2.1.1 g hg).2 ⟨x, x.property.1⟩ x.property)

/-- Select the actual singular line and apply the terminal contradiction.
The span and rank conclusions remain assigned to the original 15.3.50 and
15.3.65 producers; F.6 retains its independent recognition assembly. -/
theorem terminal_contradiction_of_original_span_rank
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
    (hspan : IsMulCommutative (conjugateSpanBy d.V d.Mc))
    (hr : ChapterE.globalR d.V = 2)
    (classificationF : GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SourceClassificationInput.{u}
      KnownSimple.IsKnownSimple) : False := by
  obtain ⟨E, earlier, _, _⟩ := exists_earlierData_of_rank_two
    (beforeLine_from_original hG d hempty hM hu hmany hfixed hspan) hr
  exact GoldschmidtCore.Centrality.SourceAssembly.terminal_contradiction_knownSimple_from_original_bounds
    earlier hG hfixed
    (Source49.normalizer_three_prime_from_original hG d hempty hM hu hmany hfixed)
    classificationF

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizerSource
