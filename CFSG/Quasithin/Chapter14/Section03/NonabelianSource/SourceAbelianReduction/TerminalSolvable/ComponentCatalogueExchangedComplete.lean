module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulRecognition
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedPairedRecognition

/-!
# The complete exchanged-component source conclusion

Split the kernel of the literal chosen constituent action into its central
and noncentral cases. The completed faithful-image recognition handles the
first; the paired-A5 recognition handles the second. Both conclusions concern
the original moved component, and the original small-actor source theorem
then constructs its ambient local lift. No image-classification premise or
kernel alternative is retained as an extra assumption.

Source: Aschbacher--Smith G.10.15 and 14.3.15,
printed pp.362--363 and 994.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Original exchanged constituent data give the original component cases;
centrality of its action kernel is decided inside the proof. -/
theorem source_exchanged_component_image_cases
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hn : ¬ Group.IsSolvable F.TerminalHdot)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hsmall : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      finrank (ZMod 2) (Additive F.Uhat) / 2 - 1)
    {L : Subgroup F.TerminalHdot} (hL : IsComponent F.TerminalHdot L)
    (hm : ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (ho : ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B L)
    (hfix : fixedSpace F.terminalRepresentation (componentOrbit L ⊤)=⊥)
    (hcom : subspaceCommutator F.terminalRepresentation ⊤ (componentOrbit L ⊤)=⊤)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation
      (componentOrbit L ⊤) (F.terminalDot (F.X g)) I)
    (hirr : IsIrreducible
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I hI.invariant).toRepresentation)
    (hspan : letI : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
      (⨆ a : F.TerminalHdot, conjugateSubrepresentation F.terminalRepresentation
        (componentOrbit L ⊤)
        (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I hI.invariant) a)=⊤)
    (hdis : ∀ a : F.TerminalHdot,
      I.map (F.terminalRepresentation a)=I ∨ Disjoint (I.map (F.terminalRepresentation a)) I)
    (hform : (∀ u∈I,∀ w∈I,B u w=0) ∨ (B.restrict I).Nondegenerate)
    (hdim : 2 < finrank (ZMod 2) I)
    (hind : sSupIndep (subspaceOrbit F.terminalRepresentation (F.terminalDot (F.X g)) I))
    (hv : v∉I)
    : ComponentImageCases L := by
  by_cases hk : (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
      hI.invariant).toRepresentation.asGroupHom.ker ≤ Subgroup.center (componentOrbit L ⊤)
  · let s : ExchangedCentralSource T M Mc F g B v L I := {
      simple := hG
      empty := hempty
      maximal := hM
      unique_overgroup := hu
      many_overgroups := hmany
      seed_card := hcard
      centralizer_quotient := ⟨e⟩
      not_model := hnot
      nonabelian := hne
      parabolic_mem := hgP
      normalizer_not_mem := hgH
      nonsolvable := hn
      hypothesis := hyp
      small_actor := hsmall
      component := hL
      moved := hm
      orthogonal := ho
      fixedSpace_eq_bot := hfix
      commutator_eq_top := hcom
      selected := hI
      irreducible := hirr
      conjugate_span := hspan
      conjugate_disjoint := hdis
      form_cases := hform
      dimension_gt_two := hdim
      independent := hind
      point_not_mem := hv
      central_kernel := hk }
    exact s.component_image_cases
  · let s : ExchangedPairedSource T M Mc F g B v L I := {
      simple := hG
      empty := hempty
      maximal := hM
      unique_overgroup := hu
      many_overgroups := hmany
      seed_card := hcard
      centralizer_quotient := ⟨e⟩
      not_model := hnot
      nonabelian := hne
      parabolic_mem := hgP
      normalizer_not_mem := hgH
      nonsolvable := hn
      hypothesis := hyp
      small_actor := hsmall
      component := hL
      moved := hm
      orthogonal := ho
      fixedSpace_eq_bot := hfix
      commutator_eq_top := hcom
      selected := hI
      irreducible := hirr
      conjugate_span := hspan
      conjugate_disjoint := hdis
      form_cases := hform
      dimension_gt_two := hdim
      independent := hind
      point_not_mem := hv
      noncentral_kernel := hk }
    exact s.component_image_cases

/-- The actual ambient local lift, from the full original exchanged-source
prefix and constituent selection, without a classification callback. -/
theorem source_exchanged_component_local_lift
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hn : ¬ Group.IsSolvable F.TerminalHdot)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hsmall : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      finrank (ZMod 2) (Additive F.Uhat) / 2 - 1)
    {L : Subgroup F.TerminalHdot} (hL : IsComponent F.TerminalHdot L)
    (hm : ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (ho : ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B L)
    (hfix : fixedSpace F.terminalRepresentation (componentOrbit L ⊤)=⊥)
    (hcom : subspaceCommutator F.terminalRepresentation ⊤ (componentOrbit L ⊤)=⊤)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation
      (componentOrbit L ⊤) (F.terminalDot (F.X g)) I)
    (hirr : IsIrreducible
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I hI.invariant).toRepresentation)
    (hspan : letI : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
      (⨆ a : F.TerminalHdot, conjugateSubrepresentation F.terminalRepresentation
        (componentOrbit L ⊤)
        (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I hI.invariant) a)=⊤)
    (hdis : ∀ a : F.TerminalHdot,
      I.map (F.terminalRepresentation a)=I ∨ Disjoint (I.map (F.terminalRepresentation a)) I)
    (hform : (∀ u∈I,∀ w∈I,B u w=0) ∨ (B.restrict I).Nondegenerate)
    (hdim : 2 < finrank (ZMod 2) I)
    (hind : sSupIndep (subspaceOrbit F.terminalRepresentation (F.terminalDot (F.X g)) I))
    (hv : v∉I)
    : ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K := by
  have hc := source_exchanged_component_image_cases hG T hempty hM hu hmany hcard e hnot
    F hne g hgP hgH hn hyp hsmall hL hm ho hfix hcom hI hirr hspan hdis hform hdim hind hv
  exact source_component_catalogue_of_small_actor_image hG T hempty hM hu hmany hcard e
    F hne g hgP hgH hyp hsmall hL hm hc

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
