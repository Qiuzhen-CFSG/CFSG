module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedComplete
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.AlternatingSixActionSourceMultiplicityRank
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.AlternatingSixActionSourceIrreducible
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.AlternatingSix
public import Theory.Representation.BinaryAlternatingSixModels.SelfDual

/-!
# The original A₆ point in the small-actor branch

The original selected constituent cannot miss the marked point. In that case
a central constituent kernel gives a non-self-dual irreducible action, contrary
to the complete fixed-action A₆ self-duality theorem. A noncentral kernel
recognizes the original component as A₅, contradicting its A₆ order. The same constituent then supplies the completed Schur
coordinates and the natural diagram action, including the reducible case.

Source: Aschbacher--Smith G.10.15, G.11.6 and 14.3.15, pp.362--366,994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_terminal_a6_selected_point_of_small_actor
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
    {K : Subgroup G} (hK : ComponentLift F g K)
    (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6))
    (ho : ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B (F.terminalDot K))
    (hfix : fixedSpace F.terminalRepresentation (componentOrbit (F.terminalDot K) ⊤)=⊥)
    (hcom : subspaceCommutator F.terminalRepresentation ⊤ (componentOrbit (F.terminalDot K) ⊤)=⊤)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation
      (componentOrbit (F.terminalDot K) ⊤) (F.terminalDot (F.X g)) I)
    (hirr : IsIrreducible
      (invariantSubspace F.terminalRepresentation (componentOrbit (F.terminalDot K) ⊤) I hI.invariant).toRepresentation)
    (hspan : letI : (componentOrbit (F.terminalDot K) ⊤).Normal := componentOrbit_top_normal (F.terminalDot K)
      (⨆ a : F.TerminalHdot, conjugateSubrepresentation F.terminalRepresentation
        (componentOrbit (F.terminalDot K) ⊤)
        (invariantSubspace F.terminalRepresentation (componentOrbit (F.terminalDot K) ⊤) I hI.invariant) a)=⊤)
    (hdis : ∀ a : F.TerminalHdot,
      I.map (F.terminalRepresentation a)=I ∨ Disjoint (I.map (F.terminalRepresentation a)) I)
    (hform : (∀ u∈I,∀ w∈I,B u w=0) ∨ (B.restrict I).Nondegenerate)
    (hdim : 2 < finrank (ZMod 2) I)
    (hind : sSupIndep (subspaceOrbit F.terminalRepresentation (F.terminalDot (F.X g)) I))
    : v ∈ I := by
  classical
  by_contra hv
  let := hK.alternatingSix_image_normal hG e6
  have hoL : componentOrbit (F.terminalDot K) ⊤ = F.terminalDot K :=
    le_antisymm
      (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl le_normalizer_of_normal)
      (le_componentOrbit _ _)
  by_cases hk : (invariantSubspace F.terminalRepresentation (componentOrbit (F.terminalDot K) ⊤) I
      hI.invariant).toRepresentation.asGroupHom.ker ≤ Subgroup.center (componentOrbit (F.terminalDot K) ⊤)
  · let s : ExchangedCentralSource T M Mc F g B v (F.terminalDot K) I := {
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
      component := hK.image_component
      moved := hK.image_moved
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
    let := hirr
    exact s.faithful_data.2.1
      (BinaryAlternatingSix.selfDual_of_alternatingSix_equiv
        (invariantSubspace F.terminalRepresentation (componentOrbit (F.terminalDot K) ⊤)
          I hI.invariant).toRepresentation
        ((MulEquiv.subgroupCongr hoL).trans e6))
  · let s : ExchangedPairedSource T M Mc F g B v (F.terminalDot K) I := {
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
      component := hK.image_component
      moved := hK.image_moved
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
    have hc := Nat.card_congr
      (e6.symm.trans s.component_alternating_five.some).toEquiv
    rw [nat_card_alternatingGroup, nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial] at hc

/-- Select a proper constituent containing the original point, for the same
supplied component and G.10 hypothesis, when its whole action is reducible. -/
theorem source_terminal_a6_proper_point_of_small_actor
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {K : Subgroup G} (hK : ComponentLift F g K)
    (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6))
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hsmall : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      finrank (ZMod 2) (Additive F.Uhat) / 2 - 1)
    (hred : ¬ IsIrreducible (F.terminalRepresentation.comp (F.terminalDot K).subtype)) :
    ∃ I : Submodule (ZMod 2) (Additive F.Uhat),
      IsIrrPlus F.terminalRepresentation (componentOrbit (F.terminalDot K) ⊤) I ∧
      v ∈ I ∧ I ≠ ⊤ := by
  have hn := hK.terminal_not_solvable
  obtain ⟨hfix,hcom,I,hI,hirr,hspan,hdis,hform,hdim,hind⟩ :=
    componentOrbit_selection F.terminalRepresentation hyp.faithful
      (hyp.irreducible_of_not_solvable hn) B hyp.alternating hyp.preserves
      hK.image_component (IsElementaryAbelian.isPGroup 2 (F.terminalDot (F.X g)))
  have hv := source_terminal_a6_selected_point_of_small_actor
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hn hyp hsmall hK e6
    (hyp.component_orthogonal_data hn (F.terminalDot K)) hfix hcom
    hI hirr hspan hdis hform hdim hind
  refine ⟨I,hI.isIrrPlus,hv,?_⟩
  intro htop
  apply hred
  let := hK.alternatingSix_image_normal hG e6
  have hoL : componentOrbit (F.terminalDot K) ⊤ = F.terminalDot K :=
    le_antisymm
      (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl le_normalizer_of_normal)
      (le_componentOrbit _ _)
  subst I
  let ee : Representation.Equiv
      (invariantSubspace F.terminalRepresentation (componentOrbit (F.terminalDot K) ⊤)
        ⊤ hI.invariant).toRepresentation
      (F.terminalRepresentation.comp (componentOrbit (F.terminalDot K) ⊤).subtype) :=
    .mk Submodule.topEquiv (by intro a; ext x; rfl)
  have hh := (RepEquiv.ofRepresentationEquiv ee.symm).irreducible_of_euqiv hirr
  exact (congrArg (fun A : Subgroup F.TerminalHdot =>
    IsIrreducible (F.terminalRepresentation.comp A.subtype)) hoL).mp hh

/-- The original small actor supplies the complete natural diagram action.
The reducible branch uses the proper original point constituent and the proved
Schur-rank coordinates; the irreducible branch uses its existing recognition. -/
theorem source_terminal_a6_natural_action_of_small_actor
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {K : Subgroup G} (hK : ComponentLift F g K)
    (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6))
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hsmall : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      finrank (ZMod 2) (Additive F.Uhat) / 2 - 1)
    : hK.AlternatingSixNaturalAction e6 := by
  by_cases hi : IsIrreducible (F.terminalRepresentation.comp (F.terminalDot K).subtype)
  · exact hK.alternatingSixNaturalAction_of_irreducible
      hG T hempty hM hu hmany hcard e F hne g hgP hgH e6 hi
  · obtain ⟨I,hI,hv,hp⟩ := source_terminal_a6_proper_point_of_small_actor
      hG T hempty hM hu hmany hcard e F hnot hne g hgP hgH hK e6 hyp hsmall hi
    exact hK.alternatingSixNaturalAction_of_coordinates hG e6
      (source_terminal_a6_coordinates_of_proper_constituent
        hG T hempty hM hu hmany hcard e F hnot hne g hgP hgH hK e6 hyp hI hv hp)

/-- The actual small-actor A₆ branch of 14.3.15 is impossible. Both the
natural-action and radical/two-core premises of the cubic-parabolic sieve are
proved from the original source hypotheses. -/
theorem source_terminal_a6_false_of_small_actor
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {K : Subgroup G} (hK : ComponentLift F g K)
    (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6))
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hsmall : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      finrank (ZMod 2) (Additive F.Uhat) / 2 - 1)
    : False := by
  exact source_terminal_a6_false_of_small_actor_and_action
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hyp hsmall hK e6
    (source_terminal_a6_natural_action_of_small_actor
      hG T hempty hM hu hmany hcard e F hnot hne g hgP hgH hK e6 hyp hsmall)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
