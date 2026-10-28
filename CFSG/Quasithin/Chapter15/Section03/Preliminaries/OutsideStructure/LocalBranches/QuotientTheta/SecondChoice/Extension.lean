module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.QuotientTheta.SecondChoice.Core
public import Theory.GroupAction.ElementaryNineFourSemidirect

/-!
# The actual extraspecial second-choice extension

The images of Y₊ and S in (Y₊S)/O₂(Y₊S) are complementary subgroups of
orders nine and four. Normality of Y₊ identifies the first image with its
intrinsic two-core quotient. The already proved R=C_T(V) identifies the
second image with the natural image of S.

The two identifications are checked on representatives, so their
conjugation action is exactly `selectedPlaneAction`, including its action
on the central line. This constructs the literal quotient as the selected
semidirect product. The intrinsic elementary-nine by four recognition then
gives S₃×S₃. No complement, action compatibility, or current quotient is an
extra premise of the exported theorems.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
the second-choice proof of 15.3.11(5i), printed p.1124, using 15.3.7(2).
-/

public section

open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches.QuotientTheta
open FusionCore.CosetSetup.ExtraspecialLocal
variable {G : Type*} [Group G] [Finite G]

private theorem chosen_quotient_restrict_kernel (d : CharacteristicTwo.LocalData G) :
    ((QuotientGroup.mk' (pCore 2 ↥(d.Yplus ⊔ d.S))).comp
      (inclusion (show d.Yplus ≤ d.Yplus ⊔ d.S from le_sup_left))).ker =
      pCore 2 d.Yplus := by
  let H := d.Yplus ⊔ d.S
  let i : d.Yplus →* H := inclusion le_sup_left
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  ext y
  constructor
  · intro hy
    have hcomp : IsPGroup 2 ((pCore 2 H).comap i) :=
      pCore_isPGroup.comap_of_injective i (inclusion_injective _)
    have hnormal : ((pCore 2 H).comap i : Subgroup d.Yplus).Normal := inferInstance
    have hsub : (pCore 2 H).comap i ≤ pCore 2 d.Yplus := le_sSup ⟨hnormal, hcomp⟩
    exact hsub hy
  · intro hy
    have hn : H ≤ normalizer (d.Yplus : Set G) :=
      (sup_le_sup_right (choice_le d.M d.Y d.S d.V₁ d.Yplus d.choice) _).trans
        (ys_normalizes_yplus d)
    have hp : d.Yplus.pCoreIn 2 ≤ H.pCoreIn 2 :=
      le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _)
        ((pCoreIn_le 2 _).trans le_sup_left)
        (hn.trans (normalizer_le_normalizer_characteristic_image _ _))
    change (i y : H) ∈ pCore 2 H
    obtain ⟨x, hx, he⟩ := hp (mem_map_of_mem d.Yplus.subtype hy)
    exact (Subtype.ext he : x = i y) ▸ hx

omit [Finite G] in
private theorem chosen_sylow_quotient_kernel (d : CharacteristicTwo.LocalData G)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    ((QuotientGroup.mk' (pCore 2 ↥(d.Yplus ⊔ d.S))).comp
      (inclusion (show d.S ≤ d.Yplus ⊔ d.S from le_sup_right))).ker =
      (selectedSylowProjection d).ker := by
  let H := d.Yplus ⊔ d.S
  let i : d.S →* H := inclusion le_sup_right
  ext s
  change (QuotientGroup.mk' (pCore 2 H)) (i s) = 1 ↔ selectedSylowProjection d s = 1
  have he : i s ∈ pCore 2 H ↔ (s : G) ∈ d.R := by
    constructor
    · intro hs
      exact ⟨i s, hs, rfl⟩
    · rintro ⟨x, hx, he⟩
      exact (Subtype.ext he : x = i s) ▸ hx
  have ha : selectedSylowProjection d s = 1 ↔
      (s : G) ∈ centralizer (d.V : Set G) := by
    rw [show selectedSylowProjection d s = 1 ↔
      (⟨s, d.sylow_le s.property.1⟩ : d.M) ∈ d.action.actor.ker by
        exact Subtype.ext_iff, d.action.ker_actor]
    rfl
  exact (QuotientGroup.eq_one_iff (N := pCore 2 H) (i s)).trans
    (he.trans ((by
      rw [hR]
      change ((s : G) ∈ (d.T : Subgroup G) ∧ (s : G) ∈ centralizer (d.V : Set G)) ↔ _
      exact (and_iff_right s.property.1).trans ha.symm) :
      ((s : G) ∈ d.R ↔ selectedSylowProjection d s = 1)))

private theorem chosen_yplus_normal (d : CharacteristicTwo.LocalData G) :
    (d.Yplus.subgroupOf (d.Yplus ⊔ d.S)).Normal := by
  apply normal_subgroupOf_iff_le_normalizer le_sup_left |>.mpr
  exact (sup_le_sup_right (choice_le d.M d.Y d.S d.V₁ d.Yplus d.choice) _).trans
    (ys_normalizes_yplus d)

private noncomputable def chosen_core_quotient_equiv_image
    (d : CharacteristicTwo.LocalData G) :
    (d.Yplus ⧸ pCore 2 d.Yplus) ≃*
      ((QuotientGroup.mk' (pCore 2 ↥(d.Yplus ⊔ d.S))).comp
        (inclusion (show d.Yplus ≤ d.Yplus ⊔ d.S from le_sup_left))).range :=
  (QuotientGroup.quotientMulEquivOfEq (chosen_quotient_restrict_kernel d).symm).trans
    (QuotientGroup.quotientKerEquivRange _)

private noncomputable def chosen_image_equiv_selected (d : CharacteristicTwo.LocalData G)
    (h : ExtraspecialCase d.M d.Y d.V) :
    ((QuotientGroup.mk' (pCore 2 ↥(d.Yplus ⊔ d.S))).comp
      (inclusion (show d.Yplus ≤ d.Yplus ⊔ d.S from le_sup_left))).range ≃*
      selectedThreeSubgroup d := by
  let _ := h.extraspecial
  exact (chosen_core_quotient_equiv_image d).symm.trans
    (selectedQuotientEquiv d (IsExtraspecial.isPGroup 3 _))


private noncomputable def chosen_image_equiv_selectedSylow (d : CharacteristicTwo.LocalData G)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    ((QuotientGroup.mk' (pCore 2 ↥(d.Yplus ⊔ d.S))).comp
      (inclusion (show d.S ≤ d.Yplus ⊔ d.S from le_sup_right))).range ≃*
      d.action.image d.S := by
  let qS := (QuotientGroup.mk' (pCore 2 ↥(d.Yplus ⊔ d.S))).comp
      (inclusion (show d.S ≤ d.Yplus ⊔ d.S from le_sup_right))
  let p := selectedSylowProjection d
  let e0 := QuotientGroup.quotientKerEquivRange qS
  let e1 := QuotientGroup.quotientKerEquivOfSurjective p
    (selectedSylowProjection_surjective d)
  let eK : (d.S ⧸ qS.ker) ≃* (d.S ⧸ p.ker) :=
    QuotientGroup.quotientMulEquivOfEq (chosen_sylow_quotient_kernel d hR)
  exact e0.symm.trans (eK.trans e1)

private theorem chosen_image_normal (d : CharacteristicTwo.LocalData G) :
    (((QuotientGroup.mk' (pCore 2 ↥(d.Yplus ⊔ d.S))).comp
      (inclusion (show d.Yplus ≤ d.Yplus ⊔ d.S from le_sup_left))).range).Normal := by
  let H := d.Yplus ⊔ d.S
  let N := d.Yplus.subgroupOf H
  let _ : N.Normal := chosen_yplus_normal d
  have hn : N.Normal := chosen_yplus_normal d
  have hrange : (inclusion (show d.Yplus ≤ H from le_sup_left)).range = N := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [MonoidHom.range_comp, hrange]
  exact hn.map (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)

private theorem chosen_image_complement (d : CharacteristicTwo.LocalData G)
    (hsecond : OutsideStructure.SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (h : ExtraspecialCase d.M d.Y d.V) :
    IsComplement' (((QuotientGroup.mk' (pCore 2 ↥(d.Yplus ⊔ d.S))).comp
      (inclusion (show d.Yplus ≤ d.Yplus ⊔ d.S from le_sup_left))).range)
      (((QuotientGroup.mk' (pCore 2 ↥(d.Yplus ⊔ d.S))).comp
      (inclusion (show d.S ≤ d.Yplus ⊔ d.S from le_sup_right))).range) := by
  let H := d.Yplus ⊔ d.S
  let q := QuotientGroup.mk' (pCore 2 H)
  let qY := q.comp (inclusion (show d.Yplus ≤ H from le_sup_left))
  let qS := q.comp (inclusion (show d.S ≤ H from le_sup_right))
  let E := qY.range
  let D := qS.range
  have hsup : d.Yplus.subgroupOf H ⊔ d.S.subgroupOf H = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right]
    rw [show Subgroup.map H.subtype ⊤ = H by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, trivial, rfl⟩]
  have hrange : (inclusion (show d.Yplus ≤ H from le_sup_left)).range =
      d.Yplus.subgroupOf H := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hE_map : E = (d.Yplus.subgroupOf H).map q := by
    change qY.range = _
    rw [MonoidHom.range_comp, hrange]
  have hrangeS : (inclusion (show d.S ≤ H from le_sup_right)).range =
      d.S.subgroupOf H := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hD_map : D = (d.S.subgroupOf H).map q := by
    change qS.range = _
    rw [MonoidHom.range_comp, hrangeS]
  have hgen : E ⊔ D = ⊤ := by
    rw [hE_map, hD_map, ← Subgroup.map_sup, hsup,
      map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hE : Nat.card E = 9 := by
    have he := Nat.card_congr (chosen_image_equiv_selected d h).toEquiv
    rw [selectedThreeSubgroup_card d hsecond h7image h] at he
    change Nat.card (((QuotientGroup.mk' (pCore 2 ↥(d.Yplus ⊔ d.S))).comp
      (inclusion (show d.Yplus ≤ d.Yplus ⊔ d.S from le_sup_left))).range) = 9
    exact he
  have hD : Nat.card D = 4 := by
    have he := Nat.card_congr (chosen_image_equiv_selectedSylow d hR).toEquiv
    rw [selectedSylowImage_card] at he
    change Nat.card (((QuotientGroup.mk' (pCore 2 ↥(d.Yplus ⊔ d.S))).comp
      (inclusion (show d.S ≤ d.Yplus ⊔ d.S from le_sup_right))).range) = 4
    exact he
  let _ : E.Normal := chosen_image_normal d
  have hprod : (E : Set (H ⧸ pCore 2 H)) * (D : Set (H ⧸ pCore 2 H)) = Set.univ := by
    rw [← Subgroup.normal_mul E D, hgen]
    rfl
  exact isComplement'_of_disjoint_and_mul_eq_univ
    (disjoint_of_coprime_natCard (by rw [hE, hD]; decide)) hprod


private noncomputable def chosenYImage (d : CharacteristicTwo.LocalData G) :
    Subgroup ((↥(d.Yplus ⊔ d.S)) ⧸ pCore 2 ↥(d.Yplus ⊔ d.S)) :=
  ((QuotientGroup.mk' (pCore 2 ↥(d.Yplus ⊔ d.S))).comp
    (inclusion (show d.Yplus ≤ d.Yplus ⊔ d.S from le_sup_left))).range

private noncomputable def chosenSImage (d : CharacteristicTwo.LocalData G) :
    Subgroup ((↥(d.Yplus ⊔ d.S)) ⧸ pCore 2 ↥(d.Yplus ⊔ d.S)) :=
  ((QuotientGroup.mk' (pCore 2 ↥(d.Yplus ⊔ d.S))).comp
    (inclusion (show d.S ≤ d.Yplus ⊔ d.S from le_sup_right))).range

private noncomputable def chosenYImageEquivSelected (d : CharacteristicTwo.LocalData G)
    (h : ExtraspecialCase d.M d.Y d.V) : chosenYImage d ≃* selectedThreeSubgroup d :=
  chosen_image_equiv_selected d h

private noncomputable def chosenSImageEquivActor (d : CharacteristicTwo.LocalData G)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    chosenSImage d ≃* d.action.image d.S :=
  chosen_image_equiv_selectedSylow d hR

private noncomputable def chosenImageAction (d : CharacteristicTwo.LocalData G) :
    chosenSImage d →* MulAut (chosenYImage d) := by
  let _ : (chosenYImage d).Normal := chosen_image_normal d
  exact (chosenYImage d).normalizerMonoidHom.comp
    (inclusion (show chosenSImage d ≤ normalizer (chosenYImage d : Set ((↥(d.Yplus ⊔ d.S)) ⧸ pCore 2 ↥(d.Yplus ⊔ d.S))) by
      rw [normalizer_eq_top (H := chosenYImage d)]
      exact le_top))


private theorem chosen_semidirect_of_compatibility
    (d : CharacteristicTwo.LocalData G)
    (hsecond : OutsideStructure.SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hcore : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (h : ExtraspecialCase d.M d.Y d.V)
    (hcompat : ∀ (z : chosenSImage d) (x : selectedThreeSubgroup d),
      chosenYImageEquivSelected d h
        (chosenImageAction d z ((chosenYImageEquivSelected d h).symm x)) =
      selectedPlaneAction d hcore
        (chosenSImageEquivActor d hR z) x) :
    Nonempty ((↥(d.Yplus ⊔ d.S) ⧸ pCore 2 ↥(d.Yplus ⊔ d.S)) ≃*
      (selectedThreeSubgroup d ⋊[selectedPlaneAction d hcore] d.action.image d.S)) := by
  let eE := chosenYImageEquivSelected d h
  let eD := chosenSImageEquivActor d hR
  have hmap : ∀ z : chosenSImage d,
      (chosenImageAction d z).trans eE =
        eE.trans (selectedPlaneAction d hcore (eD z)) := by
    intro z
    apply MulEquiv.ext
    intro x
    have hh := hcompat z (eE x)
    simpa only [eE, eD, MulEquiv.symm_apply_apply, MulEquiv.trans_apply] using hh
  let me := SemidirectProduct.congr eE eD hmap
  let _ : (chosenYImage d).Normal := chosen_image_normal d
  let qeq := SemidirectProduct.mulEquivSubgroup (H := chosenYImage d) (K := chosenSImage d)
    (chosen_image_complement d hsecond h7image hR h)
  exact ⟨qeq.symm.trans me⟩

private theorem chosen_image_equiv_selected_apply (d : CharacteristicTwo.LocalData G)
    (h : ExtraspecialCase d.M d.Y d.V) (y : d.Yplus) :
    chosenYImageEquivSelected d h
      ⟨(QuotientGroup.mk' (pCore 2 ↥(d.Yplus ⊔ d.S)))
        ⟨y, (le_sup_left : d.Yplus ≤ d.Yplus ⊔ d.S) y.property⟩, ⟨y, rfl⟩⟩ = selectedQuotientMap d y := by
  let _ := h.extraspecial
  let qY := (QuotientGroup.mk' (pCore 2 ↥(d.Yplus ⊔ d.S))).comp
    (inclusion (show d.Yplus ≤ d.Yplus ⊔ d.S from le_sup_left))
  have hy : (chosen_core_quotient_equiv_image d).symm
      (⟨qY y, ⟨y, rfl⟩⟩ : qY.range) = QuotientGroup.mk' (pCore 2 d.Yplus) y := by
    apply (chosen_core_quotient_equiv_image d).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  change ((selectedQuotientEquiv d (IsExtraspecial.isPGroup 3 _))
    ((chosen_core_quotient_equiv_image d).symm ⟨qY y, ⟨y, rfl⟩⟩)).val = _
  rw [hy]
  rfl

omit [Finite G] in
private theorem chosen_image_equiv_actor_apply (d : CharacteristicTwo.LocalData G)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) (s : d.S) :
    chosenSImageEquivActor d hR
      ⟨(QuotientGroup.mk' (pCore 2 ↥(d.Yplus ⊔ d.S)))
        ⟨s, (le_sup_right : d.S ≤ d.Yplus ⊔ d.S) s.property⟩, ⟨s, rfl⟩⟩ = selectedSylowProjection d s := by
  dsimp [chosenSImageEquivActor, chosen_image_equiv_selectedSylow, chosenSImage]
  let qS := (QuotientGroup.mk' (pCore 2 ↥(d.Yplus ⊔ d.S))).comp
      (inclusion (show d.S ≤ d.Yplus ⊔ d.S from le_sup_right))
  let p := selectedSylowProjection d
  let e0 := QuotientGroup.quotientKerEquivRange qS
  let e1 := QuotientGroup.quotientKerEquivOfSurjective p (selectedSylowProjection_surjective d)
  let eK : (d.S ⧸ qS.ker) ≃* (d.S ⧸ p.ker) :=
    QuotientGroup.quotientMulEquivOfEq (chosen_sylow_quotient_kernel d hR)
  have hs : e0.symm (⟨qS s, ⟨s, rfl⟩⟩ : qS.range) = QuotientGroup.mk' qS.ker s := by
    apply e0.injective
    rw [e0.apply_symm_apply]
    rfl
  change e1 (eK (e0.symm ⟨qS s, ⟨s, rfl⟩⟩)) = p s
  rw [hs]
  rfl

private theorem chosen_action_compatibility
    (d : CharacteristicTwo.LocalData G)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hcore : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (h : ExtraspecialCase d.M d.Y d.V) :
    ∀ (z : chosenSImage d) (x : selectedThreeSubgroup d),
      chosenYImageEquivSelected d h
        (chosenImageAction d z ((chosenYImageEquivSelected d h).symm x)) =
      selectedPlaneAction d hcore
        (chosenSImageEquivActor d hR z) x := by
  let H := d.Yplus ⊔ d.S
  let q := QuotientGroup.mk' (pCore 2 ↥H)
  let qY := q.comp (inclusion (show d.Yplus ≤ H from le_sup_left))
  let qS := q.comp (inclusion (show d.S ≤ H from le_sup_right))
  intro z x
  obtain ⟨s, hs⟩ := z.property
  have hz : z = (⟨qS s, ⟨s, rfl⟩⟩ : chosenSImage d) := Subtype.ext hs.symm
  subst z
  obtain ⟨y, hyx⟩ := x.property
  have hx : x = (⟨selectedQuotientMap d y, ⟨y, rfl⟩⟩ : selectedThreeSubgroup d) :=
    Subtype.ext hyx.symm
  subst x
  have hy : chosenYImageEquivSelected d h
      (⟨qY y, ⟨y, rfl⟩⟩ : chosenYImage d) =
      (⟨selectedQuotientMap d y, ⟨y, rfl⟩⟩ : selectedThreeSubgroup d) := by
    apply Subtype.ext
    exact chosen_image_equiv_selected_apply d h y
  have hs : chosenSImageEquivActor d hR
      (⟨qS s, ⟨s, rfl⟩⟩ : chosenSImage d) =
      selectedSylowProjection d s := by
    apply Subtype.ext
    exact congrArg Subtype.val (chosen_image_equiv_actor_apply d hR s)
  have hyinv : (chosenYImageEquivSelected d h).symm
      (⟨selectedQuotientMap d y, ⟨y, rfl⟩⟩ : selectedThreeSubgroup d) =
      (⟨qY y, ⟨y, rfl⟩⟩ : chosenYImage d) := by
    apply (chosenYImageEquivSelected d h).injective
    rw [MulEquiv.apply_symm_apply, hy]
  rw [hyinv, hs]
  let y' := d.Yplus.normalizerMonoidHom
      ⟨s, ys_normalizes_yplus d (mem_sup_right s.property)⟩ y
  have hact :
      chosenImageAction d (⟨qS s, ⟨s, rfl⟩⟩ : chosenSImage d)
        (⟨qY y, ⟨y, rfl⟩⟩ : chosenYImage d) =
      (⟨qY y', ⟨y', rfl⟩⟩ : chosenYImage d) := by
    apply Subtype.ext
    simp [chosenImageAction, Subgroup.normalizerMonoidHom,
      MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply,
      HSMul.hSMul, y']
    rfl
  rw [hact]
  apply Subtype.ext
  have hright :
      ((selectedPlaneAction d hcore (selectedSylowProjection d s))
        (⟨selectedQuotientMap d y, ⟨y, rfl⟩⟩ : selectedThreeSubgroup d)).val =
      (selectedQuotientMap d y') := by
    rw [selectedPlaneAction]
    exact selectedSylowAction_on_selected d hcore s y
  rw [hright]
  convert (chosen_image_equiv_selected_apply d h y') using 1
  apply congrArg Subtype.val
  apply congrArg (chosenYImageEquivSelected d h)
  apply Subtype.ext
  rfl

/-- The actual second-choice core quotient realizes the previously constructed
selected action. Both the complement and action compatibility are proved here. -/
theorem second_choice_extraspecial_semidirect_quotient
    (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus)
    (hsecond : OutsideStructure.SecondChoice d)
    (hcore : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h : ExtraspecialCase d.M d.Y d.V)
    (hSylow : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S) :
    Nonempty ((↥(d.Yplus ⊔ d.S) ⧸ pCore 2 ↥(d.Yplus ⊔ d.S)) ≃*
      (selectedThreeSubgroup d ⋊[selectedPlaneAction d hcore] d.action.image d.S)) := by
  have hR := second_choice_extraspecial_core d I hI hsecond hcore h7image h hSylow
  exact chosen_semidirect_of_compatibility d hsecond h7image hR hcore h
    (chosen_action_compatibility d hR hcore h)

/-- In the extraspecial earlier alternative, Y₊/O₂(Y₊) is elementary nine,
and the stronger literal O₂ quotient of Y₊S is S₃×S₃, with R=C_T(V).
This discharges the quotient-recognition step of the second-choice proof of
15.3.11(5i), without assuming a rank-two case or a current quotient. -/
theorem second_choice_extraspecial_quotient_and_core
    (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus)
    (hsecond : OutsideStructure.SecondChoice d)
    (hcore : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h : ExtraspecialCase d.M d.Y d.V)
    (hSylow : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S) :
    Nonempty ((d.Yplus ⧸ pCore 2 d.Yplus) ≃* Multiplicative (Fin 2 → ZMod 3)) ∧
      Nonempty ((↥(d.Yplus ⊔ d.S) ⧸ pCore 2 ↥(d.Yplus ⊔ d.S)) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G) := by
  let _ := selectedThreeSubgroup_elementary d hsecond h7image h
  let _ := selectedSylowImage_elementary d
  obtain ⟨eq⟩ := second_choice_extraspecial_semidirect_quotient
    d I hI hsecond hcore h7image h hSylow
  obtain ⟨es⟩ := ElementaryNineFourSemidirect.nonempty_mulEquiv
    (selectedPlaneAction d hcore)
    (selectedThreeSubgroup_card d hsecond h7image h)
    (selectedSylowImage_card d)
    (selectedPlaneAction_injective d hsecond hcore h7image h)
    (selectedCentralLine d)
    (selectedCentralLine_card d hsecond h7image h)
    (selectedCentralLine_stable d hcore)
  exact ⟨second_choice_extraspecial_selected_quotient d hsecond h7image h,
    ⟨eq.trans es⟩, second_choice_extraspecial_core d I hI hsecond hcore h7image h hSylow⟩

end CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches.QuotientTheta

end
