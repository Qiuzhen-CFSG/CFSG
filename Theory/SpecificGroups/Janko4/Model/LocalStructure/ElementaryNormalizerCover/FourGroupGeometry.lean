module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.Symmetry
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators

/-!
# Native four-groups and the intrinsic elementary form

The certified first-centralizer census gives two generated native subgroups
covering pure-2A four-groups, with actual conjugators and full centralizer and
normalizer transport. Its intrinsic residual character singles out rows 4, 5
and 6 as the outer pairs. Rows 5 and 6 generate the same subgroup, leaving two
native nonsingular configurations whenever a first-class member is present.

Pure-2A elementary subgroups have zero intrinsic form. Consequently a nonzero
form supplies an actual second-class involution. The nonsingular consumer
places the full centralizer in a conjugate of one of the two generated
four-group centralizers. Their structural identification, the pure-second
four-group configuration and the subsequent order-256 geometry are separate
source obligations.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Table 1,
p.487, and the opening reductions of Sections 2.1 and 2.3, pp.488--492.
No new finite certificate is used: the actual word census, fusion and residual
comparisons are supplied by the imported native modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover
open Cardinality.LocalInvolutionCensus LargeCenterRadicals.OuterHalf
attribute [local irreducible] modelGroup matrixA matrixB

private theorem first_pair_lift (x y : Model) (hx : IsConj a x) (hc : Commute x y) :
    ∃ (g : Model) (u : H), (MulAut.conj g) a = x ∧
      (MulAut.conj g) (eH u) = y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hx
  let e := MulAut.conj g⁻¹
  have hx' : e x = a := by
    rw [← hg]
    simp [e, mul_assoc]
  have hc' : Commute a (e y) := by
    simpa only [MulEquiv.coe_toMonoidHom, hx'] using hc.map e.toMonoidHom
  let v : InvolutionCentralizers.First.centralizer :=
    ⟨e y, mem_centralizer_singleton_iff.mpr hc'.eq.symm⟩
  obtain ⟨u, hu⟩ := Cardinality.Thompson.max2EquivCentralizer.surjective v
  have hu' : eH u = e y := by
    simpa only [Cardinality.Thompson.max2EquivCentralizer_coe] using congrArg Subtype.val hu
  refine ⟨g, u, hg, ?_⟩
  rw [hu']
  simp [e, mul_assoc]

private theorem conjugate_pair_lift (g : Model) (u : H) (i : Fin 11)
    (hi : IsConj (representative i) u) :
    ∃ k : Model, (MulAut.conj k) a = (MulAut.conj g) a ∧
      (MulAut.conj k) (eH (representative i)) = (MulAut.conj g) (eH u) := by
  obtain ⟨k, hk⟩ := isConj_iff.mp hi
  have hka : (MulAut.conj (eH k)) a = a := by
    change eH k * a * (eH k)⁻¹ = a
    have hkz : eH k * a = a * eH k := (eH_commute_z k).eq
    rw [hkz, mul_inv_cancel_right]
  have hku : (MulAut.conj (eH k)) (eH (representative i)) = eH u := by
    simpa only [map_mul, map_inv, MulAut.conj_apply] using congrArg eH hk
  have hcomp (v : Model) : (MulAut.conj (g * eH k)) v =
      (MulAut.conj g) ((MulAut.conj (eH k)) v) := by simp [mul_assoc]
  exact ⟨g * eH k, by rw [hcomp, hka], by rw [hcomp, hku]⟩

/-- Two actual native representatives cover every marked pure first-class four-group. -/
theorem pure_first_pair_coverage (x y : Model) (hc : Commute x y)
    (hx : IsConj a x) (hy : IsConj a y) (hp : IsConj a (x * y)) :
    ∃ (i : Fin 11) (g : Model), (i = 2 ∨ i = 7) ∧
      (MulAut.conj g) a = x ∧ (MulAut.conj g) (eH (representative i)) = y := by
  obtain ⟨g, u, hxg, hyg⟩ := first_pair_lift x y hx hc
  have hyu : IsConj z (eH u) :=
    hy.trans (isConj_iff.mpr ⟨g, hyg⟩).symm
  have hpu : IsConj z (eH (u * zH)) := by
    apply hp.trans
    apply IsConj.symm
    apply isConj_iff.mpr
    refine ⟨g, ?_⟩
    change (MulAut.conj g) (eH (u * zH)) = x * y
    rw [map_mul, eH_zH, map_mul, hyg, hxg, hc.eq]
  have hu : u ∈ aa := ⟨hyu, hpu⟩
  have hcov := aa_coverage Cardinality.Thompson.max2_card.le hu
  suffices ∀ i : Fin 11, (i = 2 ∨ i = 7) → IsConj (representative i) u →
      ∃ (j : Fin 11) (k : Model), (j = 2 ∨ j = 7) ∧
        (MulAut.conj k) a = x ∧ (MulAut.conj k) (eH (representative j)) = y by
    rcases hcov with h | h
    · exact this 2 (Or.inl rfl) h
    · exact this 7 (Or.inr rfl) h
  intro i hi hconj
  obtain ⟨k, hka, hku⟩ := conjugate_pair_lift g u i hconj
  exact ⟨i, k, hi, hka.trans hxg, hku.trans hyg⟩

open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound Coordinates FusionCertificates

private theorem local_kernel_zero : localKernelProduct 0 = 1 := by
  change sourceSubgroupEquivLocal (kernelProduct 0) = 1
  simp [kernelProduct]

private theorem local_kernel_one : localKernelProduct 1 = zH := by
  have he : kernelProduct 1 = sourceSeed ^ 2 := by
    apply Subtype.ext
    apply toMatrix_injective
    change toMatrix (kernelProduct 1 : Model) = toMatrix (kernelFactor 0 : Model)
    rw [eval_kernel_1, KernelSeparation.eval_factor]
  change sourceSubgroupEquivLocal (kernelProduct 1) = zH
  rw [he, sourceEquiv_seed_sq]

private theorem representative_six : representative 6 = zH * representative 5 := by
  change localKernelProduct 1 * lift 2 = zH * (localKernelProduct 0 * lift 2)
  rw [local_kernel_one, local_kernel_zero, one_mul]

private theorem first_pair5_not_forward : ¬ InnerRelated a (eH (representative 5)) := by
  intro h5
  apply first_pair6_not_forward
  rw [representative_six, map_mul, eH_zH]
  exact ((solvableResidual (centralizer ({a} : Set Model))).map
    (centralizer ({a} : Set Model)).subtype).mul_mem (innerRelated_self a orderOf_a) h5

/-- Complete intrinsic inner/outer character for the eleven native first-centralizer rows. -/
theorem first_representative_inner_iff (i : Fin 11) :
    InnerRelated a (eH (representative i)) ↔ i ≠ 4 ∧ i ≠ 5 ∧ i ≠ 6 := by
  fin_cases i
  · have hz : eH (representative 0) = 1 :=
      isConj_one_right.mp (firstTarget_isConj_representative 0)
    apply iff_of_true _ (by decide)
    change InnerRelated a (eH (representative 0))
    rw [hz]
    exact ((solvableResidual _).map _).one_mem
  · have hz : representative 1 = zH := by
      change localKernelProduct 1 * lift 0 = zH
      have h0 : lift 0 = 1 := map_one sourceSubgroupEquivLocal
      rw [local_kernel_one, h0, mul_one]
    apply iff_of_true _ (by decide)
    change InnerRelated a (eH (representative 1))
    rw [hz, eH_zH]
    exact innerRelated_self a orderOf_a
  · exact iff_of_true first_pair_inner.1 (by decide)
  · exact iff_of_true (first_pair3_class_inner _ (IsConj.refl _)).1 (by decide)
  · exact iff_of_false first_pair4_not_forward (by decide)
  · exact iff_of_false first_pair5_not_forward (by decide)
  · exact iff_of_false first_pair6_not_forward (by decide)
  · exact iff_of_true first_pair7_forward (by decide)
  · exact iff_of_true first_pair8_forward (by decide)
  · exact iff_of_true (first_pair9_class_inner _ (IsConj.refl _)).1 (by decide)
  · exact iff_of_true first_pair10_forward (by decide)

/-- Nonsingular pairs with a first-class entry have precisely three marked rows.
Rows 5 and 6 are the two orientations of the same four-group. -/
theorem noninner_first_pair_coverage (x y : Model) (hx : IsConj a x)
    (hy : orderOf y = 2) (hc : Commute x y) (hn : ¬ InnerRelated x y) :
    ∃ (i : Fin 11) (g : Model), (i = 4 ∨ i = 5 ∨ i = 6) ∧
      (MulAut.conj g) a = x ∧ (MulAut.conj g) (eH (representative i)) = y := by
  obtain ⟨g, u, hxg, hyg⟩ := first_pair_lift x y hx hc
  have hs : u ^ 2 = 1 := by
    apply eH_injective
    apply (MulAut.conj g).injective
    rw [map_pow, map_one, map_pow, map_one, hyg]
    simpa only [hy] using pow_orderOf_eq_one y
  obtain ⟨i, hi⟩ := square_one_coverage Cardinality.Thompson.max2_card.le u hs
  have hni : ¬ InnerRelated a (eH (representative i)) := by
    intro h
    have hu := (innerRelated_first_class_iff hi).1.mp h
    have hg := innerRelated_map (MulAut.conj g).toMonoidHom hu
    exact hn (by simpa only [MulEquiv.coe_toMonoidHom, hxg, hyg] using hg)
  have hic : i = 4 ∨ i = 5 ∨ i = 6 := by
    simpa only [first_representative_inner_iff, not_and_or, not_not] using hni
  obtain ⟨k, hka, hku⟩ := conjugate_pair_lift g u i hi
  exact ⟨i, k, hic, hka.trans hxg, hku.trans hyg⟩

/-- The literal four-group generated by the marked involution and a census row. -/
@[expose] def firstFourGroup (i : Fin 11) : Subgroup Model :=
  closure ({a, eH (representative i)} : Set Model)

private theorem pair_map (i : Fin 11) (g x y : Model)
    (hx : (MulAut.conj g) a = x) (hy : (MulAut.conj g) (eH (representative i)) = y) :
    (firstFourGroup i).map (MulAut.conj g).toMonoidHom = closure ({x, y} : Set Model) := by
  rw [firstFourGroup, MonoidHom.map_closure, Set.image_pair]
  exact congrArg Subgroup.closure (by rw [show (MulAut.conj g).toMonoidHom a = x from hx,
    show (MulAut.conj g).toMonoidHom (eH (representative i)) = y from hy])

private theorem four_group_generators (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hcard : Nat.card X = 4) :
    ∃ x ∈ X, ∃ y ∈ X, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y ∧ closure ({x, y} : Set Model) = X := by
  have hX : X ≠ ⊥ := by intro he; simp [he] at hcard
  obtain ⟨x0, hx01⟩ := (ne_bot_iff_exists_ne_one).mp hX
  let x : Model := x0
  have hx : x ∈ X := x0.property
  have hx1 : x ≠ 1 := fun he => hx01 (Subtype.ext he)
  have hx2 : orderOf x = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hx) hx1
  have hnot : ¬ X ≤ zpowers x := by
    intro h
    have hh := Nat.le_of_dvd (Nat.card_pos) (card_dvd_of_le h)
    rw [hcard, Nat.card_zpowers, hx2] at hh
    omega
  obtain ⟨y, hy, hyn⟩ := SetLike.not_le_iff_exists.mp hnot
  have hy1 : y ≠ 1 := by intro he; exact hyn (he ▸ (zpowers x).one_mem)
  have hxy : x ≠ y := by intro he; exact hyn (he ▸ mem_zpowers x)
  have hy2 : orderOf y = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hy) hy1
  have hcomm : Commute x y := congrArg Subtype.val (mul_comm (⟨x, hx⟩ : X) ⟨y, hy⟩)
  have hk := isKleinFour_closure_pair_of_orderOf x y hx2 hy2 hxy hcomm
  have hle : closure ({x, y} : Set Model) ≤ X := (closure_le _).mpr (by
    rintro v (rfl | rfl) <;> assumption)
  exact ⟨x, hx, y, hy, hx1, hy1, hxy, eq_of_le_of_card_ge hle (by rw [hcard, hk.card_four])⟩

/-- Every actual pure-2A four-group is conjugate to one of two generated native
subgroups. The same conjugator identifies its full centralizer and normalizer. -/
theorem pure_first_four_group_geometry (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hcard : Nat.card X = 4) (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x) :
    ∃ (i : Fin 11) (g : Model), (i = 2 ∨ i = 7) ∧
      X = (firstFourGroup i).map (MulAut.conj g).toMonoidHom ∧
      centralizer (X : Set Model) =
        (centralizer (firstFourGroup i : Set Model)).map (MulAut.conj g).toMonoidHom ∧
      normalizer (X : Set Model) =
        (normalizer (firstFourGroup i : Set Model)).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨x, hx, y, hy, hx1, hy1, hxy, hgen⟩ := four_group_generators X hcard
  have hc : Commute x y := congrArg Subtype.val (mul_comm (⟨x, hx⟩ : X) ⟨y, hy⟩)
  have hprod : x * y ≠ 1 := by
    intro he
    have hy2 : y * y = 1 := by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hy
    exact hxy (mul_right_cancel (he.trans hy2.symm))
  obtain ⟨i, g, hi, hxa, hya⟩ := pure_first_pair_coverage x y hc
    (hpure x hx hx1) (hpure y hy hy1) (hpure _ (X.mul_mem hx hy) hprod)
  have hmap := (pair_map i g x y hxa hya).trans hgen
  refine ⟨i, g, hi, hmap.symm, ?_, ?_⟩
  · rw [← hmap]
    exact (map_centralizer_equiv (firstFourGroup i : Set Model) (MulAut.conj g)).symm
  · rw [← hmap]
    exact (map_equiv_normalizer_eq (firstFourGroup i) (MulAut.conj g)).symm

private theorem firstFourGroup_six : firstFourGroup 6 = firstFourGroup 5 := by
  have hrep : eH (representative 6) = a * eH (representative 5) := by
    rw [representative_six, map_mul, eH_zH]
  have ha (i : Fin 11) : a ∈ firstFourGroup i := subset_closure (by simp)
  have hb (i : Fin 11) : eH (representative i) ∈ firstFourGroup i := subset_closure (by simp)
  apply le_antisymm <;> apply (closure_le _).mpr
  · rintro v (rfl | rfl)
    · exact ha 5
    · rw [hrep]; exact mul_mem (ha 5) (hb 5)
  · rintro v (rfl | rfl)
    · exact ha 6
    · have hh := mul_mem (ha 6) (hb 6)
      rw [hrep, ← mul_assoc, show a * a = 1 by simpa only [pow_two] using a_pow_two,
        one_mul] at hh
      exact hh

/-- The two nonsingular four-group configurations having a first-class member,
with literal ambient conjugation rather than an abstract isomorphism label. -/
theorem noninner_first_four_group_geometry (x y : Model) (hx : IsConj a x)
    (hy : orderOf y = 2) (hc : Commute x y) (hn : ¬ InnerRelated x y) :
    ∃ (i : Fin 11) (g : Model), (i = 4 ∨ i = 5) ∧
      closure ({x, y} : Set Model) = (firstFourGroup i).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨i, g, hi, hxa, hya⟩ := noninner_first_pair_coverage x y hx hy hc hn
  have he := (pair_map i g x y hxa hya).symm
  rcases hi with rfl | rfl | rfl
  · exact ⟨4, g, Or.inl rfl, he⟩
  · exact ⟨5, g, Or.inr rfl, he⟩
  · exact ⟨5, g, Or.inr rfl, by rwa [firstFourGroup_six] at he⟩

/-- The actual nonsingular elementary-subgroup consumer: a first-class member
selects one of the two native four-groups and places the full centralizer there. -/
theorem nonsingular_first_configuration (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hform : (intrinsicElementaryForm X).Nondegenerate)
    (x : Model) (hx : x ∈ X) (hxa : IsConj a x) :
    ∃ (i : Fin 11) (g : Model), (i = 4 ∨ i = 5) ∧
      (firstFourGroup i).map (MulAut.conj g).toMonoidHom ≤ X ∧
      centralizer (X : Set Model) ≤
        (centralizer (firstFourGroup i : Set Model)).map (MulAut.conj g).toMonoidHom := by
  have hx1 : x ≠ 1 := by
    intro he
    have ha : a = 1 := isConj_one_left.mp (he ▸ hxa)
    have ho := orderOf_a
    simp [ha] at ho
  let x0 : Additive X := Additive.ofMul ⟨x, hx⟩
  have hx0 : x0 ≠ 0 := fun he => hx1 (congrArg (fun w : Additive X => (w.toMul : Model)) he)
  have hex : ∃ y : Additive X, intrinsicElementaryForm X x0 y ≠ 0 := by
    by_contra! hn
    exact hx0 (hform.1 x0 hn)
  obtain ⟨y0, hy0⟩ := hex
  let y : Model := y0.toMul
  have hyX : y ∈ X := y0.toMul.property
  have hy1 : y ≠ 1 := by
    intro he
    apply hy0
    change outerValue x y = 0
    rw [he, outerValue_one_right]
  have hy2 : orderOf y = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hyX) hy1
  have hc : Commute x y := congrArg Subtype.val (mul_comm (⟨x, hx⟩ : X) y0.toMul)
  have hn : ¬ InnerRelated x y := by
    intro h
    exact hy0 ((outerValue_eq_zero_iff x y hx1).mpr h)
  obtain ⟨i, g, hi, hgen⟩ := noninner_first_four_group_geometry x y hxa hy2 hc hn
  have hle : (firstFourGroup i).map (MulAut.conj g).toMonoidHom ≤ X := by
    rw [← hgen]
    exact (closure_le _).mpr (by rintro v (rfl | rfl) <;> assumption)
  refine ⟨i, g, hi, hle, ?_⟩
  rw [map_centralizer_equiv]
  exact centralizer_le hle

/-- Every pure first-class four-group is orthogonal for the intrinsic form. -/
theorem pure_first_pair_inner (x y : Model) (hc : Commute x y)
    (hx : IsConj a x) (hy : IsConj a y) (hp : IsConj a (x * y)) :
    InnerRelated x y := by
  obtain ⟨i, g, hi, hxg, hyg⟩ := pure_first_pair_coverage x y hc hx hy hp
  have h : InnerRelated a (eH (representative i)) := by
    rcases hi with rfl | rfl
    · exact first_pair_inner.1
    · exact first_pair7_forward
  simpa only [MulEquiv.coe_toMonoidHom, hxg, hyg] using
    innerRelated_map (MulAut.conj g).toMonoidHom h

/-- In a pure first-class elementary subgroup, all pairs are inner-related. -/
theorem pure_first_outerValue_zero (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x) (x y : X) :
    outerValue x y = 0 := by
  by_cases hx : (x : Model) = 1
  · simp [hx]
  by_cases hy : (y : Model) = 1
  · simp [hy]
  apply (outerValue_eq_zero_iff _ _ hx).mpr
  by_cases hxy : x = y
  · subst y
    have hd := orderOf_dvd_of_pow_eq_one
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ x.property)
    exact innerRelated_self x ((Nat.prime_two.eq_one_or_self_of_dvd _ hd).resolve_left
      (by simpa using hx))
  · apply pure_first_pair_inner x y
    · exact congrArg Subtype.val (mul_comm x y)
    · exact hpure x x.property hx
    · exact hpure y y.property hy
    · apply hpure _ (X.mul_mem x.property y.property)
      intro he
      apply hxy
      apply Subtype.ext
      have hy2 : (y : Model) * y = 1 := by
        simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) _ y.property
      exact mul_right_cancel (he.trans hy2.symm)

/-- The zero-form assertion used at the start of KW Section 2.1. -/
theorem pure_first_intrinsicForm_zero (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x) : intrinsicElementaryForm X = 0 := by
  ext x y
  exact pure_first_outerValue_zero X hpure x.toMul y.toMul

/-- A subgroup that is not pure first-class contains a marked second-class involution. -/
theorem nonpure_contains_second (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x) :
    ∃ t ∈ X, orderOf t = 2 ∧ ¬ IsConj a t ∧
      IsConj ((a * b * a * b * b) ^ 5) t := by
  push Not at hn
  obtain ⟨t, ht, ht1, hnt⟩ := hn
  have hd := orderOf_dvd_of_pow_eq_one
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ ht)
  have ht2 : orderOf t = 2 := (Nat.prime_two.eq_one_or_self_of_dvd _ hd).resolve_left
    (by simpa using ht1)
  exact ⟨t, ht, ht2, hnt,
    (OuterReduction.involution_isConj_of_max1_odd_index
      OuterReduction.max1_odd_index_unconditional ht2).resolve_left hnt⟩

/-- A nonzero intrinsic form forces an actual second-class involution. -/
theorem nonzero_form_contains_second (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hform : intrinsicElementaryForm X ≠ 0) :
    ∃ t ∈ X, orderOf t = 2 ∧ ¬ IsConj a t ∧
      IsConj ((a * b * a * b * b) ^ 5) t :=
  nonpure_contains_second X (fun hp => hform (pure_first_intrinsicForm_zero X hp))

end Janko4.LocalStructure.ElementaryNormalizerCover
