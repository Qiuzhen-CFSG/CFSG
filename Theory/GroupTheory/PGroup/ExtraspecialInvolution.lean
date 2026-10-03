module

public import Theory.GroupTheory.PGroup.ClassTwoCyclicCenter
public import Theory.GroupTheory.PGroup.PrimeCubeCenter
public import Theory.GroupTheory.PGroup.ExtraspecialCentralizer
public import Theory.GroupTheory.DihedralPresentation
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# Splitting a dihedral factor from an extraspecial two-group

A noncentral involution in a finite extraspecial two-group inverts a suitable
rotation of order four. They generate a dihedral subgroup of order eight that
contains the ambient center. Its own center has order two, so these centers
agree inside the ambient group. Commutator duality then splits off this
subgroup with its centralizer as supplement.

To find the rotation, choose an element not commuting with the involution.
If it has order four, use it; if it has order two, use its product with the
involution. The nontrivial commutator is the unique central involution.

Sources: GLS2, Chapter C, Proposition 10.4; Gorenstein, *Finite Groups*,
Sections 5.4–5.5.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative

/-- Every square in an extraspecial binary group is central. -/
public theorem IsExtraspecial.square_mem_center
    {P : Type*} [Group P] [IsExtraspecial 2 P] (x : P) : x ^ 2 ∈ center P :=
  (IsExtraspecial.quotient_elementary_abelian 2 P).sq_mem_center_of_central_quotient x

/-- An extraspecial binary group has exponent dividing four. -/
public theorem IsExtraspecial.pow_four_eq_one
    {P : Type*} [Group P] [IsExtraspecial 2 P] (x : P) : x ^ 4 = 1 := by
  have h := congrArg Subtype.val
    (pow_card_eq_one' (x := (⟨x ^ 2, IsExtraspecial.square_mem_center x⟩ : center P)))
  simpa only [IsExtraspecial.center_order_p 2 P, SubmonoidClass.coe_pow,
    OneMemClass.coe_one, ← pow_mul] using h

private theorem rotation_of_noncentral_involution
    {P : Type*} [Group P] [IsExtraspecial 2 P]
    (t : P) (ht : t ^ 2 = 1) (htZ : t ∉ center P) :
    ∃ a : P, orderOf a = 4 ∧ t * a * t⁻¹ = a⁻¹ := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ht)
  obtain ⟨y, hy⟩ : ∃ y : P, y * t ≠ t * y := by
    simpa only [mem_center_iff, not_forall] using htZ
  have horder {a : P} (ha : a ^ 2 ≠ 1) : orderOf a = 4 := by
    exact orderOf_eq_prime_pow (p := 2) (n := 1) ha (IsExtraspecial.pow_four_eq_one a)
  by_cases hy2 : y ^ 2 = 1
  · have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hy2)
    refine ⟨y * t, horder ?_, ?_⟩
    · intro he
      have hi : (y * t)⁻¹ = y * t := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using he)
      simp only [mul_inv_rev, hti, hyi] at hi
      exact hy hi.symm
    · simp only [mul_inv_rev, hti, hyi, mul_assoc]
      rw [← pow_two, ht, mul_one]
  · have hc : ⁅t, y⁆ ∈ center P :=
      (IsExtraspecial.quotient_elementary_abelian 2 P).commutator_le_center_of_central_quotient
        (commutator_mem_commutator (mem_top t) (mem_top y))
    have hcne : ⁅t, y⁆ ≠ 1 := fun h => hy
      (commutatorElement_eq_one_iff_mul_comm.mp h).symm
    obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : center P)).mp
      (IsExtraspecial.center_order_p 2 P)
    have hceq : ⁅t, y⁆ = y ^ 2 := congrArg Subtype.val
      ((hz ⟨⁅t, y⁆, hc⟩ (fun h => hcne (congrArg Subtype.val h))).trans
        (hz ⟨y ^ 2, IsExtraspecial.square_mem_center y⟩
          (fun h => hy2 (congrArg Subtype.val h))).symm)
    refine ⟨y, horder hy2, ?_⟩
    calc
      t * y * t⁻¹ = ⁅t, y⁆ * y := by
        simp only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one]
      _ = y ^ 2 * y := by rw [hceq]
      _ = y⁻¹ := by
        apply mul_right_cancel (b := y)
        simpa only [pow_succ, pow_zero, one_mul, inv_mul_cancel] using
          IsExtraspecial.pow_four_eq_one y

/-- A noncentral involution in an extraspecial binary group lies in a dihedral
factor of order eight whose centralizer supplements it. -/
public theorem IsExtraspecial.exists_dihedral_factor_of_noncentral_involution
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (t : P) (ht : t ^ 2 = 1) (htZ : t ∉ center P) :
    ∃ D : Subgroup P, Nonempty (D ≃* DihedralGroup 4) ∧ center P ≤ D ∧
      D ⊔ centralizer (D : Set P) = ⊤ := by
  obtain ⟨a, ha, hinv⟩ := rotation_of_noncentral_involution t ht htZ
  have ha2 : a ^ 2 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [ha] at hd
    norm_num at hd
  have htout : t ∉ zpowers a := by
    intro h
    have hc : Commute t a := by
      obtain ⟨k, rfl⟩ := h
      exact (Commute.refl a).zpow_left k
    have he : a = a⁻¹ := by simpa only [hc.eq, mul_inv_cancel_right] using hinv
    apply ha2
    simpa only [pow_two] using (congrArg (fun x : P => x * a) he).trans (inv_mul_cancel a)
  have hn : t ∈ normalizer (zpowers a : Set P) := by
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (t * a * t⁻¹) = zpowers a
    rw [hinv, zpowers_inv]
  let D := zpowers a ⊔ zpowers t
  have hcard : Nat.card D = 8 := by
    rw [card_sup_zpowers_of_normalizing_involution (zpowers a) t ht htout hn,
      Nat.card_zpowers, ha]
  have haD : a ∈ D := mem_sup_left (mem_zpowers a)
  have htD : t ∈ D := mem_sup_right (mem_zpowers t)
  let aD : D := ⟨a, haD⟩
  let tD : D := ⟨t, htD⟩
  have hgen : closure ({aD, tD} : Set D) = ⊤ := by
    apply map_injective D.subtype_injective
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      ← MonoidHom.range_eq_map, D.range_subtype]
    change closure ({a, t} : Set P) = zpowers a ⊔ zpowers t
    rw [← Set.singleton_union, Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure]
  have hmodel : Nonempty (D ≃* DihedralGroup 4) :=
    dihedralGroup_equiv_of_presentation (by decide) aD tD
      ((Subgroup.orderOf_coe aD).symm.trans ha)
      (Subtype.ext ht) (Subtype.ext hinv) hgen hcard
  have hZD : center P ≤ D := by
    have heq : zpowers (a ^ 2) = center P := by
      apply eq_of_le_of_card_ge (zpowers_le.mpr (IsExtraspecial.square_mem_center a))
      rw [Nat.card_zpowers, orderOf_pow, ha, IsExtraspecial.center_order_p 2 P]
      decide
    rw [← heq]
    exact zpowers_le.mpr (D.pow_mem haD 2)
  have hnonab : ¬ IsMulCommutative D := by
    intro h
    let : IsMulCommutative D := h
    have he : a = a⁻¹ := by
      have hcomm : t * a = a * t := congrArg Subtype.val (mul_comm tD aD)
      simpa only [hcomm, mul_inv_cancel_right] using hinv
    exact ha2 (by simpa only [pow_two] using
      (congrArg (fun x : P => x * a) he).trans (inv_mul_cancel a))
  have hcenter : Nat.card (center D) = 2 :=
    card_center_eq_prime_of_card_eq_prime_cube (p := 2) hcard hnonab
  have himage : (center D).map D.subtype = center P := by
    apply (eq_of_le_of_card_ge ?_ ?_).symm
    · intro x hx
      refine ⟨⟨x, hZD hx⟩, ?_, rfl⟩
      exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hx y))
    · rw [card_map_of_injective D.subtype_injective, hcenter,
        IsExtraspecial.center_order_p 2 P]
  let : IsExtraspecial 2 D := {
    center_order_p := hcenter
    quotient_elementary_abelian :=
      (IsExtraspecial.quotient_elementary_abelian 2 P).central_quotient_subgroup D
    quotient_nontrivial := QuotientGroup.nontrivial_iff.mpr
      (fun h => hnonab (center_eq_top_iff.mp h)) }
  refine ⟨D, hmodel, hZD, sup_centralizer_eq_top_of_extraspecial_two D ?_⟩
  rw [himage]
  exact (commutator_mono le_rfl le_top).trans
    (IsExtraspecial.quotient_elementary_abelian 2 P).commutator_le_center_of_central_quotient
