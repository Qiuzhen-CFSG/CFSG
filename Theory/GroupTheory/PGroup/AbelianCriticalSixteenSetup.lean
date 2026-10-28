module

public import Theory.GroupTheory.PGroup.NormalEightCriticalSubgroup
public import Theory.GroupTheory.PGroup.NormalEightCentralAction
public import Theory.GroupTheory.PGroup.NormalEightC4SquareAction
public import Theory.GroupTheory.PGroup.C4SquareSelfCentralizing
public import Theory.GroupAction.C4SquareFixedKernel
public import Theory.GroupAction.C4SquareCThreeCentralizer
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# The congruence action of an abelian critical sixteen

An abelian critical subgroup is self-centralizing. If it is a C₄-square and
the ambient central omega has order four, absence of normal elementary eights
forces conjugation to fix its involutions. The congruence-kernel calculation
then makes the quotient by the critical subgroup elementary abelian.
In particular, an outside involution has central conjugation action. The
normal-eight obstruction forces it to invert an element of order four.

These are the initial reductions for the split and nonsplit index-four cores
in MacWilliams, Trans. AMS 150 (1970), Case 1.2, (xxi) and Lemma 3,
printed pp.380–382, DOI 10.1090/S0002-9947-1970-0276324-3.
-/

open Subgroup

namespace IsCriticalPSubgroup

variable {P : Type*} [Group P] [Finite P] {C : Subgroup P}

omit [Finite P] in
/-- An abelian critical subgroup equals its ambient centralizer. -/
public theorem centralizer_eq_self_of_abelian
    (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C] :
    centralizer (C : Set P) = C := by
  apply le_antisymm
  · rw [hC.centralizer_eq]
    exact map_subtype_le _
  · exact C.le_centralizer

private theorem action_fixes_square_one
    (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (e : C ≃* C4SquareExtension.Model) :
    letI : C.Characteristic := hC.characteristic
    ∀ g : P, ∀ x : C4SquareExtension.Model, x ^ 2 = 1 →
      MulAut.congr e (MulAut.conjNormal g) x = x := by
  let : C.Characteristic := hC.characteristic
  intro g x hx
  change e (MulAut.conjNormal g (e.symm x)) = x
  have hs : (e.symm x) ^ 2 = 1 := by rw [← map_pow, hx, map_one]
  rw [IsPGroup.conjNormal_fixed_of_square_eq_one_of_no_normal_eight
    hno hZ C hC.centralizer_eq_self_of_abelian.le g _ hs, e.apply_symm_apply]

/-- All ambient conjugation actions on an abelian critical C₄-square commute. -/
public theorem c4_square_conjugations_commute
    (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (e : C ≃* C4SquareExtension.Model) :
    letI : C.Characteristic := hC.characteristic
    ∀ g h : P, Commute (MulAut.conjNormal (H := C) g) (MulAut.conjNormal h) := by
  let : C.Characteristic := hC.characteristic
  intro g h
  apply Commute.of_map (MulAut.congr e).injective
  exact C4SquareExtension.commute_of_fix_square_one _ _
    (hC.action_fixes_square_one hno hZ e g)
    (hC.action_fixes_square_one hno hZ e h)

/-- Every ambient square lies in the abelian critical C₄-square. -/
public theorem square_mem_of_c4_square
    (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (e : C ≃* C4SquareExtension.Model) (g : P) : g ^ 2 ∈ C := by
  let : C.Characteristic := hC.characteristic
  let f : P →* MulAut C := MulAut.conjNormal
  rw [← conjNormal_ker_eq_of_selfCentralizing_abelian C
    hC.centralizer_eq_self_of_abelian.le]
  apply MonoidHom.mem_ker.mpr
  change f (g ^ 2) = 1
  rw [map_pow]
  apply (MulAut.congr e).injective
  rw [map_pow, map_one]
  exact C4SquareExtension.square_eq_one_of_fix_square_one _
    (hC.action_fixes_square_one hno hZ e g)

/-- The quotient by an abelian critical C₄-square is elementary abelian. -/
public theorem quotient_elementary_of_c4_square
    (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (e : C ≃* C4SquareExtension.Model) :
    letI : C.Characteristic := hC.characteristic
    IsElementaryAbelian 2 (P ⧸ C) := by
  let : C.Characteristic := hC.characteristic
  have hs (x : P ⧸ C) : x ^ 2 = 1 := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C x
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (N := C) _).mpr (hC.square_mem_of_c4_square hno hZ e g)
  refine {
    toIsMulCommutative := IsMulCommutative.of_comm ?_
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  intro x y
  have hi (z : P ⧸ C) : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hs z)
  calc
    x * y = (x * y)⁻¹ := (hi _).symm
    _ = y * x := by rw [mul_inv_rev, hi, hi]

/-- Every involution in the critical subgroup is ambiently central. -/
public theorem involution_mem_ambient_center
    (hC : IsCriticalPSubgroup 2 C)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    {x : P} (hx : x ∈ C) (hx2 : orderOf x = 2) : x ∈ center P := by
  exact map_subtype_le _ (hC.mem_omega_center_of_square_eq_one hno hZ hx
    (hx2 ▸ pow_orderOf_eq_one x))

/-- The elementary-subgroup rank bound follows from the actual action on the
critical C₄-square and the normal-eight exclusion. -/
public theorem elementary_card_le_sixteen_of_c4_square
    (hP : IsPGroup 2 P) (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (e : C ≃* C4SquareExtension.Model)
    (E : Subgroup P) [IsElementaryAbelian 2 E] : Nat.card E ≤ 16 := by
  let : C.Characteristic := hC.characteristic
  have hk := card_le_omega_one_mul_conj_image_of_elementary C
    hC.centralizer_eq_self_of_abelian.le E
  have hi := IsPGroup.conj_image_card_le_four_of_c4_square_of_no_normal_eight
    hP hno hZ C hC.centralizer_eq_self_of_abelian.le e E
  rw [hC.card_omega_one_eq_four hno hZ] at hk
  exact hk.trans (by simpa using Nat.mul_le_mul_left 4 hi)

/-- Every outside involution inverts a primitive element of the C₄-square.
This uses the normal-eight obstruction, without a generator-rank hypothesis. -/
public theorem exists_inverted_order_four_of_involution_not_mem
    (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (e : C ≃* C4SquareExtension.Model)
    {t : P} (ht : orderOf t = 2) (hout : t ∉ C) :
    ∃ c ∈ C, orderOf c = 4 ∧ t * c * t⁻¹ = c⁻¹ := by
  let : C.Characteristic := hC.characteristic
  have hex : ∃ c ∈ C, t * c * t⁻¹ = c⁻¹ ∧ c ^ 2 ≠ 1 := by
    by_contra! hn
    exact hout (IsPGroup.involution_mem_normal_abelian_of_central_action_of_no_normal_eight
      hno hZ C hC.centralizer_eq_self_of_abelian.le t (ht ▸ pow_orderOf_eq_one t)
      (fun g => hC.c4_square_conjugations_commute hno hZ e g t) hn)
  obtain ⟨c, hc, hinv, hs⟩ := hex
  refine ⟨c, hc, ?_, hinv⟩
  have hc4 : c ^ 4 = 1 := by
    have hm : ∀ x : C4SquareExtension.Model, x ^ 4 = 1 := by decide
    have h : (⟨c, hc⟩ : C) ^ 4 = 1 := e.injective (by rw [map_pow, hm, map_one])
    exact congrArg Subtype.val h
  have hd : orderOf c ∣ 4 := orderOf_dvd_of_pow_eq_one hc4
  have hle : orderOf c ≤ 4 := Nat.le_of_dvd (by decide) hd
  interval_cases ho : orderOf c <;> norm_num at hd
  · exact (hs (by rw [orderOf_eq_one_iff.mp ho]; simp)).elim
  · exact (hs (ho ▸ pow_orderOf_eq_one c)).elim
  · rfl

/-- The fixed subgroup of an automorphism free on the critical sixteen is
elementary abelian: each fixed element has a fixed square in that sixteen. -/
public theorem fixedSubgroup_elementary_of_c4_square
    (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (e : C ≃* C4SquareExtension.Model)
    (a : MulAut P) (hfree : ∀ c ∈ C, a c = c → c = 1) :
    IsElementaryAbelian 2 a.fixedSubgroup := by
  have hs (x : a.fixedSubgroup) : x ^ 2 = 1 := by
    apply Subtype.ext
    apply hfree _ (hC.square_mem_of_c4_square hno hZ e x)
    rw [map_pow, (MulAut.mem_fixedSubgroup a x).mp x.property]
  refine {
    toIsMulCommutative := IsMulCommutative.of_comm ?_
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  intro x y
  have hi (z : a.fixedSubgroup) : z⁻¹ = z :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hs z)
  calc
    x * y = (x * y)⁻¹ := (hi _).symm
    _ = y * x := by rw [mul_inv_rev, hi, hi]

/-- A cubic automorphism free on the critical C₄-square has at most four
fixed elements in the ambient two-group. Conjugation on the critical subgroup
is faithful on its fixed subgroup and commutes with the cubic restriction. -/
public theorem fixedSubgroup_card_le_four_of_c4_square
    (hP : IsPGroup 2 P) (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (e : C ≃* C4SquareExtension.Model)
    (a : MulAut P) (ha : orderOf a = 3)
    (hfree : ∀ c ∈ C, a c = c → c = 1) : Nat.card a.fixedSubgroup ≤ 4 := by
  let : C.Characteristic := hC.characteristic
  let f : P →* MulAut C := MulAut.conjNormal
  let b : MulAut C := MulAut.characteristic C a
  let r : a.fixedSubgroup →* MulAut C := f.comp a.fixedSubgroup.subtype
  have hbinv : b ^ 3 = 1 := by
    change (MulAut.characteristic C a) ^ 3 = 1
    rw [← map_pow, show a ^ 3 = 1 from ha ▸ pow_orderOf_eq_one a, map_one]
  have hbne : b ≠ 1 := by
    intro hb
    have hall (c : C) : c = 1 := by
      apply Subtype.ext
      apply hfree c c.property
      exact congrArg (fun f : MulAut C => (f c : P)) hb
    have h : (Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 4))) =
        (1 : C4SquareExtension.Model) := by
      simpa using congrArg e (hall (e.symm (Multiplicative.ofAdd 1, 1)))
    exact (by decide : (Multiplicative.ofAdd (1 : ZMod 4),
      (1 : Multiplicative (ZMod 4))) ≠ (1 : C4SquareExtension.Model)) h
  have hr : Function.Injective r := by
    apply r.ker_eq_bot_iff.mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    have hxc : (x : P) ∈ C := by
      rw [← conjNormal_ker_eq_of_selfCentralizing_abelian C
        hC.centralizer_eq_self_of_abelian.le]
      exact hx
    exact hfree x hxc ((MulAut.mem_fixedSubgroup a x).mp x.property)
  have hcomm : ∀ c ∈ r.range, Commute c b := by
    rintro c ⟨x, rfl⟩
    apply MulEquiv.ext
    intro d
    apply Subtype.ext
    change (x : P) * a (d : P) * (x : P)⁻¹ = a ((x : P) * (d : P) * (x : P)⁻¹)
    rw [map_mul, map_mul, map_inv, (MulAut.mem_fixedSubgroup a x).mp x.property]
  have hbound := two_group_c4_square_automorphism_centralizer_card_le_four
    ⟨e⟩ b hbinv hbne r.range
    ((hP.to_subgroup a.fixedSubgroup).of_surjective r.rangeRestrict r.rangeRestrict_surjective)
    hcomm
  exact (Nat.card_le_card_of_injective r.rangeRestrict
    (fun x y h => hr (congrArg Subtype.val h))).trans hbound

end IsCriticalPSubgroup
