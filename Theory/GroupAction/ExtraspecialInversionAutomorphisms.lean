module
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms

/-!
# Extraspecial automorphisms commuting with quotient inversion

For an extraspecial ternary group, an automorphism acting trivially on the
central quotient is inner. If it commutes with an automorphism inverting
that quotient, its conjugating element is fixed and inverted modulo the
center, hence central. Thus the centralizer of quotient inversion acts
faithfully on the central quotient. This also lifts equality of quotient
actions to equality of the original actions.

The application is the complement in the cubic-line normalizer of
Aschbacher, *Sporadic Groups* (1994), 45.8 and 45.11, pp.246 and 248.
-/

public section
open Subgroup
namespace IsExtraspecial
variable {P : Type*} [Group P] [Finite P] [IsExtraspecial 3 P]
omit [Finite P] [IsExtraspecial 3 P] in
private theorem conj_eq_one_of_mem_center {r : P} (hr : r ∈ center P) : MulAut.conj r = 1 := by
  apply MulEquiv.ext
  intro x
  change r * x * r⁻¹ = x
  rw [← mem_center_iff.mp hr x, mul_inv_cancel_right]

/-- A central-quotient kernel element commuting with quotient inversion is trivial. -/
theorem aut_eq_one_of_quotient_eq_one_of_commute_inversion
    (α β : MulAut P)
    (hα : ∀ x : P, quotientAut (center P) α (QuotientGroup.mk' (center P) x) =
      (QuotientGroup.mk' (center P) x)⁻¹)
    (hβ : quotientAut (center P) β = 1) (hcomm : Commute α β) : β = 1 := by
  obtain ⟨r, hr⟩ := (quotientAut_center_ker_eq_range_conj (p := 3)).le hβ
  have he : MulAut.conj (α r) = MulAut.conj r := by
    apply MulEquiv.ext
    intro x
    have hh := DFunLike.congr_fun hcomm.eq (α.symm x)
    rw [←hr] at hh
    simpa only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply] using hh
  have ht : α r * r⁻¹ ∈ center P := by
    have ht' : MulAut.conj (α r * r⁻¹) = 1 := by rw [map_mul, map_inv, he, mul_inv_cancel]
    apply mem_center_iff.mpr
    intro x
    have hx := DFunLike.congr_fun ht' x
    change (α r * r⁻¹) * x * (α r * r⁻¹)⁻¹ = x at hx
    have hx' := congrArg (fun u => u * (α r * r⁻¹)) hx
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hx'.symm
  let q := QuotientGroup.mk' (center P)
  have hq : q (α r) * (q r)⁻¹ = 1 := by
    rw [←map_inv,←map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr ht
  have ha : q (α r) = (q r)⁻¹ := by simpa only [quotientAut_apply_mk] using hα r
  have htwo : q r ^ 2 = 1 := by
    have hh : (q r)⁻¹ = q r := (mul_inv_eq_one.mp hq).symm.trans ha |>.symm
    rw [pow_two]
    calc q r * q r = (q r)⁻¹ * q r := congrArg (· * q r) hh.symm
         _ = 1 := inv_mul_cancel _
  let : IsElementaryAbelian 3 (P ⧸ center P) := quotient_elementary_abelian 3 P
  have hthree : q r ^ 3 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 3 (P ⧸ center P)) (q r)
  have hqr : q r = 1 := by simpa only [show 3 = 2+1 from rfl,pow_succ,htwo,one_mul] using hthree
  have hrc : r ∈ center P := (QuotientGroup.eq_one_iff _).mp hqr
  rw [←hr]
  exact conj_eq_one_of_mem_center hrc

/-- The centralizer of quotient inversion embeds in the quotient automorphism group. -/
theorem quotientAut_injective_on_centralizer_inversion
    (α : MulAut P)
    (hα : ∀ x : P, quotientAut (center P) α (QuotientGroup.mk' (center P) x) =
      (QuotientGroup.mk' (center P) x)⁻¹) :
    Function.Injective ((quotientAut (center P)).comp (centralizer ({α} : Set (MulAut P))).subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro β hβ
  apply Subtype.ext
  exact aut_eq_one_of_quotient_eq_one_of_commute_inversion α β hα hβ
    (mem_centralizer_singleton_iff.mp β.property).symm

/-- Two automorphisms commuting with quotient inversion agree as soon as their
central-quotient actions agree. -/
theorem aut_eq_of_quotient_eq_of_commute_inversion
    (α β γ : MulAut P)
    (hα : ∀ x : P, quotientAut (center P) α (QuotientGroup.mk' (center P) x) =
      (QuotientGroup.mk' (center P) x)⁻¹)
    (hβ : Commute α β) (hγ : Commute α γ)
    (hq : quotientAut (center P) β = quotientAut (center P) γ) : β = γ := by
  have hβ' : β ∈ centralizer ({α} : Set (MulAut P)) :=
    mem_centralizer_singleton_iff.mpr hβ.eq.symm
  have hγ' : γ ∈ centralizer ({α} : Set (MulAut P)) :=
    mem_centralizer_singleton_iff.mpr hγ.eq.symm
  exact congrArg Subtype.val
    (quotientAut_injective_on_centralizer_inversion α hα (a₁ := ⟨β,hβ'⟩)
      (a₂ := ⟨γ,hγ'⟩) hq)
end IsExtraspecial
