module
public import Theory.Representation.ExtraspecialBinarySix
public import Theory.Representation.ExtraspecialCubicDisplacement
public import Theory.Representation.BinaryOddDisplacement.CentralQuotient
public import Theory.GroupTheory.PGroup.ExtraspecialThreeInvolutionEndpoints

/-!
# A small involution forces the extraspecial binary six-space

Let P be a normal extraspecial group of order 27 acting faithfully on a
binary module whose P-center has zero fixed space. A nontrivial involution
on P fixing its center inverts P/Z(P) and forces exponent three. A
commutator with that involution is therefore a noncentral cubic element.
Its displacement is four times one sixth of the module dimension, while
it is at most twice the involution's displacement. An involution moving
at most two dimensions forces dimension six; faithfulness then gives
irreducibility on P.

The original ambient action and center are retained throughout. This
supplies the degree calculation used in Aschbacher–Smith 14.7.16(1),
printed p.1048, without requiring the whole D.2.17 classification.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.ExtraspecialBinarySix
set_option backward.isDefEq.respectTransparency false in
/-- A center-fixing involution of displacement at most two forces the
faithful extraspecial section to be irreducible of binary degree six. -/
theorem six_and_irreducible_of_small_involution
    {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) (hf : Function.Injective σ)
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27)
    (hfix : invariants ((σ.comp P.subtype).comp (center P).subtype) = ⊥)
    (t : D) (ht : t ^ 2 = 1)
    (hne : (MulAut.conjNormal t : MulAut P) ≠ 1)
    (hcenter : ∀ z ∈ center P, (MulAut.conjNormal t : MulAut P) z = z)
    (hsmall : fixedCodim σ (zpowers t) ≤ 2) :
    Module.finrank (ZMod 2) W = 6 ∧ IsIrreducible (σ.comp P.subtype) := by
  let a : MulAut P := MulAut.conjNormal t
  have ha : Function.Involutive a := by
    intro x
    have he : a ^ 2 = 1 := by
      change (MulAut.conjNormal t : MulAut P) ^ 2 = 1
      rw [←map_pow,ht,map_one]
    exact congrArg (fun f : MulAut P => f x) (by simpa only [pow_two] using he)
  obtain ⟨hexp,hinv⟩ := IsExtraspecial.exponent_and_frattini_inversion_of_card27 hP a ha hne hcenter
  let : Nontrivial (P ⧸ center P) := IsExtraspecial.quotient_nontrivial 3 P
  let : IsElementaryAbelian 3 (P ⧸ center P) := IsExtraspecial.quotient_elementary_abelian 3 P
  obtain ⟨y,hy⟩ := exists_ne (1 : P ⧸ center P)
  have hy3 : orderOf y = 3 := orderOf_eq_prime
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 (P ⧸ center P)) y) hy
  have hiy : MulAut.centralQuotientAction (MulEquiv.refl (P ⧸ center P)) a y = y⁻¹ := by
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center P) y
    have hax : QuotientGroup.mk' (center P) (a x) = (QuotientGroup.mk' (center P) x)⁻¹ := by
      rw [←map_inv]
      apply QuotientGroup.eq_iff_div_mem.mpr
      rw [←IsExtraspecial.frattini_eq_center_three]
      exact QuotientGroup.eq_iff_div_mem.mp (by simpa only [QuotientGroup.mk'_apply,QuotientGroup.mk_inv] using hinv x)
    exact (MulAut.centralQuotientAction_apply (MulEquiv.refl (P ⧸ center P)) a x).trans hax
  obtain ⟨x,hxo,hxd⟩ := exists_small_displacement_of_inverted_centralQuotient
    σ P (MulEquiv.refl (P ⧸ center P)) t y (by rw [hy3]; decide) hiy
  have hxZ : x ∉ center P := by
    intro hx
    have hz : QuotientGroup.mk' (center P) x = 1 := (QuotientGroup.eq_one_iff _).mpr hx
    change orderOf (QuotientGroup.mk' (center P) x) = orderOf y at hxo
    rw [hz,orderOf_one,hy3] at hxo
    omega
  have hx3 : orderOf x = 3 := orderOf_eq_prime
    (by simpa only [hexp] using Monoid.pow_exponent_eq_one x)
    (fun hx => hxZ (hx ▸ (center P).one_mem))
  have hd := BinaryCoprimeDegree.extraspecial_twentySeven_fixedCodim_zpowers
    (σ.comp P.subtype) hP hfix hx3 hxZ
  have hdiv := BinaryCoprimeDegree.six_dvd_finrank_of_extraspecial_twentySeven
    (σ.comp P.subtype) hP hfix
  have hlo := BinaryCoprimeDegree.extraspecial_finrank_le (p := 3) (by decide)
    (σ.comp P.subtype) (hf.comp P.subtype_injective) hP
  norm_num [BinaryPrimeDegree.orderOf_two_mod_three] at hlo
  have hdim : Module.finrank (ZMod 2) W = 6 := by omega
  exact ⟨hdim,RankTwo.ExtraspecialModel.irreducible_of_faithful_six
    (σ.comp P.subtype) (hf.comp P.subtype_injective) hP hdim⟩

end Representation.ExtraspecialBinarySix
