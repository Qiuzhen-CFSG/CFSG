module
public import Theory.GroupAction.FiveSixteenCentralizer

/-!
# Commuting involutions on the four-dimensional five-factor

The existing faithful five-action centralizer theorem bounds that centralizer
by order fifteen on a carrier of order sixteen. An involutory automorphism
in it has order dividing both two and fifteen, so is the identity. Applied
to the restricted action on a factor summand, this supplies the fixed-space
inference without an additional representation classification.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951, the rank-one actor centralizing the second five-factor.
The subgroup here is in the actual automorphism group of the carrier;
faithful order-five restriction must be verified by the application.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
open Subgroup
variable {W : Type*} [Group W] [Finite W]

/-- An involutory automorphism commuting with a faithful five-subgroup on
sixteen elements is trivial. This applies to a restricted factor action. -/
theorem involution_eq_one_of_centralizes_five
    (P : Subgroup (MulAut W)) (hP : Nat.card P = 5) (hW : Nat.card W = 16)
    (b : MulAut W) (hb : b ^ 2 = 1) (hcomm : b ∈ centralizer (P : Set (MulAut W))) :
    b = 1 := by
  let C := centralizer (P : Set (MulAut W))
  let c : C := ⟨b, hcomm⟩
  have hc : c ^ 2 = 1 := Subtype.ext hb
  have hd := card_centralizer_five_dvd_fifteen (V := W) P hP hW
  have ho : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes
    (by decide : Nat.Coprime 2 15) (orderOf_dvd_of_pow_eq_one hc)
    ((orderOf_dvd_natCard c).trans hd)
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp ho)

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
end
