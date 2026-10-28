module
public import Theory.SpecificGroups.Triality.ParabolicOuterTwo.Extensions
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedCellCount

/-!
# Prime actors on genuine binary triality

The root-cell order formula makes ³D₄(2) five-free, and inner–coefficient
coverage makes its outer automorphism group have order dividing three.
Consequently its full automorphism group is five-free. A faithful actor
of order three or five must therefore be cubic. This uses the full actual
automorphism group, with no assumed splitting or chosen outer action.

Source: GLS3 §2.5 for graph-field automorphisms and §§2.3–2.6 for the root
order formula; the prime actors in Aschbacher–Smith 5.2.2, pp.647–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Triality.Standard.BinaryPrimeActors

/-- Neither the inner group nor the outer quotient has a factor of five. -/
theorem five_not_dvd_card_aut :
    ¬ 5 ∣ Nat.card (MulAut (BinaryCarrier 1 Nat.zero_lt_one)) := by
  let M := BinaryCarrier 1 Nat.zero_lt_one
  have ho : Nat.card (MulAut.Outer M) ∣ 3 := by
    simpa only [mul_one] using ParabolicOuterTwo.outer_card_dvd 1 Nat.zero_lt_one
  have hi : Nat.card (MulAut.innerSubgroup M) ∣ Nat.card M :=
    Subgroup.card_dvd_of_surjective (MulAut.conj : M →* MulAut M).rangeRestrict
      (MulAut.conj : M →* MulAut M).rangeRestrict_surjective
  have hm : ¬ 5 ∣ Nat.card M := by
    rw [ConcreteBruhat.FixedCellCount.card_carrier,ConcreteBruhat.FixedCellCount.card_borel]
    norm_num [binaryParameters_q]
  intro hd
  rw [(MulAut.innerSubgroup M).card_eq_card_quotient_mul_card_subgroup] at hd
  rcases (by decide : Nat.Prime 5).dvd_mul.mp hd with h | h
  · exact (by decide : ¬ 5 ∣ 3) (h.trans ho)
  · exact hm (h.trans hi)

/-- A faithful actor of order three or five on genuine binary triality
necessarily has order three. -/
theorem prime_eq_three {A K : Type*} [Group A] [Finite A] [Group K] [Finite K]
    (e : K ≃* BinaryCarrier 1 Nat.zero_lt_one) (f : A →* MulAut K)
    (hf : Function.Injective f) {p : ℕ} (hp : p = 3 ∨ p = 5)
    (hc : Nat.card A = p) : p = 3 := by
  rcases hp with hp | hp
  · exact hp
  · have hd := Subgroup.card_dvd_of_injective ((MulAut.congr e).toMonoidHom.comp f)
      ((MulAut.congr e).injective.comp hf)
    rw [hc,hp] at hd
    exact (five_not_dvd_card_aut hd).elim

end Triality.Standard.BinaryPrimeActors
