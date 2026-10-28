module

public import BenderSuzuki.Converse.PSL2
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# A root subgroup gives the binary PSL₂ rank lower bound

The additive group of a field of order 2ⁿ embeds by upper transvections
in PSL₂. In characteristic two the scalar kernel is trivial. The resulting
elementary subgroup has order 2ⁿ and proves the required rank lower bound
without any automorphism classification.

Source application: the larger field model in Aschbacher–Smith 16.1.7(3a)
and its exclusion in 16.3.9, printed pp.1172 and 1180.
-/

public section

namespace Theory.PSL2
open BenderSuzuki.Converse

/-- The actual upper root subgroup witnesses two-rank at least n. -/
theorem root_two_rank_ge (F : Type*) [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) :
    n ≤ primeRank 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let f := (pi F).comp (uniHom F)
  have hf : Function.Injective f := pi_injective.comp uniHom_injective
  let e := MonoidHom.ofInjective hf
  let : IsElementaryAbelian 2 f.range := {
    toIsMulCommutative := ⟨⟨fun a b => e.symm.injective (by
      simp only [map_mul, mul_comm])⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      apply e.symm.injective
      rw [map_pow, map_one, pow_two]
      change (e.symm x).toAdd + (e.symm x).toAdd = 0
      exact CharTwo.add_self_eq_zero _) }
  apply IsElementaryAbelian.primeRank_ge_of_card f.range
  exact (Nat.card_congr e.toEquiv.symm).trans hF

end Theory.PSL2
