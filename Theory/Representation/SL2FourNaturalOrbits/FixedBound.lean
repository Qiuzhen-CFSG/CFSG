module
public import Theory.Representation.SL2FourNaturalOrbits.NoTransvections

/-!
# Fixed-vector bound in the natural SL₂(4) normalizer

Every nonidentity element of the actual binary normalizer fixes at most
four vectors. Faithfulness excludes displacement rank zero, and the proved
absence of binary transvections excludes rank one. Rank-nullity then bounds
the fixed dimension by two. No involution or abstract group identification
is needed.

Source application: Aschbacher--Smith, 14.3.33(3), printed p.1005,
using the natural-normalizer facts of 6.2.5.
-/

public section
namespace Representation.SL2FourNatural

/-- A nonidentity element of the actual natural normalizer fixes at most four vectors. -/
theorem normalizer_nonidentity_fixed_card_le_four (e : V ≃ₗ[ZMod 2] V)
    (he : e ∈ SemilinearNormalizer.normalizer) (hne : e ≠ 1) :
    Nat.card e.toLinearMap.fixedSubmodule ≤ 4 := by
  have hzero : Module.finrank (ZMod 2) (LinearMap.range (e.toLinearMap - LinearMap.id)) ≠ 0 := by
    intro hz
    have heq : e.toLinearMap - LinearMap.id = 0 :=
      LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)
    have heq' := sub_eq_zero.mp heq
    exact hne (LinearEquiv.toLinearMap_injective heq')
  have hone := normalizer_no_rank_one e he
  have hd := (e.toLinearMap - LinearMap.id).finrank_range_add_finrank_ker
  rw [←LinearMap.fixedSubmodule_eq_ker,finrank_vector] at hd
  have hdim : Module.finrank (ZMod 2) e.toLinearMap.fixedSubmodule ≤ 2 := by omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) hdim)

end Representation.SL2FourNatural
