module
public import Theory.GroupTheory.Recognition.Brauer.PlaneData
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The odd inverted subgroups in Brauer's geometry

Brauer, *On finite Desarguesian planes I*, article page 118, derives that
`M` and `Mstar` are abelian of odd order and inverted by the distinguished
involution `j`. These properties are consequences of the original seed
postulates and are not additional assumptions in the geometry.

For either subgroup, conjugation by `j` is an automorphism because `C(j)`
normalizes it. Its fixed elements are precisely its intersection with `C(j)`,
which is trivial. The automorphism is involutive since `j` has order two.
Mathlib's fixed-point-free automorphism results now give inversion, pairwise
commutativity, and odd order. The two source subgroups use the same argument.

The conclusion retains each subgroup's original Group instance and states
commutativity explicitly. This lets the later fixed-subgroup decomposition
reuse exactly the conjugation action induced by the source normalizer.
-/

namespace Theory.GroupTheory

private theorem odd_commuting_inverted_of_disjoint_centralizer
    {G : Type*} [Group G] (H : Subgroup G) [Finite H] (j : G)
    (hj : orderOf j = 2) (hn : j ∈ Subgroup.normalizer (H : Set G))
    (hd : Disjoint H (Subgroup.centralizer ({j} : Set G))) :
    Odd (Nat.card H) ∧ (∀ a b : H, Commute a b) ∧
      ∀ m : H, j⁻¹ * (m : G) * j = (m : G)⁻¹ := by
  let φ : MulAut H := H.normalizerMonoidHom ⟨j, hn⟩
  have hsq : j * j = 1 := by simpa only [hj, pow_two] using pow_orderOf_eq_one j
  have hinv : j⁻¹ = j := inv_eq_iff_mul_eq_one.mpr hsq
  have hφ : MonoidHom.FixedPointFree φ := by
    intro m hm
    apply Subtype.ext
    have heq : j * (m : G) * j⁻¹ = (m : G) := congrArg Subtype.val hm
    have hc : (m : G) ∈ Subgroup.centralizer ({j} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp heq).symm
    have hm' : (m : G) ∈ H ⊓ Subgroup.centralizer ({j} : Set G) := ⟨m.property, hc⟩
    change (m : G) = 1
    simpa only [hd.eq_bot, Subgroup.mem_bot] using hm'
  have hi : Function.Involutive φ := by
    intro m
    apply Subtype.ext
    change j * (j * (m : G) * j⁻¹) * j⁻¹ = (m : G)
    simp only [hinv, mul_assoc, hsq, mul_one]
    rw [← mul_assoc, hsq, one_mul]
  refine ⟨hφ.odd_card_of_involutive hi, hφ.commute_all_of_involutive hi, ?_⟩
  intro m
  have hm : φ m = m⁻¹ := congrFun (hφ.coe_eq_inv_of_involutive hi) m
  have hval := congrArg Subtype.val hm
  change j * (m : G) * j⁻¹ = (m : G)⁻¹ at hval
  simpa only [hinv] using hval

namespace BrauerPlaneSeed

/-- Brauer I, p.118: both root subgroups have odd order, are abelian, and
are inverted by the distinguished involution. -/
public theorem inverted_subgroups {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G) :
    (Odd (Nat.card S.M) ∧ (∀ a b : S.M, Commute a b) ∧
      ∀ m : S.M, S.j⁻¹ * (m : G) * S.j = (m : G)⁻¹) ∧
    (Odd (Nat.card S.Mstar) ∧ (∀ a b : S.Mstar, Commute a b) ∧
      ∀ m : S.Mstar, S.j⁻¹ * (m : G) * S.j = (m : G)⁻¹) := by
  have hjC : S.j ∈ Subgroup.centralizer ({S.j} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  exact ⟨odd_commuting_inverted_of_disjoint_centralizer S.M S.j S.j_order
      (S.centralizer_le_normalizer_M hjC) S.disjoint_M_centralizer,
    odd_commuting_inverted_of_disjoint_centralizer S.Mstar S.j S.j_order
      (S.centralizer_le_normalizer_Mstar hjC) S.disjoint_Mstar_centralizer⟩

end BrauerPlaneSeed
end Theory.GroupTheory
