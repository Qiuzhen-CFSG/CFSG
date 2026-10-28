module

public import Theory.Mathieu.M23.Properties.Automorphisms
public import Theory.Mathieu.M23.Properties.NoOrderTen
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Involutory fixers of five-divisible subgroups in M₂₃

Every automorphism of the concrete M₂₃ is inner. An involutory automorphism
therefore has an involutory conjugating element, whose centralizer has order
2688. It cannot fix a subgroup of order divisible by five pointwise. Faithful
action on the central quotient transports the conclusion to every perfect
central cover, retaining the literal image of the fixed subgroup.

This is the M₂₃ containing-component calculation in Aschbacher–Smith 10.2.9,
printed pp.750–751, with the A₅ block from A.3.14, printed pp.48–49.
-/

public section
open Subgroup
namespace Sporadic.Mathieu

/-- An automorphism of square one fixing a five-divisible subgroup of M₂₃ is
trivial. The subgroup is the actual fixed subgroup, not an abstract model tag. -/
theorem m23_involutory_fixer_eq_one (B : Subgroup M23) (hB : 5 ∣ Nat.card B)
    (a : MulAut M23) (ha : a ^ 2 = 1) (hfix : ∀ b ∈ B, a b = b) : a = 1 := by
  obtain ⟨g, rfl⟩ := m23_conj_surjective a
  have hg2 : g ^ 2 = 1 := by
    apply MulAut.conj_injective_of_center_eq_bot M23Geometry.m23_center_eq_bot
    simpa only [map_pow, map_one] using ha
  by_cases hg : g = 1
  · simp [hg]
  · have ho : orderOf g = 2 := orderOf_eq_prime hg2 hg
    have hle : B ≤ centralizer ({g} : Set M23) := by
      intro b hb
      apply mem_centralizer_singleton_iff.mpr
      exact (mul_inv_eq_iff_eq_mul.mp (hfix b hb)).symm
    exact (m23_involution_centralizer_not_five g ho
      (hB.trans (card_dvd_of_le hle))).elim

/-- The same rigidity holds in any perfect central cover of the actual M₂₃.
Five-divisibility is required of the literal central image of the fixed group. -/
theorem m23_perfect_cover_involutory_fixer_eq_one
    {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (e : K ⧸ center K ≃* M23) (L : Subgroup K)
    (hL : 5 ∣ Nat.card (L.map (QuotientGroup.mk' (center K))))
    (a : MulAut K) (ha : a ^ 2 = 1) (hfix : ∀ l ∈ L, a l = l) : a = 1 := by
  let q := QuotientGroup.mk' (center K)
  let B := (L.map q).map e.toMonoidHom
  have hB : 5 ∣ Nat.card B := by
    rw [show Nat.card B = Nat.card (L.map q) from
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ e.injective).toEquiv.symm]
    exact hL
  have hf : ∀ b ∈ B, MulAut.centralQuotientAction e a b = b := by
    rintro _ ⟨x, ⟨l, hl, rfl⟩, rfl⟩
    change MulAut.centralQuotientAction e a
      (e (QuotientGroup.mk' (center K) l)) = e (QuotientGroup.mk' (center K) l)
    rw [MulAut.centralQuotientAction_apply, hfix l hl]
  have hs : (MulAut.centralQuotientAction e a) ^ 2 = 1 := by
    rw [← map_pow, ha, map_one]
  apply MulAut.centralQuotientAction_injective e
  rw [map_one]
  exact m23_involutory_fixer_eq_one B hB _ hs hf

end Sporadic.Mathieu
