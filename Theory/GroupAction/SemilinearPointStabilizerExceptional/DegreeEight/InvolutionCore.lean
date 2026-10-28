module

public import Theory.PGroupCore

/-!
# Commuting involutions and the two-core

If all elements with square one commute, those elements themselves form a
normal elementary abelian two-subgroup. Thus a group of even order and trivial
two-core must have two noncommuting involutions. This excludes the affine
alternative in the degree-eight permutation calculation for GLS, Volume 4,
Chapter 1, Theorem 3.2 (`refs/KGroup/GLS4/Chapter1.tex`, lines 305–468).
-/

public section
namespace MulAction.SemilinearPointStabilizer.DegreeEight

/-- Pairwise commutation makes the square-one elements a normal two-subgroup. -/
theorem square_one_mem_twoCore_of_commute {G : Type*} [Group G]
    (hc : ∀ a b : G, a ^ 2 = 1 → b ^ 2 = 1 → Commute a b)
    (t : G) (ht : t ^ 2 = 1) : t ∈ pCore 2 G := by
  let E : Subgroup G :=
    { carrier := {g | g ^ 2 = 1}
      one_mem' := one_pow 2
      mul_mem' := fun ha hb => by
        change (_ * _) ^ 2 = 1
        rw [(hc _ _ ha hb).mul_pow, ha, hb, one_mul]
      inv_mem' := fun ha => by
        change _⁻¹ ^ 2 = 1
        rw [inv_pow, ha, inv_one] }
  have hE : E.Normal := ⟨by
    intro n hn g
    change (MulAut.conj g n) ^ 2 = 1
    rw [← map_pow, show n ^ 2 = 1 from hn, map_one]⟩
  have hp : IsPGroup 2 E := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    exact g.property
  exact (show E ≤ pCore 2 G from le_sSup ⟨hE, hp⟩) ht

/-- Even order and trivial two-core rule out commuting involutions. -/
theorem not_all_square_one_commute {G : Type*} [Group G] [Finite G]
    (heven : 2 ∣ Nat.card G) (hcore : pCore 2 G = ⊥) :
    ¬ (∀ a b : G, a ^ 2 = 1 → b ^ 2 = 1 → Commute a b) := by
  intro hc
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 heven
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have hmem := square_one_mem_twoCore_of_commute hc t ht2
  rw [hcore, Subgroup.mem_bot] at hmem
  simp [hmem] at ht

end MulAction.SemilinearPointStabilizer.DegreeEight
