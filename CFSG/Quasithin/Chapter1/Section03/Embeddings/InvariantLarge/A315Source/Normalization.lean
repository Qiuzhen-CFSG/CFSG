module
public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Theory.GroupTheory.SubgroupProductCard
public import Theory.GroupTheory.TwoPrimeSolvable
public import Theory.GroupTheory.SolvableSylowControl.Marked
public import Theory.GroupTheory.SylowNormalIntersection
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.Source

/-!
# The actual soluble Sylow product in A.3.15

Permutability makes the join B S have two-prime order. Burnside solvability
and intrinsic solvable Sylow control then normalize S ∩ D in the original
ambient group. The proof retains the supplied Sylow; no complement or Cartan
placement is assumed. These are the source inputs used by the five
nonbinary even rank-two model branches of Proposition 1.3.4, pp.510–511.
-/
public noncomputable section

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source
open Subgroup Theory.GroupTheory
open scoped Pointwise
variable {J : Type*} [Group J] [Finite J]

/-- A permuting p-subgroup and two-subgroup have soluble join. -/
theorem solvable_product {p : ℕ} [Fact p.Prime]
    (B S : Subgroup J) (hB : IsPGroup p B) (hS : IsPGroup 2 S)
    (hp : p ≠ 2) (hperm : (B : Set J) * S = (S : Set J) * B) :
    Group.IsSolvable (B ⊔ S : Subgroup J) := by
  have hd := IsPGroup.disjoint_of_ne p 2 hp B S hB hS
  have hc := card_set_mul_mul_card_inf B S
  rw [hd.eq_bot, card_bot, mul_one, ← coe_sup_of_set_mul_comm B S hperm] at hc
  change Nat.card (B ⊔ S : Subgroup J) = Nat.card B * Nat.card S at hc
  apply isSolvable_of_prime_dvd_card_eq_two_or_prime _ (Fact.out : p.Prime)
  intro r hr hdr
  rw [hc] at hdr
  rcases hr.dvd_mul.mp hdr with hb | hs
  · obtain ⟨n, hn⟩ := hB.exists_card_eq
    rw [hn] at hb
    exact Or.inr ((Nat.dvd_prime (Fact.out : p.Prime)).mp
      (hr.dvd_of_dvd_pow hb) |>.resolve_left hr.ne_one)
  · obtain ⟨n, hn⟩ := hS.exists_card_eq
    rw [hn] at hs
    exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
      (hr.dvd_of_dvd_pow hs) |>.resolve_left hr.ne_one)

/-- Intrinsic solvable Sylow control normalizes the literal ambient intersection. -/
theorem normalizes_intersection {D B : Subgroup J} [D.Normal]
    (S : Sylow 2 J) {p : ℕ} [Fact p.Prime]
    (hB : IsPGroup p B) (hp : p ≠ 2) (_hBD : B ≤ D)
    (hperm : (B : Set J) * S = (S : Set J) * B)
    (hc : SolvableSylowControl 2 D) :
    B ≤ normalizer ((S : Subgroup J) ⊓ D : Subgroup J) := by
  let A := B ⊔ (S : Subgroup J)
  let : Group.IsSolvable A := solvable_product B S hB S.isPGroup' hp hperm
  obtain ⟨U, hU⟩ := S.exists_subgroupOf_eq_of_normal D
  have he : (U : Subgroup D).map D.subtype = (S : Subgroup J) ⊓ D := by
    rw [hU, subgroupOf_map_subtype]
  have hn := hc.normalizes_sylow D A U (by simp [normalizer_eq_top])
    (show (U : Subgroup D).map D.subtype ≤ A by rw [he]; exact inf_le_left.trans le_sup_right)
  rw [he] at hn
  exact le_sup_left.trans hn

/-- Subtype form of the same literal normalization. -/
theorem normalizes_restriction {D B : Subgroup J} [D.Normal]
    (S : Sylow 2 J) {p : ℕ} [Fact p.Prime]
    (hB : IsPGroup p B) (hp : p ≠ 2) (hBD : B ≤ D)
    (hperm : (B : Set J) * S = (S : Set J) * B)
    (hc : SolvableSylowControl 2 D) :
    B.subgroupOf D ≤ normalizer ((S : Subgroup J).subgroupOf D : Set D) := by
  have hn := normalizes_intersection S hB hp hBD hperm hc
  apply le_normalizer_iff.mpr
  intro b hb u hu
  exact (le_normalizer_iff.mp hn b hb u ⟨hu, u.property⟩).1
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source
