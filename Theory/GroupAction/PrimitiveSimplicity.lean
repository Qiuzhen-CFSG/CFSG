module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Simplicity from a faithful quasiprimitive action

Every nontrivial normal subgroup in a faithful quasiprimitive action is
transitive. Consequently the degree divides its order. To prove simplicity,
it therefore suffices to exclude proper normal subgroups whose orders are
divisible by any fixed divisor of the degree.

The proof combines the normal-orbit criterion in Mathlib's `Primitive` module
(Wielandt, *Finite Permutation Groups*, Theorem 7.1) with orbit-stabilizer.
-/

namespace MulAction

variable {G X : Type*} [Group G] [MulAction G X]
  [FaithfulSMul G X] [IsQuasiPreprimitive G X] [Nonempty X]

/-- A nontrivial normal subgroup in a faithful quasiprimitive action has order
divisible by the degree. -/
public theorem card_dvd_card_normal_of_quasiprimitive
    (N : Subgroup G) [N.Normal] (hne : N ≠ ⊥) : Nat.card X ∣ Nat.card N := by
  have hfixed : fixedPoints N X ≠ Set.univ := by
    intro h
    apply hne
    apply N.eq_bot_iff_forall.mpr
    intro n hn
    apply FaithfulSMul.eq_of_smul_eq_smul (M := G) (α := X)
    intro x
    rw [one_smul]
    exact (mem_fixedPoints.mp (h ▸ Set.mem_univ x)) ⟨n, hn⟩
  let : IsPretransitive N X := IsQuasiPreprimitive.isPretransitive_of_normal hfixed
  obtain ⟨x⟩ := ‹Nonempty X›
  have horbit : Nat.card (orbit N x) = Nat.card X := by
    rw [orbit_eq_univ]
    exact Nat.card_congr (Equiv.Set.univ X)
  refine ⟨Nat.card (stabilizer N x), ?_⟩
  rw [← horbit, ← Nat.card_prod]
  exact Nat.card_congr (orbitProdStabilizerEquivGroup N x).symm

/-- A divisor of the degree can reduce simplicity to one family of normal
subgroup orders. In even degree, one may take `d = 2`. -/
public theorem isSimpleGroup_of_quasiprimitive_of_normal_card
    [Nontrivial G] {d : ℕ} (hd : d ∣ Nat.card X)
    (h : ∀ N : Subgroup G, N.Normal → d ∣ Nat.card N → N = ⊤) :
    IsSimpleGroup G := by
  constructor
  intro N hN
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  · let : N.Normal := hN
    exact Or.inr (h N hN (hd.trans
      (card_dvd_card_normal_of_quasiprimitive (X := X) N hbot)))

end MulAction
