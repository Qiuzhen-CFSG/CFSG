module

public import Theory.SpecificGroups.Alternating.FiveSubgroupExtension.Transport
public import Theory.Alternating.Aut

/-!
# Generating pairs for an alternating four-subgroup of A₅

A three-cycle and an involution whose product has order three are conjugate
in S₅ to the explicit pair below. Their twelve distinct words give the A₄
normal forms. The common S₅ centralizer is trivial. The finite checks concern
only individual permutations, never subgroups or functions on A₅.

These facts supply the marking extension in `FiveSubgroupExtension.lean`,
used for Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38.
-/

@[expose] public section
open Subgroup
namespace AlternatingFiveSubgroupExtension.Generators

abbrev S5 := Equiv.Perm (Fin 5)

/-- The cycle `(0 1 2)`. -/
def a : A5 := ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

/-- The double transposition `(0 1)(2 3)`. -/
def b : A5 := ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

/-- Every nontrivial element of exponent three in A₅ is a three-cycle. -/
lemma cube_cycleType (x : A5) (hx : x ^ 3 = 1) (hx1 : x ≠ 1) :
    x.val.cycleType = {3} := by
  have ho : orderOf x.val = 3 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hx hx1
  obtain ⟨r, hr, he⟩ := GroupTheory.AutAlternating.cycleType_of_order_three x.val ho
  have hb := x.val.sum_cycleType_le
  rw [he, Multiset.sum_replicate] at hb
  have hr1 : r = 1 := by
    simp only [nsmul_eq_mul, Fintype.card_fin, Nat.cast_id] at hb
    omega
  simpa [hr1] using he

/-- Three-cycles are conjugate in the symmetric group. -/
lemma a_conjugate (x : A5) (hx : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ g : S5, g * a.val * g⁻¹ = x.val := by
  apply isConj_iff.mp
  apply Equiv.Perm.isConj_iff_cycleType_eq.mpr
  rw [cube_cycleType x hx hx1]
  decide +kernel

/-- The six elements of the centralizer of `a` carry `b` to every involution
whose product with `a` has exponent three. -/
lemma b_conjugate : ∀ y : A5, y ^ 2 = 1 → y ≠ 1 → (a * y) ^ 3 = 1 →
    ∃ i : Fin 3, ∃ j : Fin 2,
      let g := a.val ^ i.val * (Equiv.swap 3 4 : S5) ^ j.val
      g * a.val * g⁻¹ = a.val ∧ g * b.val * g⁻¹ = y.val := by
  decide +kernel

/-- Lagrange's exponent bound leaves only an A₄ pair or an inverting involution. -/
lemma product_cases : ∀ y : A5, y ^ 2 = 1 → y ≠ 1 → (a * y) ^ 12 = 1 →
    (a * y) ^ 3 = 1 ∨ y * a * y⁻¹ = a⁻¹ := by
  decide +kernel

/-- The common centralizer of the generating pair in S₅ is trivial. -/
lemma centralizer_pair : ∀ g : S5,
    g * a.val = a.val * g → g * b.val = b.val * g → g = 1 := by
  decide +kernel

/-- Twelve normal forms for the A₄ pair, written uniformly in any group. -/
def word {G : Type*} [Group G] (x y : G) (i : Fin 3 × Fin 2 × Fin 2) : G :=
  x ^ i.1.val * y ^ i.2.1.val * (x * y * x⁻¹) ^ i.2.2.val

/-- Homomorphisms preserve the normal-form words. -/
lemma map_word {G H F : Type*} [Group G] [Group H]
    [FunLike F G H] [MonoidHomClass F G H] (f : F)
    (x y : G) (i : Fin 3 × Fin 2 × Fin 2) :
    f (word x y i) = word (f x) (f y) i := by
  simp only [word, map_mul, map_pow, map_inv]

/-- The twelve standard words are distinct, already on the points zero and one. -/
lemma word_injective : Function.Injective (word a b) := by
  have hi : Function.Injective (fun i => ((word a b i).val 0, (word a b i).val 1)) := by
    decide +kernel
  intro i j h
  exact hi (congrArg (fun z : A5 => (z.val 0, z.val 1)) h)
end AlternatingFiveSubgroupExtension.Generators
end
