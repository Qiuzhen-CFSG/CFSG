module
public import Theory.Representation.BinarySevenCode.PermutationAction
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
public import Mathlib.GroupTheory.PGroup
/-!
# Central representatives in the binary seven-letter module

Every two-group of coordinate permutations fixes a word of each nonzero
even weight. Indeed, the sets of two-, four- and six-element subsets have
odd sizes 21, 35 and 7. The fixed-point theorem for two-groups supplies a
fixed support, and its characteristic word is even.

Source application: Aschbacher--Smith, 12.3.4(2) and 12.3.5, printed pp.808--809.
-/

public section
open scoped Pointwise
namespace BinarySevenCode

theorem exists_fixed_weight {P : Type*} [Group P] (hP : IsPGroup 2 P)
    (f : P →* Equiv.Perm (Fin 7)) {n : ℕ} (hn : n = 2 ∨ n = 4 ∨ n = 6) :
    ∃ w : EvenWord, weight w.val = n ∧ ∀ p : P, evenRepresentation (f p) w = w := by
  let : MulAction P (Fin 7) := MulAction.compHom (Fin 7) f
  obtain ⟨s,hs⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card
    (Set.powersetCard (Fin 7) n) (by
      rw [Set.powersetCard.card]
      simp only [Nat.card_fin]
      rcases hn with rfl | rfl | rfl <;> decide)
  let w : Word := fun i => if i ∈ s.val then 1 else 0
  have hsum : ∑ i, w i = (n : ZMod 2) := by
    simp only [w,Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,
      nsmul_eq_mul,mul_one]
    exact congrArg (Nat.cast : ℕ → ZMod 2) (Set.powersetCard.card_eq s)
  have hw : w ∈ evenWords := by
    rw [mem_evenWords_iff,hsum]
    rcases hn with rfl | rfl | rfl <;> decide
  refine ⟨⟨w,hw⟩, ?_, ?_⟩
  · simp [weight,w,Set.powersetCard.card_eq]
  · intro p
    apply Subtype.ext
    funext i
    change w ((f p).symm i) = w i
    have he : (f p).symm i ∈ s.val ↔ i ∈ s.val := by
      have ht : p • s = s := hs p
      have ht' : p • s.val = s.val := congrArg Subtype.val ht
      have hmem : (f p).symm i ∈ s.val ↔ i ∈ p • s.val := by
        rw [Finset.mem_smul_finset]
        constructor
        · intro hi
          exact ⟨(f p).symm i,hi,(f p).apply_symm_apply i⟩
        · rintro ⟨j,hj,hji⟩
          change f p j = i at hji
          have hj' : j = (f p).symm i := (f p).injective (by simpa using hji)
          rwa [← hj']
      exact hmem.trans (by rw [ht'])
    simp only [w,he]

end BinarySevenCode
