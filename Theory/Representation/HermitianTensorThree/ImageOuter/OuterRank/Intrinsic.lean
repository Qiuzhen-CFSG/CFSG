module

public import Theory.Representation.HermitianTensorThree.ImageOuter.Overgroups
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.GroupTheory.PrimeRankHom

/-!
# Intrinsic ranks in the Hermitian tensor normalizer

The center of SL₃ has exponent dividing three, so it has two-rank zero.
Projection to PSL₃ and the embedded upper unitriangular group then give
rank 2m over a field of order 2^m. The actual image equivalences give rank
4n for the Hermitian tensor image. A supplied equivalence for the literal
marked centralizer gives its rank 2n without identifying an arbitrary
source overgroup with the full normalizer.

Source: Aschbacher–Smith, Chapter H, H.4.4(6–7), printed pp.380–382.
-/

public section
noncomputable section
namespace Representation.HermitianTensorThree.ImageOuter.OuterRank
open Subgroup Theory.GroupTheory

/-- Finiteness of the literal binary ambient linear group. -/
instance finiteBinaryLinearEquiv (n : ℕ) [NeZero n] :
    Finite (Space n ≃ₗ[ZMod 2] Space n) :=
  Finite.of_injective (fun e : Space n ≃ₗ[ZMod 2] Space n => (e : Space n → Space n))
    DFunLike.coe_injective

/-- The cubic scalar center contributes no elementary two-subgroup. -/
theorem specialLinearThree_center_twoRank (k : Type*) [Field k] [Finite k] :
    primeRank 2 (center (Matrix.SpecialLinearGroup (Fin 3) k)) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply primeRank_le_of_pow_eq_one_subset
    (⊥ : Subgroup (center (Matrix.SpecialLinearGroup (Fin 3) k)))
  · simp
  · intro x hx
    rw [mem_bot]
    have h3 : x ^ 3 = 1 := by
      obtain ⟨c, hc, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp x.property
      have hc' : c ^ 3 = 1 := by simpa using hc
      apply Subtype.ext
      apply Subtype.ext
      change x.val.val ^ 3 = 1
      rw [← he, ← map_pow, hc', map_one]
    rw [pow_succ, hx, one_mul] at h3
    exact h3

/-- The same root planes realize the rank in SL₃ and its central quotient. -/
theorem specialLinearThree_twoRank (k : Type*) [Field k] [Finite k] {m : ℕ}
    (hm : 0 < m) (hk : Nat.card k = 2 ^ m) :
    primeRank 2 (Matrix.SpecialLinearGroup (Fin 3) k) = 2 * m := by
  let := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow (p := 2) (f := m)
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  apply le_antisymm
  · have hb := primeRank_le_ker_add (p := 2)
      (QuotientGroup.mk' (center (Matrix.SpecialLinearGroup (Fin 3) k)))
    rw [QuotientGroup.ker_mk', specialLinearThree_center_twoRank, zero_add] at hb
    exact hb.trans (Matrix.PSL3Even.two_rank k hm hk).le
  · rw [← Matrix.PSL3Even.UnipotentGeometry.unipotent_two_rank k hk]
    exact primeRank_le_of_injective 2 _
      (Matrix.PSL3Even.UnipotentGeometry.specialLinear_injective k)

variable (n : ℕ) [NeZero n]

/-- Both parity cases use the actual image, with its original binary action. -/
theorem binaryImage_twoRank : primeRank 2 (binaryImage n) = 4 * n := by
  let : Finite (Image n) := Finite.of_injective (binaryImageEquiv n) (binaryImageEquiv n).injective
  rw [← primeRank_equiv 2 (binaryImageEquiv n)]
  rcases Nat.even_or_odd n with hn | hn
  · rw [primeRank_equiv 2 (imageEquivSL n hn)]
    have h := specialLinearThree_twoRank (E n)
      (Nat.mul_pos (by decide) (Nat.pos_of_ne_zero (NeZero.ne n))) (card_E n)
    simpa [← Nat.mul_assoc] using h
  · rw [primeRank_equiv 2 (imageEquivPSL n hn)]
    have h := Matrix.PSL3Even.two_rank (E n)
      (Nat.mul_pos (by decide) (Nat.pos_of_ne_zero (NeZero.ne n))) (card_E n)
    simpa [← Nat.mul_assoc] using h

/-- The marked centralizer hypothesis is on the literal subgroup of the image. -/
theorem markedCentralizer_twoRank
    (hK : Nonempty (↥(binaryImage n ⊓
      centralizer ({fieldSwapBinary n} : Set (Space n ≃ₗ[ZMod 2] Space n))) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (F n))) :
    primeRank 2 ↥(binaryImage n ⊓
      centralizer ({fieldSwapBinary n} : Set (Space n ≃ₗ[ZMod 2] Space n))) = 2 * n := by
  obtain ⟨e⟩ := hK
  rw [primeRank_equiv 2 e]
  exact specialLinearThree_twoRank (F n) (Nat.pos_of_ne_zero (NeZero.ne n)) (card_F n)

/-- The lower half of the source equality m₂(M) = 4n needs no normalizer coverage. -/
theorem sourceOvergroup_twoRank_ge
    (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M) :
    4 * n ≤ primeRank 2 M := by
  rw [← binaryImage_twoRank n]
  exact primeRank_le_of_injective 2 (inclusion (sourceOvergroup_contains_image n M hM))
    (inclusion_injective _)

end Representation.HermitianTensorThree.ImageOuter.OuterRank
