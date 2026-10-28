module

public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.TransitiveCoverage.Native

/-!
# A numerical invariant of native M₂₄ Sylow cosets

The marked Sylow subgroup preserves the binary partition
`(((0,11),(8,9)),((3,19),(4,21)))` of its eight-point orbit. At each vertex,
encode the unordered pair of child codes by its minimum and maximum.
The resulting integer is unchanged by right multiplication by the Sylow
subgroup. Distinct integers therefore certify distinct native cosets; global
injectivity of this encoding is unnecessary.

This supplies the small coset invariant used in exhaustive finite coverage.
Source context: Aschbacher, *Sporadic Groups*, Chapter 7, §20; GLS3 Table 5.3e.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.TransitiveCoverage
open SylowNormalizer

def unorderedPairCode (n a b : ℕ) : ℕ := min a b * n + max a b

theorem unorderedPairCode_comm (n a b : ℕ) : unorderedPairCode n a b = unorderedPairCode n b a := by
  simp only [unorderedPairCode, min_comm, max_comm]

def flagKey (g : Fin 24 → Fin 24) : ℕ :=
  unorderedPairCode (32 ^ 4)
    (unorderedPairCode (32 ^ 2) (unorderedPairCode 32 (g 0).val (g 11).val) (unorderedPairCode 32 (g 8).val (g 9).val))
    (unorderedPairCode (32 ^ 2) (unorderedPairCode 32 (g 3).val (g 19).val) (unorderedPairCode 32 (g 4).val (g 21).val))

private theorem flagKey_generator (g : Fin 24 → Fin 24) (i : Fin 4) :
    flagKey (g ∘ generatorPoint i) = flagKey g := by
  fin_cases i <;> dsimp [flagKey, generatorPoint] <;> simp only [unorderedPairCode_comm]

theorem flagKey_mul (g : M24) (s : candidate) :
    flagKey (g * s : M24).val = flagKey g.val := by
  have aux (y : M24) (hy : y ∈ candidate) :
      ∀ x : M24, flagKey (x * y).val = flagKey x.val := by
    apply Subgroup.closure_induction_left (s := Set.range generator)
      (p := fun y _ => ∀ x : M24, flagKey (x * y).val = flagKey x.val) ?_ ?_ ?_ hy
    · intro x
      rw [mul_one]
    · rintro _ ⟨i, rfl⟩ y _ ih x
      rw [← mul_assoc, ih]
      change flagKey (x.val ∘ generatorPerm i) = flagKey x.val
      have he : (generatorPerm i : Fin 24 → Fin 24) = generatorPoint i :=
        funext (generatorPerm_apply i)
      rw [he]
      exact flagKey_generator _ _
    · rintro _ ⟨i, rfl⟩ y _ ih x
      rw [← mul_assoc, ih]
      have he : (generatorPerm i : Fin 24 → Fin 24) = generatorPoint i :=
        funext (generatorPerm_apply i)
      have ht := flagKey_generator (x * (generator i)⁻¹).val i
      rw [← he] at ht
      change flagKey ((x * (generator i)⁻¹) * generator i).val = _ at ht
      simpa only [inv_mul_cancel_right] using ht.symm
  exact aux s s.property g

theorem key_eq_of_coset_eq {g h : M24}
    (he : (QuotientGroup.mk g : M24 ⧸ candidate) = QuotientGroup.mk h) :
    flagKey g.val = flagKey h.val := by
  have hm : g⁻¹ * h ∈ candidate := QuotientGroup.eq.mp he
  have := flagKey_mul g ⟨g⁻¹ * h, hm⟩
  simpa only [mul_inv_cancel_left] using this.symm

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.TransitiveCoverage
