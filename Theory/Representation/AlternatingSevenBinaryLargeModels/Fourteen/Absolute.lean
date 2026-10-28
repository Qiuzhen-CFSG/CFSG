module

public import Theory.Representation.AlternatingSevenBinaryLargeModels.Fourteen.Certificate
public import Mathlib.Algebra.Field.ZMod

/-!
# Absolute irreducibility of the fourteen-space

The checked action words span every matrix unit. Transporting this density
through the coordinate equivalence and extending scalars proves absolute
irreducibility of the actual binary A₇ action.

Source: the candidate construction in the degree argument for
Aschbacher–Smith K.1.2, printed p.452/PDF p.463.
-/

public section

open Matrix Thompson.BinaryMatrix
namespace Representation.AlternatingSevenBinaryLargeModels.Fourteen
namespace Certificate

private theorem decode_stored (k : Fin 196) :
    decode 14 storedRows[k.val]! = Packed.matrix 14 data[k.val]! := by
  ext i j
  change bit (storedRows[k.val]!)[i.val]! j.val = bit data[k.val]! (14 * i.val + j.val)
  rw [flatten_checked k i]
  unfold bit
  rw [Nat.testBit_mod_two_pow _ 14 j.val, Nat.testBit_shiftRight]
  simp only [j.isLt, decide_true, Bool.true_and]

/-- The checked words in the two actual action matrices span all endomorphisms. -/
theorem matrix_algebra_eq_top
    (A : Subalgebra (ZMod 2) (Matrix (Fin 14) (Fin 14) (ZMod 2)))
    (ha : firstMatrix ∈ A) (hb : secondMatrix ∈ A) : A = ⊤ := by
  have hg (b : Bool) : decode 14 storedRows[genIndex b]! ∈ A := by
    cases b
    · rw [show genIndex false = 1 from rfl, decode_stored ⟨1, by decide⟩, first_data]
      exact ha
    · rw [show genIndex true = 2 from rfl, decode_stored ⟨2, by decide⟩, second_data]
      exact hb
  have hm (k : ℕ) : k < 196 → decode 14 storedRows[k]! ∈ A := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      by_cases hz : k = 0
      · subst k
        rw [decode_stored ⟨0, by decide⟩, first_checked]
        exact A.one_mem
      let j : Fin 195 := ⟨k - 1, by omega⟩
      have hj : j.val + 1 = k := by dsimp [j]; omega
      have hp := parents_checked j
      rw [hj] at hp
      have he := decode_mul 14 storedRows[genIndex choices[k]!]!
        storedRows[parents[k]!]! storedRows[k]! (by
          intro i
          simpa only [hj] using products_checked j i)
      rw [← he]
      exact A.mul_mem (hg _) (ih _ hp (by omega))
  apply Packed.eq_top_of_spanning 14 196 data coefficients
  · intro i j
    exact inverse_checked ⟨14 * i.val + j.val, by omega⟩
  · intro k
    rw [← decode_stored k]
    exact hm k.val k.isLt

end Certificate

/-- The fourteen-dimensional representation generates its full endomorphism algebra. -/
theorem density : Algebra.adjoin (ZMod 2) (Set.range representation) = ⊤ := by
  let P := Algebra.adjoin (ZMod 2) (Set.range representation)
  let e : Module.End (ZMod 2) Vector ≃ₐ[ZMod 2] Matrix (Fin 14) (Fin 14) (ZMod 2) :=
    LinearMap.toMatrixAlgEquiv'
  let Q := P.map e.toAlgHom
  have ha : firstMatrix ∈ Q := by
    rw [← matrix_threeCycle]
    exact ⟨representation threeCycle, Algebra.subset_adjoin (Set.mem_range_self _), rfl⟩
  have hb : secondMatrix ∈ Q := by
    rw [← matrix_sevenCycle]
    exact ⟨representation sevenCycle, Algebra.subset_adjoin (Set.mem_range_self _), rfl⟩
  have hQ := Certificate.matrix_algebra_eq_top Q ha hb
  apply top_unique
  intro f _
  have hf : e f ∈ Q := by rw [hQ]; trivial
  obtain ⟨f', hf', he⟩ := hf
  exact e.injective he ▸ hf'

/-- An actual absolutely irreducible fourteen-dimensional binary A₇ representation. -/
theorem absolutelyIrreducible : IsAbsolutelyIrreducible
    (F := ZMod 2) (G := alternatingGroup (Fin 7)) (V := Fin 14 → ZMod 2)
    representation := by
  refine ⟨?_⟩
  apply irreducible_of_jacobson_density_surjective
  exact (extendScalars_surj_iff (AlgebraicClosure (ZMod 2)) representation).mp density

end Representation.AlternatingSevenBinaryLargeModels.Fourteen
