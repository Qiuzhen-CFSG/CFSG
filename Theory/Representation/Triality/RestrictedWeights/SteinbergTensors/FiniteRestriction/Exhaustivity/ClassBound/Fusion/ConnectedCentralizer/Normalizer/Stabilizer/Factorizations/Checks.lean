module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Stabilizer.Factorizations.Data

/-!
# Kernel checks for the finite D4 factorization certificate

Closure under all four simple reflections certifies the table used for Weyl
coverage. Each short path certifies a product of actual root candidates and
all its doubled displacement equations. `Factorizations` provides the
structural identification with the root pairing's Weyl group.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, §§4–6 and 8.2(6)–(7).
-/

-- Sequential certificate batches keep peak memory bounded.
set_option Elab.async false

public section
open Theory.AlgebraicGroup.StandardRootSystem D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.ConnectedCentralizer.Normalizer.Stabilizer.FactorizationData

private def rowIndex (a : Fin 12) (b : Fin 16) : Fin 192 :=
  ⟨a.val * 16 + b.val, by omega⟩

private lemma checkRows {p : Fin 192 → Prop}
    (h : ∀ a b, p (rowIndex a b)) : ∀ k, p k := by
  intro k
  let a : Fin 12 := ⟨k.val / 16, by omega⟩
  let b : Fin 16 := ⟨k.val % 16, by omega⟩
  have he : rowIndex a b = k := by
    apply Fin.ext
    dsimp [rowIndex, a, b]
    omega
  simpa only [he] using h a b

lemma matrix_zero : matrix 0 = 1 := by decide +kernel
lemma words_zero : words 0 = [] := rfl

set_option maxRecDepth 4000 in
lemma parent_spec : ∀ k : Fin 192, k ≠ 0 →
    parent k < k ∧ words k = step k :: words (parent k) ∧ next (parent k) (step k) = k := by
  apply checkRows
  intro a
  fin_cases a <;> decide +kernel

set_option maxRecDepth 4000 in
lemma matrix_next : ∀ (k : Fin 192) (i j : Fin 4),
    reflection i (fun a => matrix k a j) = fun a => matrix (next k i) a j := by
  apply checkRows
  intro a
  fin_cases a <;> decide +kernel

set_option maxRecDepth 4000 in
lemma matrix_reflection : ∀ (r : Fin 12) (i : Fin 4),
    (matrix (refIndex r)).mulVec (typeDCartanMatrix 2 i) =
      typeDCartanMatrix 2 i - weights r i • weights r := by
  decide +kernel

set_option maxRecDepth 4000 in
lemma paths_valid : ∀ k : Fin 192, pathValid k (path k) := by
  apply checkRows
  intro a
  fin_cases a <;> decide +kernel

set_option maxRecDepth 4000 in
lemma displacements : ∀ (k : Fin 192) p, p ∈ path k →
    (matrix k).mulVec p.2.2 - p.2.2 = (2 : ℤ) • weights p.1 := by
  apply checkRows
  intro a
  fin_cases a <;> decide +kernel

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.ConnectedCentralizer.Normalizer.Stabilizer.FactorizationData
