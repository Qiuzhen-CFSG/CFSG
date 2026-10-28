module
public import Theory.Representation.FrobeniusFilteredIrreducibility
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.FrobeniusSeparation
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.BasicSpaces

/-!
# The original Ree action and the finite filtered irreducibility criterion

Specialize the proved finite Frobenius argument to the literal field of degree
`2*m+1` and the original `Model m` action. The remaining premises are actual
root expansions, the tensor primitive line and tensor layer generation; their
producer must discharge them on the unweighted tensor filtration. No finite
irreducibility or realization premise occurs in this implication.

Source: Steinberg, Representations of Algebraic Groups (1963), proof of 12.2.
-/

public section
open scoped BigOperators
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
variable {m : ℕ} {F V I J : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem irreducible_of_root_filtration [Nontrivial V]
    (f : CoefficientField m →+* F) (ρ : Representation F (Model m) V)
    (C : ℤ → Submodule F V) (hmono : Monotone C)
    (N : ℕ) (htop : C N = ⊤)
    (v : V) (hzero : C 0 = Submodule.span F {v})
    (P : I → Fin (2*m+1) → Module.End F V)
    (Q : J → Fin (2*m+1) → Module.End F V)
    (d : I → ℕ) (hd : ∀ i, 0 < d i) (e : J → ℕ) (he : ∀ j, 0 < e j)
    (positive : I → CoefficientField m → Model m) (negative : J → CoefficientField m → Model m)
    (hP : ∀ i k x, x ∈ C k → ∀ a, P i a x ∈ C (k - d i))
    (hpos : ∀ i k x, x ∈ C k → ∀ t,
      ρ (positive i t) x - x - ∑ a, f (t ^ (2 ^ a.val)) • P i a x ∈ C (k - d i - 1))
    (hprimitive : ∀ k : ℕ, 0 < k → ∀ x, x ∈ C k →
      (∀ i a, P i a x ∈ C ((k : ℤ) - d i - 1)) → x ∈ C ((k : ℤ) - 1))
    (hneg : ∀ j k x, x ∈ C k → ∀ t,
      ρ (negative j t) x - x - ∑ a, f (t ^ (2 ^ a.val)) • Q j a x ∈ C (k + e j - 1))
    (hgenerate : ∀ k : ℕ, 0 < k → C k ≤ C ((k : ℤ) - 1) ⊔
      ⨆ j, ⨆ a, (C ((k : ℤ) - e j)).map (Q j a))
    : Representation.IsIrreducible ρ := by
  have h := Representation.FrobeniusFiltered.isIrreducible (p := 2) (I := I) (J := J)
    f ρ C hmono N htop v hzero
  rw [GaloisField.finrank 2 (by omega : 2*m+1 ≠ 0)] at h
  exact h P Q d hd e he positive negative hP hpos hprimitive hneg hgenerate

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
