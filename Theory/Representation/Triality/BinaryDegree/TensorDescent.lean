module

public import Theory.Representation.Triality.BinaryDegree.TwistedProduct
public import Theory.Representation.ReeF4.BinaryDegree.SchurDescent
public import Theory.AlgebraicGroup.RootSystems.TypeD4DiagramTriality

/-!
# Binary descent for diagram-twisted D4 tensor factors

The sixteen binary restricted weights use the same numbered D4 vertices and
pinned arm cycle as the genuine standard carrier. `TensorData` specifies the
consequences needed from the Steinberg classification: the tensor dimension
formula, the basic degree bounds, and the exact correspondence between character
Frobenius periods and periods of the diagram-twisted weight sequence.

The existing Schur-field construction gives an absolutely irreducible module
and the exact character period `s`. The threefold wrap shows `s ∣ 3*n`, and
`TwistedProduct` proves the degree estimate for every possible period. Multiplying
by the Schur-field degree yields the binary lower bound, also for `n = 1`.
No assertion that all standard triality representations admit `TensorData` is
made here; that is the remaining model-specific representation theorem.

Sources: GLS3 §2.8, especially 2.8.2, 2.8.6(a), and 2.8.8
(`refs/KGroup/GLS3/chapter2.tex`); Aschbacher--Smith, *The Classification of
Quasithin Groups*, printed p.356 (PDF p.367).
-/

@[expose] public section

namespace Triality.BinaryDegree

open Theory.AlgebraicGroup.StandardRootSystem
open Representation.FrobeniusTensor

universe u v w

/-- Binary coefficients of a restricted D4 weight, with central vertex `1`
and the three arms `0`, `2`, `3`, as in the standard carrier. -/
abbrev RestrictedWeight := Fin 4 → Bool

/-- The zero highest weight. -/
def trivialWeight : RestrictedWeight := fun _ => false

/-- Pullback of a weight by the same pinned arm cycle used in `StandardModel`. -/
def twistWeight (wt : RestrictedWeight) : RestrictedWeight :=
  wt ∘ typeD4DiagramPermutation

@[simp] theorem twistWeight_trivial : twistWeight trivialWeight = trivialWeight := rfl

@[simp] theorem twistWeight_three (wt : RestrictedWeight) :
    twistWeight (twistWeight (twistWeight wt)) = wt := by
  funext i
  simp only [twistWeight, Function.comp_apply, typeD4DiagramPermutation_three]

/-- Numerical and character consequences of a genuine restricted-weight tensor
classification. Constructing this data for every qualifying irreducible is a
separate theorem. In particular, no binary degree lower bound is assumed. -/
structure TensorData {F : Type v} [Field F] {G : Type u} [Group G]
    {W : Type w} [AddCommGroup W] [Module F W]
    (n : ℕ) (σ : Representation F G W) where
  /-- The restricted weights, extended through the diagram-twisted wraparound. -/
  weight : ℕ → RestrictedWeight
  /-- Dimensions of the basic restricted-weight modules. -/
  factorDegree : RestrictedWeight → ℕ
  /-- Every basic module is nonzero. -/
  factor_pos : ∀ wt, 0 < factorDegree wt
  /-- The zero weight gives the trivial one-dimensional module. -/
  trivial_degree : factorDegree trivialWeight = 1
  /-- The tensor product is nontrivial. -/
  nontrivial_factor : ∃ i, weight i ≠ trivialWeight
  /-- The absolute minimum for a nontrivial basic D4 module. -/
  nontrivial_degree : ∀ wt, wt ≠ trivialWeight → 8 ≤ factorDegree wt
  /-- The stronger minimum for a nontrivial diagram-fixed highest weight. -/
  fixed_degree : ∀ wt, wt ≠ trivialWeight → twistWeight wt = wt → 24 ≤ factorDegree wt
  /-- Diagram twisting preserves the dimension of a basic module. -/
  diagram_degree : ∀ wt, factorDegree (twistWeight wt) = factorDegree wt
  /-- Wrapping the tensor sequence applies the pinned D4 diagram action. -/
  twisted_period : ∀ i, weight (i + n) = twistWeight (weight i)
  /-- The dimension of the actual representation is the product of the factors. -/
  finrank_eq : Module.finrank F W = ∏ i ∈ Finset.range n, factorDegree (weight i)
  /-- Frobenius fixes the character exactly when it fixes the tensor parameters.
  This requires the actual classification and uniqueness, including graph twisting. -/
  character_period : ∀ r,
    (∀ g, σ.character g ^ (2 ^ r) = σ.character g) ↔ Function.Periodic weight r

/-- Three diagram-twisted wraps give an ordinary period. -/
theorem TensorData.weight_periodic_three
    {F : Type v} [Field F] {G : Type u} [Group G]
    {W : Type w} [AddCommGroup W] [Module F W]
    {n : ℕ} {σ : Representation F G W} (h : TensorData n σ) :
    Function.Periodic h.weight (3 * n) := by
  intro i
  rw [show i + 3 * n = ((i + n) + n) + n by omega]
  simp only [h.twisted_period, twistWeight_three]

/-- Descent from all restricted-weight alternatives, using the actual Schur
field of the binary irreducible. The tensor data still has to be constructed. -/
theorem binary_finrank_ge_of_tensorData
    {G : Type u} [Group G] {V : Type v} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    {n : ℕ} (hn : 0 < n) (h : TensorData n (absoluteRep ρ)) :
    24 * n ≤ Module.finrank (ZMod 2) V := by
  let s := Module.finrank (ZMod 2) (SchurField ρ)
  have hs : 0 < s := schurField_finrank_pos ρ
  have hsn : s ∣ 3 * n := (character_pow_iff ρ (3 * n)).mp
    ((h.character_period (3 * n)).mpr h.weight_periodic_three)
  have hperiod : Function.Periodic h.weight s :=
    (h.character_period s).mp ((character_pow_iff ρ s).mpr (dvd_refl s))
  have hlarge : ∃ i, 8 ≤ h.factorDegree (h.weight i) := by
    obtain ⟨i, hi⟩ := h.nontrivial_factor
    exact ⟨i, h.nontrivial_degree _ hi⟩
  have hfixed (i : ℕ) (hfix : twistWeight (h.weight i) = h.weight i)
      (hi : 8 ≤ h.factorDegree (h.weight i)) : 24 ≤ h.factorDegree (h.weight i) := by
    apply h.fixed_degree _ _ hfix
    intro heq
    rw [heq, h.trivial_degree] at hi
    omega
  rw [binary_finrank_eq ρ, h.finrank_eq]
  exact twenty_four_mul_le_twisted_product hn hs hsn h.twisted_period h.diagram_degree
    hperiod (fun i => h.factor_pos _) hlarge hfixed

end Triality.BinaryDegree
