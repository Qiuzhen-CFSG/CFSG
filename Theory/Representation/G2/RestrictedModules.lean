module

public import Theory.Representation.G2.RestrictedModules.Trivial
public import Theory.Representation.G2.RestrictedModules.NaturalIrreducible
public import Theory.Representation.G2.RestrictedModules.NaturalHighestWeight
public import Theory.Representation.G2.RestrictedModules.NaturalFieldTransport
public import Theory.Representation.G2.RestrictedModules.Adjoint
public import Theory.Representation.G2.RestrictedModules.Steinberg
public import Theory.Representation.ExtendScalars
public import Theory.Representation.SemilinearConjugation

/-!
# Concrete restricted G₂ modules in characteristic two

This interface supplies the four actual restricted factors: the trivial line, the
six-dimensional natural quotient action, the fourteen-dimensional octonion adjoint
action, and the level-two Steinberg orbit in the tensor cube. Each action is on the
actual `Atlas.G2.Model F`; the natural coordinate model is retained together with an
explicit intertwining equivalence to the trace-zero split-octonion quotient.

The factor dimensions are `1, 6, 14, 64`, and every factor is absolutely irreducible
over every characteristic-two field. The module-local interfaces also expose the
root actions, highest vectors and genuine coefficient/Frobenius representation
equivalences needed by tensor-product arguments. This file packages those facts
without identifying factors merely from their dimensions.

Sources: GLS3, 2.8.6, 2.8.7 and 2.8.10(g); Aschbacher--Smith, G.9.3(10), printed
pp.354,356--357. Tensor exhaustivity and binary Schur descent are separate results.
-/

@[expose] public noncomputable section

namespace Atlas.G2.Restricted

/-- The four restricted highest-weight factors in GLS3's order. -/
inductive Factor
  | trivial
  | natural
  | adjoint
  | steinberg
  deriving DecidableEq

instance : Fintype Factor :=
  ⟨{.trivial, .natural, .adjoint, .steinberg}, by
    intro a
    cases a <;> simp⟩

/-- The dimension attached to a concrete restricted factor. -/
def Factor.dimension : Factor → ℕ
  | .trivial => 1
  | .natural => 6
  | .adjoint => 14
  | .steinberg => 64

variable (F : Type*) [Field F] [CharP F 2]

/-- The actual carrier of each of the four factors. -/
def Space : Factor → Type _
  | .trivial => Trivial.Space F
  | .natural => NaturalCoordinates.Space F
  | .adjoint => Adjoint.Space F
  | .steinberg => Steinberg.Space F

instance spaceAddCommGroup (a : Factor) : AddCommGroup (Space F a) := by
  cases a with
  | trivial => change AddCommGroup (Trivial.Space F); infer_instance
  | natural => change AddCommGroup (NaturalCoordinates.Space F); infer_instance
  | adjoint => change AddCommGroup (Adjoint.Space F); infer_instance
  | steinberg => change AddCommGroup (Steinberg.Space F); infer_instance

instance spaceModule (a : Factor) : Module F (Space F a) := by
  cases a with
  | trivial => change Module F (Trivial.Space F); infer_instance
  | natural => change Module F (NaturalCoordinates.Space F); infer_instance
  | adjoint => change Module F (Adjoint.Space F); infer_instance
  | steinberg => change Module F (Steinberg.Space F); infer_instance

instance spaceFiniteDimensional (a : Factor) : FiniteDimensional F (Space F a) := by
  cases a with
  | trivial => change FiniteDimensional F (Trivial.Space F); infer_instance
  | natural => change FiniteDimensional F (NaturalCoordinates.Space F); infer_instance
  | adjoint => change FiniteDimensional F (Adjoint.Space F); infer_instance
  | steinberg => change FiniteDimensional F (Steinberg.Space F); infer_instance

/-- The genuine action of the actual split-octonion automorphism group. -/
def action (a : Factor) : Representation F (Model F) (Space F a) := by
  cases a
  · exact Trivial.action F
  · exact NaturalCoordinates.action F
  · exact Adjoint.action F
  · exact Steinberg.action F

@[simp] theorem finrank_space (a : Factor) :
    Module.finrank F (Space F a) = a.dimension := by
  cases a
  · exact Trivial.finrank_space F
  · change Module.finrank F (Fin 6 → F) = 6
    simp
  · exact Adjoint.finrank F
  · exact Steinberg.finrank_space F

/-- All four concrete actions are absolutely irreducible. -/
theorem absolutelyIrreducible (a : Factor) :
    Representation.IsAbsolutelyIrreducible (action F a) := by
  cases a
  · exact Trivial.absolutelyIrreducible F
  · exact NaturalCoordinates.absolutelyIrreducible F
  · exact Adjoint.absolutelyIrreducible F
  · exact Steinberg.absolutelyIrreducible F

/-- Absolute irreducibility persists over every extension of the coefficient field. -/
theorem absolutelyIrreducible_extendScalars (a : Factor)
    (K : Type*) [Field K] [Algebra F K] :
    Representation.IsAbsolutelyIrreducible
      (Representation.extendScalars (F := F) (V := Space F a) K (action F a)) :=
  (Representation.IsAbsolutelyIrreducible.isAbsolutelyIrreducible_iff_extendScalars
    (action F a) K).mpr (absolutelyIrreducible F a)

/-- Each factor remains irreducible after arbitrary scalar extension. -/
theorem irreducible_extendScalars (a : Factor)
    (K : Type*) [Field K] [Algebra F K] :
    Representation.IsIrreducible
      (Representation.extendScalars (F := F) (V := Space F a) K (action F a)) := by
  let : Representation.IsAbsolutelyIrreducible (action F a) := absolutelyIrreducible F a
  exact Representation.IsAbsolutelyIrreducible.irreducible_of_extension (action F a) K

/-- Extension of scalars preserves the four dimensions. -/
theorem finrank_extendScalars (a : Factor)
    (K : Type*) [Field K] [Algebra F K] :
    Module.finrank K (TensorProduct F K (Space F a)) = a.dimension := by
  rw [Module.finrank_baseChange, finrank_space]

/-- The four dimensions distinguish these constructed factors. -/
theorem Factor.dimension_injective : Function.Injective Factor.dimension := by
  intro a b h
  cases a <;> cases b <;> simp_all [Factor.dimension]

/-- These four actual actions are pairwise inequivalent. -/
theorem action_equiv_iff (a b : Factor) :
    Nonempty (Representation.RepEquiv (action F a) (action F b)) ↔ a = b := by
  constructor
  · rintro ⟨e⟩
    apply Factor.dimension_injective
    simpa only [finrank_space] using e.toLinearEquiv.finrank_eq
  · rintro rfl
    exact ⟨Representation.RepEquiv.refl _⟩

/-- The factors also stay pairwise inequivalent over every scalar extension. -/
theorem extendScalars_equiv_iff (a b : Factor)
    (K : Type*) [Field K] [Algebra F K] :
    Nonempty (Representation.RepEquiv
      (Representation.extendScalars (F := F) (V := Space F a) K (action F a))
      (Representation.extendScalars (F := F) (V := Space F b) K (action F b))) ↔ a = b := by
  constructor
  · rintro ⟨e⟩
    apply Factor.dimension_injective
    simpa only [finrank_extendScalars] using e.toLinearEquiv.finrank_eq
  · rintro rfl
    exact ⟨Representation.RepEquiv.refl _⟩

/-- The natural factor is genuinely the trace-zero split-octonion quotient action. -/
def naturalActualEquiv :
    Representation.RepEquiv (action F .natural) (Atlas.G2.Natural.action F) :=
  NaturalCoordinates.repEquiv F |>.symm

@[simp] theorem naturalActualEquiv_intertwines (g : Model F) (v : Space F .natural) :
    naturalActualEquiv F (action F .natural g v) =
      Atlas.G2.Natural.action F g (naturalActualEquiv F v) := by
  exact (naturalActualEquiv F).isIntertwining g v

/-- Pairing with the short simple coroot: the coefficient of GLS3's λ₂. -/
def Factor.shortWeight : Factor → ℕ
  | .trivial | .adjoint => 0
  | .natural | .steinberg => 1

/-- Pairing with the long simple coroot: the coefficient of GLS3's λ₁. -/
def Factor.longWeight : Factor → ℕ
  | .trivial | .natural => 0
  | .adjoint | .steinberg => 1

/-- Each constructed factor has a specified nonzero highest vector. -/
def highestVector (a : Factor) : Space F a := by
  cases a
  · exact (1 : F)
  · exact NaturalCoordinates.highestVector F
  · exact Adjoint.highestVector F
  · exact Steinberg.highestVector F

theorem highestVector_ne_zero (a : Factor) : highestVector F a ≠ 0 := by
  cases a
  · exact (one_ne_zero : (1 : F) ≠ 0)
  · exact NaturalCoordinates.highestVector_ne_zero F
  · exact Adjoint.highestVector_ne_zero F
  · exact Steinberg.highestVector_ne_zero F

/-- All six actual positive root groups fix each highest vector at every parameter. -/
theorem highestVector_fixed_roots (a : Factor) (t : F) :
    action F a (rootA t) (highestVector F a) = highestVector F a ∧
    action F a (rootB t) (highestVector F a) = highestVector F a ∧
    action F a (rootC t) (highestVector F a) = highestVector F a ∧
    action F a (rootD t) (highestVector F a) = highestVector F a ∧
    action F a (rootE t) (highestVector F a) = highestVector F a ∧
    action F a (rootF t) (highestVector F a) = highestVector F a := by
  cases a
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact NaturalCoordinates.highestVector_fixed_roots F t
  · exact Adjoint.highestVector_fixed_roots F t
  · exact Steinberg.highestVector_fixed_roots F t

/-- The genuine positive unipotent subgroup fixes the chosen highest vectors. -/
theorem highestVector_fixed_unipotent (a : Factor) (g : Model F)
    (hg : g ∈ unipotent) : action F a g (highestVector F a) = highestVector F a := by
  rw [unipotent_eq_range] at hg
  obtain ⟨t, rfl⟩ := hg
  simp only [unipotentProduct, map_mul, Module.End.mul_apply]
  rw [(highestVector_fixed_roots F a _).2.2.2.2.2,
    (highestVector_fixed_roots F a _).2.2.2.2.1,
    (highestVector_fixed_roots F a _).2.2.2.1,
    (highestVector_fixed_roots F a _).2.2.1,
    (highestVector_fixed_roots F a _).2.1,
    (highestVector_fixed_roots F a _).1]

/-- The positive unipotent fixed space is exactly the specified highest line. -/
theorem fixed_unipotent_iff (a : Factor) (v : Space F a) :
    (∀ g ∈ (unipotent : Subgroup (Model F)), action F a g v = v) ↔
      ∃ c : F, v = c • highestVector F a := by
  constructor
  · intro h
    cases a with
    | trivial =>
      exact ⟨(show F from v), (mul_one (show F from v)).symm⟩
    | natural =>
      apply (NaturalCoordinates.fixed_simpleRoots_iff F v).mp
      exact ⟨h _ (Subgroup.subset_closure (by simp)),
        h _ (Subgroup.subset_closure (by simp))⟩
    | adjoint => exact (Adjoint.fixed_unipotent_iff F v).mp h
    | steinberg =>
      apply (Steinberg.fixed_binary_roots_iff F v).mp
      exact ⟨h _ (Subgroup.subset_closure (by simp)),
        h _ (Subgroup.subset_closure (by simp)),
        h _ (Subgroup.subset_closure (by simp)),
        h _ (Subgroup.subset_closure (by simp)),
        h _ (Subgroup.subset_closure (by simp)),
        h _ (Subgroup.subset_closure (by simp))⟩
  · rintro ⟨c, rfl⟩ g hg
    rw [map_smul, highestVector_fixed_unipotent F a g hg]

/-- The one-dimensional highest line of any restricted factor. -/
def highestLine (a : Factor) : Submodule F (Space F a) :=
  Submodule.span F {highestVector F a}

theorem finrank_highestLine (a : Factor) : Module.finrank F (highestLine F a) = 1 :=
  finrank_span_singleton (highestVector_ne_zero F a)

/-- The torus characters are 1, l, l*m, and l²*m respectively. -/
theorem highestVector_torus (a : Factor) (l m : Fˣ) :
    action F a (torus l m) (highestVector F a) =
      ((l : F) ^ (a.shortWeight + a.longWeight) * (m : F) ^ a.longWeight) •
        highestVector F a := by
  cases a with
  | trivial =>
    change (1 : F) = ((l : F) ^ (0 + 0) * (m : F) ^ 0) * 1
    simp
  | natural =>
    change NaturalCoordinates.action F (torus l m) (NaturalCoordinates.highestVector F) =
      ((l : F) ^ (1 + 0) * (m : F) ^ 0) • NaturalCoordinates.highestVector F
    simpa using
      NaturalCoordinates.highestVector_torus F l m
  | adjoint =>
    change Adjoint.action F (torus l m) (Adjoint.highestVector F) =
      ((l : F) ^ (0 + 1) * (m : F) ^ 1) • Adjoint.highestVector F
    simpa using
      Adjoint.highestVector_torus F l m
  | steinberg =>
    change Steinberg.action F (torus l m) (Steinberg.highestVector F) =
      ((l : F) ^ (1 + 1) * (m : F) ^ 1) • Steinberg.highestVector F
    simpa using
      Steinberg.highestVector_torus F l m

/-- Short-coroot action verifies the short coordinate of the highest weight. -/
theorem highestVector_shortCoroot (a : Factor) (t : Fˣ) :
    action F a (shortCoroot t) (highestVector F a) =
      (t : F) ^ a.shortWeight • highestVector F a := by
  cases a with
  | trivial => change (1 : F) = (t : F) ^ 0 * 1; simp
  | natural =>
    change NaturalCoordinates.action F (shortCoroot t) (NaturalCoordinates.highestVector F) =
      (t : F) ^ 1 • NaturalCoordinates.highestVector F
    simpa using NaturalCoordinates.highestVector_shortCoroot F t
  | adjoint =>
    change Adjoint.action F (shortCoroot t) (Adjoint.highestVector F) =
      (t : F) ^ 0 • Adjoint.highestVector F
    simpa using Adjoint.highestVector_shortCoroot F t
  | steinberg =>
    change Steinberg.action F (shortCoroot t) (Steinberg.highestVector F) =
      (t : F) ^ 1 • Steinberg.highestVector F
    simpa using Steinberg.highestVector_shortCoroot F t

/-- Long-coroot action verifies GLS3's opposite fundamental-weight numbering. -/
theorem highestVector_longCoroot (a : Factor) (t : Fˣ) :
    action F a (longCoroot t) (highestVector F a) =
      (t : F) ^ a.longWeight • highestVector F a := by
  cases a with
  | trivial => change (1 : F) = (t : F) ^ 0 * 1; simp
  | natural =>
    change NaturalCoordinates.action F (longCoroot t) (NaturalCoordinates.highestVector F) =
      (t : F) ^ 0 • NaturalCoordinates.highestVector F
    simpa using NaturalCoordinates.highestVector_longCoroot F t
  | adjoint =>
    change Adjoint.action F (longCoroot t) (Adjoint.highestVector F) =
      (t : F) ^ 1 • Adjoint.highestVector F
    simpa using Adjoint.highestVector_longCoroot F t
  | steinberg =>
    change Steinberg.action F (longCoroot t) (Steinberg.highestVector F) =
      (t : F) ^ 1 • Steinberg.highestVector F
    simpa using Steinberg.highestVector_longCoroot F t

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Coefficient transport on any one of the four carriers. -/
def coefficientEquiv (a : Factor) (σ : F ≃+* F) :
    LinearEquiv (σ : F →+* F) (σ' := (σ.symm : F →+* F))
      (Space F a) (Space F a) := by
  cases a
  · exact Trivial.coefficientEquiv F σ
  · exact Representation.coordinateSemilinearEquiv σ (Fin 6)
  · exact Adjoint.coefficientSemilinearEquiv F σ
  · exact Steinberg.coefficientEquiv F σ

/-- Coefficient conjugation is the action twisted by the actual field automorphism. -/
theorem coefficientConjugate_eq (a : Factor) (σ : F ≃+* F) :
    Representation.semilinearConjugate (F := F) (G := Model F)
        (V := Space F a) (W := Space F a) σ (action F a)
        (coefficientEquiv F a σ) =
      (action F a).comp (fieldEquiv σ).toMonoidHom := by
  cases a
  · exact Trivial.coefficientConjugate_eq F σ
  · exact NaturalCoordinates.coefficientConjugate_eq F σ
  · exact Adjoint.coefficientConjugate_eq F σ
  · exact Steinberg.coefficientConjugate_eq F σ

/-- A genuine representation equivalence for coefficient transport. -/
def coefficientConjugateEquiv (a : Factor) (σ : F ≃+* F) :
    Representation.RepEquiv
      (Representation.semilinearConjugate (F := F) (G := Model F)
        (V := Space F a) (W := Space F a) σ (action F a)
        (coefficientEquiv F a σ))
      ((action F a).comp (fieldEquiv σ).toMonoidHom) where
  toLinearEquiv := LinearEquiv.refl F _
  isIntertwining' g := by
    simp only [LinearEquiv.refl_toLinearMap, LinearMap.id_comp, LinearMap.comp_id]
    exact DFunLike.congr_fun (coefficientConjugate_eq F a σ) g

/-- The same coefficient equivalence after arbitrary scalar extension. -/
def coefficientConjugateExtendScalarsEquiv (a : Factor) (σ : F ≃+* F)
    (K : Type*) [Field K] [Algebra F K] :
    Representation.RepEquiv
      (Representation.extendScalars (F := F) (V := Space F a) K
        (Representation.semilinearConjugate (F := F) (G := Model F)
          (V := Space F a) (W := Space F a) σ (action F a)
          (coefficientEquiv F a σ)))
      (Representation.extendScalars (F := F) (V := Space F a) K
        ((action F a).comp (fieldEquiv σ).toMonoidHom)) := by
  rw [coefficientConjugate_eq]

/-- The actual finite-field Frobenius automorphism of `Atlas.G2.Model F`. -/
def frobeniusAutomorphism [Finite F] (r : ℕ) : MulAut (Model F) :=
  fieldEquiv (iterateFrobeniusEquiv F 2 r)

/-- Frobenius transport for every factor, with a genuine representation equivalence. -/
theorem frobeniusConjugate_eq [Finite F] (a : Factor) (r : ℕ) :
    Representation.semilinearConjugate (F := F) (G := Model F)
        (V := Space F a) (W := Space F a) (iterateFrobeniusEquiv F 2 r)
        (action F a) (coefficientEquiv F a (iterateFrobeniusEquiv F 2 r)) =
      (action F a).comp (frobeniusAutomorphism F r).toMonoidHom := by
  exact coefficientConjugate_eq F a _

/-- The Frobenius identification as an actual intertwining equivalence. -/
def frobeniusConjugateEquiv [Finite F] (a : Factor) (r : ℕ) :
    Representation.RepEquiv
      (Representation.semilinearConjugate (F := F) (G := Model F)
        (V := Space F a) (W := Space F a) (iterateFrobeniusEquiv F 2 r)
        (action F a) (coefficientEquiv F a (iterateFrobeniusEquiv F 2 r)))
      ((action F a).comp (frobeniusAutomorphism F r).toMonoidHom) :=
  coefficientConjugateEquiv F a _

/-- Frobenius compatibility retains its actual intertwiner after scalar extension. -/
def frobeniusConjugateExtendScalarsEquiv [Finite F] (a : Factor) (r : ℕ)
    (K : Type*) [Field K] [Algebra F K] :
    Representation.RepEquiv
      (Representation.extendScalars (F := F) (V := Space F a) K
        (Representation.semilinearConjugate (F := F) (G := Model F)
          (V := Space F a) (W := Space F a) (iterateFrobeniusEquiv F 2 r)
          (action F a) (coefficientEquiv F a (iterateFrobeniusEquiv F 2 r))))
      (Representation.extendScalars (F := F) (V := Space F a) K
        ((action F a).comp (frobeniusAutomorphism F r).toMonoidHom)) :=
  coefficientConjugateExtendScalarsEquiv F a _ K

end Atlas.G2.Restricted

end
