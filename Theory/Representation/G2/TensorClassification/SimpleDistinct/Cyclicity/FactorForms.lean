module

public import Theory.Representation.G2.TensorClassification.SimpleDistinct.HighestVector
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# Unipotent-invariant pairings on the four concrete G₂ factors

The natural and adjoint coordinate forms pair opposite root coordinates. For
Steinberg we contract the actual tensor cube after interchanging its first two
factors: the ordinary tensor contraction vanishes on its characteristic-two
seed, whereas this contraction pairs the seed with its opposite with value one.
All forms are invariant under the actual positive unipotent subgroup. This is
the precise invariance needed in the orthogonal-complement cyclicity argument.

The opposite vector is obtained using the same actual longest Weyl element for
all four factors. No simplicity, tensor cyclicity or classification is used.
Source: the highest-weight argument supporting GLS3, 2.8.6(a), 2.8.9 and
2.8.10(g). Coordinates use the attributed ATLAS port; see LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open scoped TensorProduct
namespace Atlas.G2.TensorClassification.Cyclicity
open Restricted
variable (F : Type*) [Field F] [CharP F 2]

private def coordPair {m : ℕ} (i j : Fin m) : LinearMap.BilinForm F (Fin m → F) :=
  (LinearMap.mul F F).compl₁₂ (LinearMap.proj i) (LinearMap.proj j)

/-- The alternating form on the six actual natural coordinates. -/
def naturalForm : LinearMap.BilinForm F (NaturalCoordinates.Space F) :=
  coordPair F 0 5 + coordPair F 5 0 + coordPair F 1 4 + coordPair F 4 1 +
    coordPair F 2 3 + coordPair F 3 2

/-- Pair opposite adjoint coordinates, including the two toral coordinates. -/
def adjointCoordinateForm : LinearMap.BilinForm F (Adjoint.Coordinates.Space F) :=
  coordPair F 0 8 + coordPair F 8 0 + coordPair F 1 9 + coordPair F 9 1 +
    coordPair F 2 10 + coordPair F 10 2 + coordPair F 3 5 + coordPair F 5 3 +
    coordPair F 4 11 + coordPair F 11 4 + coordPair F 7 12 + coordPair F 12 7 +
    coordPair F 6 13 + coordPair F 13 6

omit [CharP F 2] in
private theorem invariant_unipotent_of_roots
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F (Model F) V) (B : LinearMap.BilinForm F V)
    (hA : ∀ t x y, B (ρ (rootA t) x) (ρ (rootA t) y) = B x y)
    (hB : ∀ t x y, B (ρ (rootB t) x) (ρ (rootB t) y) = B x y)
    (hC : ∀ t x y, B (ρ (rootC t) x) (ρ (rootC t) y) = B x y)
    (hD : ∀ t x y, B (ρ (rootD t) x) (ρ (rootD t) y) = B x y)
    (hE : ∀ t x y, B (ρ (rootE t) x) (ρ (rootE t) y) = B x y)
    (hF : ∀ t x y, B (ρ (rootF t) x) (ρ (rootF t) y) = B x y)
    (g : Model F) (hg : g ∈ unipotent) (x y : V) :
    B (ρ g x) (ρ g y) = B x y := by
  rw [unipotent_eq_range] at hg
  obtain ⟨t, rfl⟩ := hg
  simp only [unipotentProduct, map_mul, Module.End.mul_apply]
  rw [hA, hB, hC, hD, hE, hF]

/-- Positive-unipotent invariance on the natural coordinate carrier. -/
theorem naturalForm_invariant (g : Model F) (hg : g ∈ unipotent)
    (x y : NaturalCoordinates.Space F) :
    naturalForm F (NaturalCoordinates.action F g x) (NaturalCoordinates.action F g y) = naturalForm F x y := by
  apply invariant_unipotent_of_roots F (NaturalCoordinates.action F) (naturalForm F)
  · intro t x y
    simp [naturalForm, coordPair, NaturalCoordinates.action_rootA]
    ring_nf
    simp [CharTwo.ofNat_eq_mod]
  · intro t x y
    simp [naturalForm, coordPair, NaturalCoordinates.action_rootB]
    ring_nf
    simp [CharTwo.ofNat_eq_mod]
  · intro t x y
    simp [naturalForm, coordPair, NaturalCoordinates.action_rootC]
    ring_nf
    simp [CharTwo.ofNat_eq_mod]
  · intro t x y
    simp [naturalForm, coordPair, NaturalCoordinates.action_rootD]
    ring_nf
    simp [CharTwo.ofNat_eq_mod]
  · intro t x y
    simp [naturalForm, coordPair, NaturalCoordinates.action_rootE]
    ring_nf
    simp [CharTwo.ofNat_eq_mod]
  · intro t x y
    simp [naturalForm, coordPair, NaturalCoordinates.action_rootF]
    ring_nf
    simp [CharTwo.ofNat_eq_mod]
  · exact hg

/-- Positive-unipotent invariance on the adjoint coordinate carrier. -/
theorem adjointCoordinateForm_invariant (g : Model F) (hg : g ∈ unipotent)
    (x y : Adjoint.Coordinates.Space F) :
    adjointCoordinateForm F (Adjoint.Coordinates.action F g x) (Adjoint.Coordinates.action F g y) = adjointCoordinateForm F x y := by
  apply invariant_unipotent_of_roots F (Adjoint.Coordinates.action F) (adjointCoordinateForm F)
  · intro t x y
    simp [adjointCoordinateForm, coordPair, Adjoint.Coordinates.action_rootA]
    ring_nf
    simp [CharTwo.ofNat_eq_mod]
  · intro t x y
    simp [adjointCoordinateForm, coordPair, Adjoint.Coordinates.action_rootB]
    ring_nf
    simp [CharTwo.ofNat_eq_mod]
  · intro t x y
    simp [adjointCoordinateForm, coordPair, Adjoint.Coordinates.action_rootC]
    ring_nf
    simp [CharTwo.ofNat_eq_mod]
  · intro t x y
    simp [adjointCoordinateForm, coordPair, Adjoint.Coordinates.action_rootD]
    ring_nf
    simp [CharTwo.ofNat_eq_mod]
  · intro t x y
    simp [adjointCoordinateForm, coordPair, Adjoint.Coordinates.action_rootE]
    ring_nf
    simp [CharTwo.ofNat_eq_mod]
  · intro t x y
    simp [adjointCoordinateForm, coordPair, Adjoint.Coordinates.action_rootF]
    ring_nf
    simp [CharTwo.ofNat_eq_mod]
  · exact hg

/-- Contract the tensor cube after interchanging its first two factors. -/
def cubeForm : LinearMap.BilinForm F (Steinberg.Ambient F) :=
  ((naturalForm F).tmul ((naturalForm F).tmul (naturalForm F))).compl₁₂
    (TensorProduct.leftComm F _ _ _).toLinearMap LinearMap.id

omit [CharP F 2] in
@[simp] theorem cubeForm_pure (x y z x' y' z' : NaturalCoordinates.Space F) :
    cubeForm F (Steinberg.pure F x y z) (Steinberg.pure F x' y' z') =
      naturalForm F z z' * naturalForm F x y' * naturalForm F y x' := by
  simp [cubeForm, Steinberg.pure, mul_assoc]

attribute [local ext] TensorProduct.ext in
theorem cubeForm_invariant_of_natural (g : Model F)
    (h : ∀ x y, naturalForm F (NaturalCoordinates.action F g x)
      (NaturalCoordinates.action F g y) = naturalForm F x y)
    (x y : Steinberg.Ambient F) :
    cubeForm F (Steinberg.ambientAction F g x) (Steinberg.ambientAction F g y) =
      cubeForm F x y := by
  have he : (cubeForm F).compl₁₂ (Steinberg.ambientAction F g)
      (Steinberg.ambientAction F g) = cubeForm F := by
    ext a b c a' b' c'
    simp [cubeForm, Steinberg.ambientAction, h]
  exact LinearMap.congr_fun (LinearMap.congr_fun he x) y

theorem cubeForm_opposite_seed : cubeForm F (Steinberg.ambientAction F (Steinberg.longestWeyl F)
    (Steinberg.seed F)) (Steinberg.seed F) = 1 := by
  simp [Steinberg.seed, Steinberg.longestWeyl, pow_succ,
    map_mul, Module.End.mul_apply, cubeForm, Steinberg.pure, Steinberg.ambientAction,
    Steinberg.e, naturalForm, coordPair]

/-- A unipotent-invariant form on each of the actual four restricted carriers. -/
def factorForm : (a : Factor) → LinearMap.BilinForm F (Space F a)
  | .trivial => LinearMap.mul F F
  | .natural => naturalForm F
  | .adjoint => (adjointCoordinateForm F).compl₁₂
      (Adjoint.Coordinates.equiv F).toLinearMap (Adjoint.Coordinates.equiv F).toLinearMap
  | .steinberg => (cubeForm F).compl₁₂ (Steinberg.orbitSpan F).toSubmodule.subtype
      (Steinberg.orbitSpan F).toSubmodule.subtype

set_option backward.isDefEq.respectTransparency false in
/-- All four forms are invariant under the actual positive unipotent subgroup. -/
theorem factorForm_invariant (a : Factor) (g : Model F) (hg : g ∈ unipotent)
    (x y : Space F a) :
    factorForm F a (action F a g x) (action F a g y) = factorForm F a x y := by
  cases a with
  | trivial => rfl
  | natural => exact naturalForm_invariant F g hg x y
  | adjoint =>
    change adjointCoordinateForm F (Adjoint.Coordinates.equiv F (Adjoint.action F g x))
      (Adjoint.Coordinates.equiv F (Adjoint.action F g y)) = _
    rw [Adjoint.equiv_action, Adjoint.equiv_action]
    exact adjointCoordinateForm_invariant F g hg _ _
  | steinberg =>
    exact cubeForm_invariant_of_natural F g (naturalForm_invariant F g hg) x.val y.val

/-- Each chosen highest vector pairs to one with its actual opposite. -/
theorem factorForm_opposite_highestVector (a : Factor) :
    factorForm F a (action F a (Steinberg.longestWeyl F) (highestVector F a))
      (highestVector F a) = 1 := by
  cases a with
  | trivial => change (1 : F) * 1 = 1; exact one_mul _
  | natural =>
    change naturalForm F (NaturalCoordinates.action F (Steinberg.longestWeyl F)
      (NaturalCoordinates.highestVector F)) (NaturalCoordinates.highestVector F) = 1
    simp [Steinberg.longestWeyl, pow_succ, map_mul, Module.End.mul_apply,
      naturalForm, coordPair, NaturalCoordinates.highestVector]
  | adjoint =>
    change adjointCoordinateForm F
      (Adjoint.Coordinates.equiv F (Adjoint.action F (Steinberg.longestWeyl F)
        (Adjoint.highestVector F))) (Adjoint.Coordinates.equiv F (Adjoint.highestVector F)) = 1
    rw [Adjoint.equiv_action, Adjoint.equiv_highestVector]
    simp [Steinberg.longestWeyl, pow_succ, map_mul, Module.End.mul_apply,
      adjointCoordinateForm, coordPair, Adjoint.Coordinates.highestVector]
  | steinberg => exact cubeForm_opposite_seed F

end Atlas.G2.TensorClassification.Cyclicity
end
