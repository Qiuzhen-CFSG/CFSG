module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.Words
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Coordinates for the F4 adjoint block in the folded E6 lattice

The real linear projection sends E6 nodes `[0,1,2,3,4,5]` to F4 nodes
`[3,2,1,0,2,3]`. Its fibre incidence matrix gives an integral map from the
52-coordinate F4 Geck lattice to the 78-coordinate E6 Geck lattice: Cartan
coordinates are repeated on diagram orbits, and each root coordinate is
repeated on its projection fibre. The entries are zero or one.

The projection and the image of this matrix are invariant under the literal
pinned diagram permutation. A lift of every F4 root proves injectivity over
any coefficient ring, by reading one coordinate in each fibre. Root lifting
and compatibility with the Geck operators are separate obligations; neither
is assumed as an instance or asserted by the definitions here.

Sources: the F4 inclusions in Aschbacher--Smith A.2.17, printed p.39 of
`refs/quasithin.pdf`; GLS3 §§2.2--2.6; the coordinate root systems and integral
Geck operators imported through `Words`.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.AdjointRestriction
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _

abbrev SourceIndex := typeF4RootPairing_base.support ⊕ typeF4Roots

/-- The F4 number of an E6 node. -/
def node : Fin 6 → Fin 4 := ![3, 2, 1, 0, 2, 3]

@[simp] theorem node_diagram (i : Fin 6) :
    node (typeE6DiagramPermutation i) = node i := by
  fin_cases i <;> rfl

/-- Linear restriction of E6 roots to the fixed Cartan space, in the existing F4 coordinates. -/
def rootProjection : Vec 8 →ₗ[ℝ] Vec 4 where
  toFun x := ![(5 * x 0 + x 1 + x 2 + x 3) / 2,
    (x 4 + x 5 + x 6 + x 7) / 2,
    (x 4 + x 5 - x 6 - x 7) / 2,
    (x 4 - x 5 + x 6 - x 7) / 2]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp <;> ring

@[simp] theorem rootProjection_simple (i : Fin 6) :
    rootProjection (typeE6SimpleRoot i) = typeF4SimpleRoot (node i) := by
  fin_cases i <;> ext j <;> fin_cases j
  · change ((5 * (1 / 2) + (-(1 / 2)) + (-(1 / 2)) + (-(1 / 2))) / 2 : ℝ) = (1 / 2)
    norm_num
  · change (((-(1 / 2)) + (-(1 / 2)) + (-(1 / 2)) + (1 / 2)) / 2 : ℝ) = (-(1 / 2))
    norm_num
  · change (((-(1 / 2)) + (-(1 / 2)) - (-(1 / 2)) - (1 / 2)) / 2 : ℝ) = (-(1 / 2))
    norm_num
  · change (((-(1 / 2)) - (-(1 / 2)) + (-(1 / 2)) - (1 / 2)) / 2 : ℝ) = (-(1 / 2))
    norm_num
  · change ((5 * 0 + 0 + 0 + 0) / 2 : ℝ) = 0
    norm_num
  · change ((0 + 0 + 1 + (-1)) / 2 : ℝ) = 0
    norm_num
  · change ((0 + 0 - 1 - (-1)) / 2 : ℝ) = 0
    norm_num
  · change ((0 - 0 + 1 - (-1)) / 2 : ℝ) = 1
    norm_num
  · change ((5 * 0 + 0 + 0 + 0) / 2 : ℝ) = 0
    norm_num
  · change ((0 + 1 + (-1) + 0) / 2 : ℝ) = 0
    norm_num
  · change ((0 + 1 - (-1) - 0) / 2 : ℝ) = 1
    norm_num
  · change ((0 - 1 + (-1) - 0) / 2 : ℝ) = (-1)
    norm_num
  · change ((5 * 0 + 0 + 0 + 0) / 2 : ℝ) = 0
    norm_num
  · change ((0 + 0 + 1 + 1) / 2 : ℝ) = 1
    norm_num
  · change ((0 + 0 - 1 - 1) / 2 : ℝ) = (-1)
    norm_num
  · change ((0 - 0 + 1 - 1) / 2 : ℝ) = 0
    norm_num
  · change ((5 * 0 + 0 + 0 + 0) / 2 : ℝ) = 0
    norm_num
  · change ((1 + (-1) + 0 + 0) / 2 : ℝ) = 0
    norm_num
  · change ((1 + (-1) - 0 - 0) / 2 : ℝ) = 0
    norm_num
  · change ((1 - (-1) + 0 - 0) / 2 : ℝ) = 1
    norm_num
  · change ((5 * 0 + 0 + 0 + 1) / 2 : ℝ) = (1 / 2)
    norm_num
  · change (((-1) + 0 + 0 + 0) / 2 : ℝ) = (-(1 / 2))
    norm_num
  · change (((-1) + 0 - 0 - 0) / 2 : ℝ) = (-(1 / 2))
    norm_num
  · change (((-1) - 0 + 0 - 0) / 2 : ℝ) = (-(1 / 2))
    norm_num

/-- The restriction is invariant under the actual pinned diagram action on roots. -/
theorem rootProjection_diagram (r : typeE6Roots) :
    rootProjection (typeE6DiagramEquiv.indexEquiv r).val = rootProjection r.val := by
  let q : typeE6RootSpan →ₗ[ℝ] Vec 4 := rootProjection.comp typeE6RootSpan.subtype
  have h : q.comp typeE6DiagramEquiv.weightMap = q := by
    apply typeE6RootPairing_base.toWeightBasis.ext
    intro i
    obtain ⟨i, rfl⟩ := typeE6RootPairing_baseEquiv.surjective i
    simp only [RootPairing.Base.toWeightBasis_apply, LinearMap.comp_apply]
    change q (typeE6DiagramEquiv.weightMap
      (typeE6RootPairing.root (typeE6RootPairing_baseEquiv i))) =
      q (typeE6RootPairing.root (typeE6RootPairing_baseEquiv i))
    rw [RootPairing.Hom.root_weightMap_apply, typeE6DiagramEquiv_simple,
      typeE6DiagramBasePermutation_numbered]
    change rootProjection (typeE6SimpleRoot (typeE6DiagramPermutation i)) =
      rootProjection (typeE6SimpleRoot i)
    simp
  have hh := LinearMap.congr_fun h (typeE6RootPairing.root r)
  change q (typeE6DiagramEquiv.weightMap (typeE6RootPairing.root r)) =
    q (typeE6RootPairing.root r) at hh
  rw [RootPairing.Hom.root_weightMap_apply] at hh
  exact hh

/-- Integral orbit-sum matrix from the F4 Geck lattice into the E6 Geck lattice. -/
def latticeMatrix : Matrix TwistedE6.Index SourceIndex ℤ
  | .inl i, .inl j => if sourceIndex (node (typeE6RootPairing_baseEquiv.symm i)) = j then 1 else 0
  | .inr r, .inr s => if rootProjection r.val = s.val then 1 else 0
  | _, _ => 0

/-- Scalar extension of the actual integral orbit-sum matrix. -/
def matrix (R : Type*) [CommRing R] : Matrix TwistedE6.Index SourceIndex R :=
  latticeMatrix.map (Int.castRingHom R)

/-- The concrete comparison acts on column vectors. -/
def linearMap (R : Type*) [CommRing R] :
    (SourceIndex → R) →ₗ[R] (TwistedE6.Index → R) := (matrix R).mulVecLin

@[simp] theorem matrix_cartan (R : Type*) [CommRing R] (i : Fin 6)
    (j : typeF4RootPairing_base.support) :
    matrix R (.inl (simpleIndex i)) (.inl j) =
      if sourceIndex (node i) = j then 1 else 0 := by
  simp [matrix, latticeMatrix, simpleIndex]

@[simp] theorem matrix_root (R : Type*) [CommRing R]
    (r : typeE6Roots) (s : typeF4Roots) :
    matrix R (.inr r) (.inr s) =
      if rootProjection r.val = s.val then 1 else 0 := by
  simp [matrix, latticeMatrix]

theorem linearMap_cartan (R : Type*) [CommRing R] (x : SourceIndex → R) (i : Fin 6) :
    linearMap R x (.inl (simpleIndex i)) = x (.inl (sourceIndex (node i))) := by
  simp [linearMap, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    matrix, latticeMatrix, simpleIndex]

theorem linearMap_root (R : Type*) [CommRing R] (x : SourceIndex → R)
    (r : typeE6Roots) (s : typeF4Roots) (h : rootProjection r.val = s.val) :
    linearMap R x (.inr r) = x (.inr s) := by
  have he (t : typeF4Roots) : rootProjection r.val = t.val ↔ t = s := by
    rw [h]
    exact ⟨fun ht => Subtype.ext ht.symm, fun ht => ht ▸ rfl⟩
  simp [linearMap, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    matrix, latticeMatrix, he]

/-- Root lifting suffices for injectivity, with no restriction on the coefficient characteristic. -/
theorem linearMap_injective_of_root_lifts (R : Type*) [CommRing R]
    (hlift : ∀ s : typeF4Roots, ∃ r : typeE6Roots, rootProjection r.val = s.val) :
    Function.Injective (linearMap R) := by
  intro x y h
  funext k
  rcases k with i | s
  · obtain ⟨i, rfl⟩ := typeF4RootPairing_baseEquiv.surjective i
    let j : Fin 6 := ![3, 2, 1, 0] i
    have hj : node j = i := by fin_cases i <;> rfl
    have hh := congrFun h (.inl (simpleIndex j))
    simpa only [linearMap_cartan, hj] using hh
  · obtain ⟨r, hr⟩ := hlift s
    have hh := congrFun h (.inr r)
    simpa only [linearMap_root R x r s hr, linearMap_root R y r s hr] using hh

/-- Every column lies in the fixed space of the literal pinned permutation. -/
theorem matrix_diagram (R : Type*) [CommRing R] (i : TwistedE6.Index) (j : SourceIndex) :
    matrix R (typeE6PinnedIndexEquiv i) j = matrix R i j := by
  rcases i with i | r <;> rcases j with j | s
  · obtain ⟨i, rfl⟩ := typeE6RootPairing_baseEquiv.surjective i
    simp [matrix, latticeMatrix, typeE6DiagramBasePermutation_numbered]
  · simp [matrix, latticeMatrix]
  · simp [matrix, latticeMatrix]
  · simp [matrix, latticeMatrix, rootProjection_diagram]

theorem linearMap_diagram (R : Type*) [CommRing R] (x : SourceIndex → R)
    (i : TwistedE6.Index) :
    linearMap R x (typeE6PinnedIndexEquiv i) = linearMap R x i := by
  simp only [linearMap, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, matrix_diagram]

end TwistedE6.FoldedSubsystem.F4Identification.AdjointRestriction
