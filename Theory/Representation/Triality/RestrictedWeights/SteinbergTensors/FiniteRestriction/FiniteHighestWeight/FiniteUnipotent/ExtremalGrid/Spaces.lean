module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.RegularFunctions
public import Theory.AlgebraicGroup.Jordan.Translation
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Spaces and finite cells for extremal D₄ interpolation

The spaces below consist of actual regular functions with right Borel
covariance. Left translation preserves them. The finite cells are literal
subgroups of the elementary group, and retain every unipotent fixed point.
The dimension bound and nonzero cell sums are separate proof obligations;
neither is included in the geometric input.

Source: GLS3, Definition 2.8.1 and Theorem 2.8.2; Steinberg,
`refs/KGroup/GLS3/Chapter2St2.tex`, Sections 12 and 13.2(d).
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid
open Theory.AlgebraicGroup
open scoped BigOperators
universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Regular functions with the specified right torus character and root invariance. -/
def covariantSpace (S : Geometry K) (P : Set S.roots.Root) (chi : TorusWeight S.torus) :
    Submodule k K.PolynomialFunction where
  carrier := {f | RootCovariant S P chi f}
  zero_mem' := by intro g t u hu; simp
  add_mem' := by
    intro f h hf hh g t u hu
    change f (g * S.torus.includePoint t * u) + h (g * S.torus.includePoint t * u) = _
    rw [hf g t u hu, hh g t u hu]
    exact (mul_add _ _ _).symm
  smul_mem' := by
    intro c f hf g t u hu
    simp only [polynomialFunction_smul_apply, hf g t u hu]
    ring

/-- Left translation commutes with the defining right covariance. -/
theorem leftTranslate_mem (S : Geometry K) (P : Set S.roots.Root)
    (chi : TorusWeight S.torus) (g : Variety.Point K)
    {f : K.PolynomialFunction} (hf : f ∈ covariantSpace S P chi) :
    leftTranslationPullback K g f ∈ covariantSpace S P chi := by
  intro x t u hu
  simp only [leftTranslationPullback_apply]
  simpa only [mul_assoc] using hf (g * x) t u hu

/-- A linear left translation on the same covariant function space. -/
def leftTranslate (S : Geometry K) (P : Set S.roots.Root)
    (chi : TorusWeight S.torus) (g : Variety.Point K) :
    covariantSpace S P chi →ₗ[k] covariantSpace S P chi :=
  (leftTranslationPullback K g).restrict (fun _ hf => leftTranslate_mem S P chi g hf)

@[simp] theorem leftTranslate_apply (S : Geometry K) (P : Set S.roots.Root)
    (chi : TorusWeight S.torus) (g x : Variety.Point K) (f : covariantSpace S P chi) :
    (leftTranslate S P chi g f).val x = f.val (g * x) :=
  leftTranslationPullback_apply K g x f.val

/-- The root cell inside the literal elementary subgroup. -/
def finiteCell (S : Geometry K) (n : ℕ) (Q : Set S.roots.Root) :
    Subgroup (graphFieldElementarySubgroup S.diagram.toMulEquiv S.frobenius.onPoints n) :=
  (RootSubgroupGenerated S.roots Q).comap (S.inclusion n)

/-- Finiteness follows from the supplied graph-field geometry. -/
theorem finiteCell_finite (S : Geometry K) (n : ℕ) (hn : 0 < n)
    (Q : Set S.roots.Root) : Finite (finiteCell S n Q) := by
  let := S.elementary_finite n hn
  infer_instance

/-- The cell inclusion into the ambient algebraic group. -/
def cellInclusion (S : Geometry K) (n : ℕ) (Q : Set S.roots.Root) :
    finiteCell S n Q →* Variety.Point K :=
  (S.inclusion n).comp (finiteCell S n Q).subtype

/-- The ambient cell inclusion is injective. -/
theorem cellInclusion_injective (S : Geometry K) (n : ℕ) (Q : Set S.roots.Root) :
    Function.Injective (cellInclusion S n Q) :=
  (inclusion_injective S n).comp Subtype.coe_injective

/-- Every element of the finite cell belongs to the corresponding root group. -/
theorem cellInclusion_mem (S : Geometry K) (n : ℕ) (Q : Set S.roots.Root)
    (g : finiteCell S n Q) : cellInclusion S n Q g ∈ RootSubgroupGenerated S.roots Q :=
  g.property

/-- The two-group property passes to the finite cell through its injective inclusion. -/
theorem finiteCell_isPGroup (S : Geometry K) (n : ℕ) (Q : Set S.roots.Root)
    (hQ : IsPGroup 2 (RootSubgroupGenerated S.roots Q)) :
    IsPGroup 2 (finiteCell S n Q) :=
  hQ.comap_of_injective (S.inclusion n) (inclusion_injective S n)

/-- If a root cell's fixed points survive passage to the elementary subgroup,
the two literal cell subgroups are isomorphic by forgetting that membership
proof. Apply this with `positiveFixed_le_elementary` or
`negativeFixed_le_elementary`; no equality of the ambient finite groups occurs. -/
def finiteCellEquivFixed (S : Geometry K) (n : ℕ) (Q : Set S.roots.Root)
    (hkeep : (RootSubgroupGenerated S.roots Q).comap
      (graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n).subtype ≤
        graphFieldElementarySubgroup S.diagram.toMulEquiv S.frobenius.onPoints n) :
    finiteCell S n Q ≃* (RootSubgroupGenerated S.roots Q).comap
      (graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n).subtype where
  toFun g := ⟨g.val.val, g.property⟩
  invFun g := ⟨⟨g.val, hkeep g.property⟩, g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Evaluation on a finite cell, without choosing a polynomial presentation. -/
def cellEvaluation (S : Geometry K) (n : ℕ) (P Q : Set S.roots.Root)
    (chi : TorusWeight S.torus) : covariantSpace S P chi →ₗ[k] (finiteCell S n Q → k) where
  toFun f g := f.val (cellInclusion S n Q g)
  map_add' _ _ := rfl
  map_smul' c f := by ext g; exact polynomialFunction_smul_apply K c f.val _

/-- A nonzero scalar sum of one actual covariant function on the finite cell. -/
def HasNonzeroCellSum (S : Geometry K) (n : ℕ) (P Q : Set S.roots.Root)
    (chi : TorusWeight S.torus) : Prop :=
  ∃ f : covariantSpace S P chi, (∑ᶠ g : finiteCell S n Q, f.val (cellInclusion S n Q g)) ≠ 0

/-- The algebraic dimension estimate required for the two extremal spaces.
This is a proof obligation, not a field of `Geometry`. -/
def DimensionBounds (S : Geometry K) (n : ℕ) : Prop :=
  (FiniteDimensional k (covariantSpace S S.roots.positive
      (S.coordinateEmbedding (maximalRestrictedWeight n))) ∧
    Module.finrank k (covariantSpace S S.roots.positive
      (S.coordinateEmbedding (maximalRestrictedWeight n))) ≤ (2 ^ n) ^ 12) ∧
  (FiniteDimensional k (covariantSpace S (S.roots.neg ⁻¹' S.roots.positive)
      (S.coordinateEmbedding (maximalRestrictedWeight n))⁻¹) ∧
    Module.finrank k (covariantSpace S (S.roots.neg ⁻¹' S.roots.positive)
      (S.coordinateEmbedding (maximalRestrictedWeight n))⁻¹) ≤ (2 ^ n) ^ 12)

/-- The two finite cells have the expected twelve-root cardinality. -/
def CellCardinalities (S : Geometry K) (n : ℕ) : Prop :=
  Nat.card (finiteCell S n (S.roots.neg ⁻¹' S.roots.positive)) = (2 ^ n) ^ 12 ∧
  Nat.card (finiteCell S n S.roots.positive) = (2 ^ n) ^ 12

/-- The two nonzero norm calculations, kept separate from evaluation injectivity. -/
def CellSums (S : Geometry K) (n : ℕ) : Prop :=
  HasNonzeroCellSum S n S.roots.positive (S.roots.neg ⁻¹' S.roots.positive)
    (S.coordinateEmbedding (maximalRestrictedWeight n)) ∧
  HasNonzeroCellSum S n (S.roots.neg ⁻¹' S.roots.positive) S.roots.positive
    (S.coordinateEmbedding (maximalRestrictedWeight n))⁻¹

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid
