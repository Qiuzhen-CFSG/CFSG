module

public import Theory.Representation.OrthogonalFourPlusMatrix.OuterWeakClosureGeometry.SingularLine
public import Theory.Representation.OrthogonalFourPlusMatrix.OuterWeakClosureGeometry.Transport
public import Theory.Representation.OrthogonalFourPlusMatrix.OuterWeakClosureGeometry.FixedLine

/-!
# Outer weak-closure geometry in the original binary tensor normalizer

A rank-at-least-three elementary actor outside the inner determinant group,
once it fixes a singular coefficient line pointwise, has a binary subspace
whose pointwise action kernel has index at most four. Its actual displacement
span contains nonsingular vectors on two distinct coefficient lines.

The inner coordinate action transports the proved standard fixed-line
geometry back to the original subgroup, preserving its kernel and literal
operators. Together with the invariant singular-line theorem, this gives the
two geometric steps of Aschbacher–Smith 9.4.5, printed pp.736–737: the first
kernel has index at most two, and the final kernel has index at most four.
The ambient weak-closure argument supplies pointwise centralization between
these steps.
-/

@[expose] public noncomputable section
open Module Matrix Subgroup
open Representation.BinaryOffender Representation.BinaryOffender.NaturalTensor
namespace ClassicalOrthogonal.FourPlusMatrix.Binary

local instance : Finite (Module.End (ZMod 2) V) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

/-- The actual binary span of normalizer displacements on a subspace. -/
def normalizerMovedSpace (B : Subgroup (linearNormalizer action))
    (U : Submodule (ZMod 2) V) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {z | ∃ h : B, ∃ v ∈ U, h.val.val.val v - v = z}

/-- The outer elementary actor has a small action quotient and a nonsingular pair. -/
theorem outer_fixed_line_geometry
    (B : Subgroup (linearNormalizer action)) (hB : IsElementaryTwo B)
    (hr : 3 ≤ rank B)
    (houter : ¬ B.map (linearNormalizer action).subtype ≤ actionImage action)
    (v : V) (hv : v ≠ 0) (hs : v.det = 0)
    (hfix : ∀ h : B, ∀ c : F, h.val.val.val (c • v) = c • v) :
    ∃ U : Submodule (ZMod 2) V, ∃ K : Subgroup B,
      K.index ≤ 4 ∧ (∀ h ∈ K, ∀ w ∈ U, h.val.val.val w = w) ∧
      ∃ x ∈ normalizerMovedSpace B U, ∃ y ∈ normalizerMovedSpace B U,
        x.det ≠ 0 ∧ y.det ≠ 0 ∧ y ∉ Submodule.span F ({x} : Set V) := by
  obtain ⟨D⟩ := exists_outerFixedLineActor B hB hr houter v hv hs hfix
  obtain ⟨U,K,hK,hKU,x,hx,y,hy,hxn,hyn,hxy⟩ :=
    OuterWeakClosureGeometry.FixedLine.fixed_unit_geometry
      D.fieldAction D.injective D.determinant D.commuting D.involutions
      D.fixesUnit D.card_ge_eight D.outer
  let e := matrixHom D.coordinate
  let eb := e.restrictScalars (ZMod 2)
  let W := U.map eb.toLinearMap
  have hspace : OuterWeakClosureGeometry.FixedLine.Normalized.movedSpace D.fieldAction U ≤
      (normalizerMovedSpace B W).comap eb.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro z ⟨h,w,hw,rfl⟩
    change e (D.fieldAction h w - w) ∈ normalizerMovedSpace B W
    rw [map_sub]
    change matrixHom D.coordinate (D.fieldAction h w) - e w ∈ _
    rw [D.equivariant]
    exact Submodule.subset_span ⟨h,e w,⟨w,hw,rfl⟩,rfl⟩
  refine ⟨W,K,hK,?_,e x,hspace hx,e y,hspace hy,?_,?_,?_⟩
  · intro h hh w hw
    obtain ⟨z,hz,rfl⟩ := hw
    have he := congrArg e (hKU h hh z hz)
    change e (D.fieldAction h z) = e z at he
    change h.val.val.val (e z) = e z
    rw [show e (D.fieldAction h z) = h.val.val.val (e z) from D.equivariant h z] at he
    exact he
  · change (matrixAction D.coordinate x).det ≠ 0
    rw [matrixAction_det]
    exact hxn
  · change (matrixAction D.coordinate y).det ≠ 0
    rw [matrixAction_det]
    exact hyn
  · intro hyx
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hyx
    apply hxy
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c,e.injective ?_⟩
    simpa only [map_smul] using hc

/-- Apply the outer geometry to the very singular line produced by the first step. -/
theorem outer_singularLineData_geometry
    (B : Subgroup (linearNormalizer action)) (hB : IsElementaryTwo B)
    (hr : 3 ≤ rank B)
    (houter : ¬ B.map (linearNormalizer action).subtype ≤ actionImage action)
    (D : NormalizerSingularLineData B.subtype)
    (hfix : ∀ h : B, ∀ v ∈ D.line, h.val.val.val v = v) :
    ∃ U : Submodule (ZMod 2) V, ∃ K : Subgroup B,
      K.index ≤ 4 ∧ (∀ h ∈ K, ∀ w ∈ U, h.val.val.val w = w) ∧
      ∃ x ∈ normalizerMovedSpace B U, ∃ y ∈ normalizerMovedSpace B U,
        x.det ≠ 0 ∧ y.det ≠ 0 ∧ y ∉ Submodule.span F ({x} : Set V) := by
  apply outer_fixed_line_geometry B hB hr houter D.vector D.vector_ne_zero D.vector_singular
  intro h c
  exact hfix h (c • D.vector) ⟨c,rfl⟩

end ClassicalOrthogonal.FourPlusMatrix.Binary
