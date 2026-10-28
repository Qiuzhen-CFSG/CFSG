module

/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Released under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.Stabilizers
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Orthogonal.OmegaImage.DeletedEightComparison
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The orthogonal six-space inside the exterior square

The six coordinates `0,1,2,4,5,7` identify the actual submodule `V₆` with
the bivector module for a four-dimensional binary space.  The Pfaffian is
transported to `V₆`, and the latter is then identified with the split form
`formD 3`.  The upper-left block of an element of the actual parabolic
`Γ₄` is determinant one; its exterior action is the action on `V₆`.

The comparison with the deleted-eight model records that the image is the
repository's Siegel-generated `Ω⁺₆(2)`, rather than the full orthogonal group.
The model is the one used in Aschbacher--Smith, Lemma 12.5.2(4), printed
pp.817--818 (PDF pp.834--835).
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1200000
open scoped MatrixGroups
namespace Representation.SL5ExteriorSquare

open SL5TenDimensional
open Atlas.Order20160A8 Atlas.Order20160A8.Bivectors
open ClassicalOrthogonal

abbrev Bit := ZMod 2

public def v6Index : Fin 6 → Fin 10 := ![0, 1, 2, 4, 5, 7]

public theorem v6Index_injective : Function.Injective v6Index := by decide

public theorem v6Basis_mem (i : Fin 6) : basis (v6Index i) ∈ V₆ := by
  apply Submodule.subset_span
  fin_cases i <;> simp [v6Index]

public def v6ToSix : V₆ →ₗ[Bit] Six Bit where
  toFun x := fun i => coordinates x.val (v6Index i)
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

public theorem v6ToSix_injective : Function.Injective v6ToSix := by
  intro x y h
  apply Subtype.ext
  apply coordinates.injective
  ext t
  fin_cases t
  · simpa [v6ToSix, v6Index] using congrFun h 0
  · simpa [v6ToSix, v6Index] using congrFun h 1
  · simpa [v6ToSix, v6Index] using congrFun h 2
  · change coordinates x.val 3 = coordinates y.val 3
    rw [(mem_coordinateSpan _ x.val).mp x.property 3 (by decide),
      (mem_coordinateSpan _ y.val).mp y.property 3 (by decide)]
  · simpa [v6ToSix, v6Index] using congrFun h 3
  · simpa [v6ToSix, v6Index] using congrFun h 4
  · change coordinates x.val 6 = coordinates y.val 6
    rw [(mem_coordinateSpan _ x.val).mp x.property 6 (by decide),
      (mem_coordinateSpan _ y.val).mp y.property 6 (by decide)]
  · simpa [v6ToSix, v6Index] using congrFun h 5
  · change coordinates x.val 8 = coordinates y.val 8
    rw [(mem_coordinateSpan _ x.val).mp x.property 8 (by decide),
      (mem_coordinateSpan _ y.val).mp y.property 8 (by decide)]
  · change coordinates x.val 9 = coordinates y.val 9
    rw [(mem_coordinateSpan _ x.val).mp x.property 9 (by decide),
      (mem_coordinateSpan _ y.val).mp y.property 9 (by decide)]

public theorem v6ToSix_surjective : Function.Surjective v6ToSix := by
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [standard_dimensions.2.2.2.1]
        simp [Module.finrank_fintype_fun_eq_card])).mp v6ToSix_injective

/-- The literal six bivector coordinates on the source submodule. -/
public noncomputable def v6Coordinates : V₆ ≃ₗ[Bit] Six Bit :=
  LinearEquiv.ofBijective v6ToSix ⟨v6ToSix_injective, v6ToSix_surjective⟩

@[simp] public theorem v6Coordinates_apply (x : V₆) (i : Fin 6) :
    v6Coordinates x i = coordinates x.val (v6Index i) := rfl

/-- The Pfaffian quadratic form transported to the actual `V₆`. -/
public def v6QuadraticForm : QuadraticForm Bit V₆ :=
  pfaffian.comp v6Coordinates.toLinearMap

public theorem v6QuadraticForm_apply (x : V₆) :
    v6QuadraticForm x =
      coordinates x.val 0 * coordinates x.val 7 +
        coordinates x.val 1 * coordinates x.val 5 +
          coordinates x.val 2 * coordinates x.val 4 := by
  simp [v6QuadraticForm, pfaffian_apply, v6Coordinates, v6ToSix, v6Index,
    sub_eq_add_neg]

/-- An explicit isometry from the actual `V₆` to the split six-dimensional form. -/
public def v6QuadraticIsometry :
    v6QuadraticForm.IsometryEquiv (formD 3 Bit) where
  toLinearEquiv := v6Coordinates.trans Atlas.Order20160A8.Exterior.coordinates
  map_app' x := by
    simpa [v6QuadraticForm] using
      (Atlas.Order20160A8.Exterior.coordinates_form (v6Coordinates x))

public abbrev SL5Group := SL5TenDimensional.Group

public def upperBlock (g : SL5Group) : Matrix (Fin 4) (Fin 4) Bit :=
  fun i j => g.val i.castSucc j.castSucc

private theorem upperBlock_matrix (g : SL5Group) (hg : g ∈ parabolic 4) :
    g.val.submatrix (finSumFinEquiv : Fin 4 ⊕ Fin 1 ≃ Fin 5)
      (finSumFinEquiv : Fin 4 ⊕ Fin 1 ≃ Fin 5) =
      Matrix.fromBlocks (upperBlock g)
        (fun i _ => g.val i.castSucc 4)
        0 !![g.val 4 4] := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · change g.val (Fin.castAdd 1 i) (Fin.castAdd 1 j) = _
    rfl
  · fin_cases j
    change g.val (Fin.castAdd 1 i) (Fin.natAdd 4 (0 : Fin 1)) = _
    rfl
  · fin_cases i
    simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right,
      finSumFinEquiv_apply_left]
    dsimp [Matrix.fromBlocks]
    exact (mem_parabolic_iff_lowerLeft_zero 4 g).mp hg 4 (Fin.castAdd 1 j) (by decide)
      (j.isLt)
  · fin_cases i
    fin_cases j
    change g.val (Fin.natAdd 4 (0 : Fin 1)) (Fin.natAdd 4 (0 : Fin 1)) = _
    rfl

private theorem upperBlock_last (g : SL5Group) (hg : g ∈ parabolic 4) :
    g.val 4 4 = 1 := by
  have hrow (j : Fin 5) (hj : j.val < 4) : g.val 4 j = 0 :=
    (mem_parabolic_iff_lowerLeft_zero 4 g).mp hg 4 j (by decide) hj
  have hne : g.val 4 4 ≠ 0 := by
    intro hz
    have hd := Matrix.det_eq_zero_of_row_eq_zero (A := g.val) 4 (by
      intro j
      by_cases hj : j.val < 4
      · exact hrow j hj
      · have he : j = 4 := by ext; omega
        simpa [he] using hz)
    rw [g.property] at hd
    exact one_ne_zero hd
  exact (by decide : ∀ a : Bit, a ≠ 0 → a = 1) _ hne

public theorem upperBlock_det (g : SL5Group) (hg : g ∈ parabolic 4) :
    (upperBlock g).det = 1 := by
  have hdet := Matrix.det_submatrix_equiv_self
    (finSumFinEquiv : Fin 4 ⊕ Fin 1 ≃ Fin 5) g.val
  rw [upperBlock_matrix g hg] at hdet
  calc
    (upperBlock g).det = (upperBlock g).det * g.val 4 4 := by
      rw [upperBlock_last g hg, mul_one]
    _ = (Matrix.fromBlocks (upperBlock g)
        (fun i _ => g.val i.castSucc 4) 0 !![g.val 4 4]).det := by
      symm
      simpa using (Matrix.det_fromBlocks_zero₂₁ (R := Bit) (upperBlock g)
        (fun i _ => g.val i.castSucc 4) (!![g.val 4 4]))
    _ = g.val.det := hdet
    _ = 1 := g.property

/-- The actual `SL₄(2)` element represented by the upper-left parabolic block. -/
public noncomputable def parabolicFourBlock (g : parabolic 4) :
    Matrix.SpecialLinearGroup (Fin 4) Bit :=
  ⟨upperBlock g.val, upperBlock_det g.val g.property⟩

public noncomputable def exteriorToOmega :
    Matrix.SpecialLinearGroup (Fin 4) Bit →*
      ClassicalOrthogonal.OmegaPlus 3 Bit :=
  (Atlas.Order20160A8.Exterior.toOrthogonal (F := Bit)).codRestrict _ (by
    intro g
    change Atlas.Order20160A8.Exterior.toOrthogonal g ∈
      elementarySubgroup (formD 3 Bit)
    rw [← Atlas.Order20160A8.DeletedEight.alternatingImage_eq_elementary]
    apply Subgroup.mem_map.mpr
    let a := Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
      (Atlas.Order20160A8.sl4TwoEquivPSL g)
    refine ⟨a.val, a.property, ?_⟩
    exact Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8_orthogonal g)

public theorem exteriorToOmega_injective : Function.Injective exteriorToOmega := by
  intro g h gh
  apply Atlas.Order20160A8.Exterior.binary_injective
  change Atlas.Order20160A8.Exterior.toOrthogonal g =
    Atlas.Order20160A8.Exterior.toOrthogonal h
  exact congrArg Subtype.val gh

public theorem exteriorToOmega_surjective : Function.Surjective exteriorToOmega := by
  intro q
  have hqmem : q.val ∈ elementarySubgroup (formD 3 Bit) := q.property
  rw [← Atlas.Order20160A8.DeletedEight.alternatingImage_eq_elementary] at hqmem
  obtain ⟨a, ha, hq⟩ := hqmem
  obtain ⟨p, hp⟩ := Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.surjective ⟨a, ha⟩
  obtain ⟨g, hg⟩ := Atlas.Order20160A8.sl4TwoEquivPSL.surjective p
  refine ⟨g, ?_⟩
  apply Subtype.ext
  change Atlas.Order20160A8.Exterior.toOrthogonal g = q.val
  calc
    Atlas.Order20160A8.Exterior.toOrthogonal g =
        Atlas.Order20160A8.DeletedEight.orthogonalHom
        (Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
          (Atlas.Order20160A8.sl4TwoEquivPSL g)).val :=
      (Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8_orthogonal g).symm
    _ = q.val := by simpa [hp, hg] using hq

/-- The genuine actor on the split six-space. -/
public noncomputable def sl4TwoOmegaEquiv :
    Matrix.SpecialLinearGroup (Fin 4) Bit ≃* ClassicalOrthogonal.OmegaPlus 3 Bit :=
  MulEquiv.ofBijective exteriorToOmega
    ⟨exteriorToOmega_injective, exteriorToOmega_surjective⟩

public theorem sl4TwoOmegaEquiv_linear (a : Matrix.SpecialLinearGroup (Fin 4) Bit) :
    (sl4TwoOmegaEquiv a).val.val = Atlas.Order20160A8.Exterior.onD a := by
  change (Atlas.Order20160A8.Exterior.toOrthogonal a).val = _
  rfl

public noncomputable def v6Action (g : parabolic 4) : V₆ →ₗ[Bit] V₆ where
  toFun x := ⟨exteriorAction 2 g.val x.val, by
    have hs : g.val ∈ exteriorStabilizer V₆ := by
      rw [exteriorStabilizer_V₆_eq_parabolic]
      exact g.property
    exact ((mem_subspaceStabilizer (exteriorAction 2) V₆ g.val).mp hs x.val).mpr x.property⟩
  map_add' x y := by apply Subtype.ext; simp
  map_smul' c x := by apply Subtype.ext; simp

public theorem v6Action_apply (g : parabolic 4) (x : V₆) :
    (v6Action g x).val = exteriorAction 2 g.val x.val := rfl

end Representation.SL5ExteriorSquare
