module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/DistinguishedPlane.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, public module boundaries, and Lean 4.33 proof adaptation.
-/

public import Theory.AtlasPort.LinearGroups.G2.PointStabilizer

/-! The distinguished octonion plane and its singular points give the only potential intermediate block. -/

@[expose] public section

namespace Atlas.G2
open Atlas.SplitOctonion
variable {K : Type*} [Field K]

/-- The singular plane spanned by x1,x2,x3. -/
def distinguishedPlane : Submodule K (Carrier K) where
  carrier := {x | ∀ i : Fin 8, 3 ≤ i.val → x i = 0}
  zero_mem' := by simp
  add_mem' hx hy i hi := by simp [hx i hi,hy i hi]
  smul_mem' a x hx i hi := by simp [hx i hi]

theorem basis_mem_distinguishedPlane (i : Fin 8) (hi : i.val < 3) :
    basisVector i ∈ distinguishedPlane (K := K) := by
  intro j hj
  have hne : j ≠ i := by intro h; subst j; omega
  simp [basisVector,hne]

theorem distinguishedPlane_coordinates {x : Carrier K} (hx : x ∈ distinguishedPlane) :
    x = ![x 0,x 1,x 2,0,0,0,0,0] := by
  funext i
  fin_cases i
  all_goals first | rfl | exact hx _ (by decide)

theorem distinguishedPlane_mul {x y : Carrier K}
    (hx : x ∈ distinguishedPlane) (hy : y ∈ distinguishedPlane) :
    SplitOctonion.mul x y = (x 2 * y 1 - x 1 * y 2) • basisVector 0 := by
  have ex := distinguishedPlane_coordinates hx
  have ey := distinguishedPlane_coordinates hy
  rw [ex,ey]
  funext i
  fin_cases i <;> simp [SplitOctonion.mul,basisVector]; ring

/-- The span of products of vectors in the plane is its distinguished x1 line. -/
theorem distinguishedPlane_product_span :
    Submodule.span K {z : Carrier K | ∃ x ∈ distinguishedPlane,
      ∃ y ∈ distinguishedPlane, SplitOctonion.mul x y = z} =
      Submodule.span K {basisVector (F := K) 0} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨x,hx,y,hy,rfl⟩
    rw [distinguishedPlane_mul hx hy]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · apply Submodule.span_le.mpr
    intro x hx
    have he : x = basisVector 0 := Set.mem_singleton_iff.mp hx
    rw [he]
    apply Submodule.subset_span
    refine ⟨basisVector 2,basis_mem_distinguishedPlane 2 (by decide),
      basisVector 1,basis_mem_distinguishedPlane 1 (by decide),?_⟩
    funext i
    fin_cases i <;> simp [SplitOctonion.mul,basisVector]


/-- Setwise preservation of the plane forces preservation of its intrinsic product line. -/
theorem plane_preserver_mem_pointStabilizer (g : Model K)
    (hg : ∀ x ∈ distinguishedPlane, g.val x ∈ distinguishedPlane) :
    g ∈ pointStabilizer := by
  have h21 : SplitOctonion.mul (basisVector (F := K) 2) (basisVector 1) = basisVector 0 := by
    funext i
    fin_cases i <;> simp [SplitOctonion.mul,basisVector]
  have hge : g.val (basisVector 0) =
      ((g.val (basisVector 2)) 2 * (g.val (basisVector 1)) 1 -
        (g.val (basisVector 2)) 1 * (g.val (basisVector 1)) 2) • basisVector 0 := by
    conv_lhs => rw [← h21,automorphism_mul]
    exact distinguishedPlane_mul (hg _ (basis_mem_distinguishedPlane 2 (by decide)))
      (hg _ (basis_mem_distinguishedPlane 1 (by decide)))
  let a := (g.val (basisVector 2)) 2 * (g.val (basisVector 1)) 1 -
        (g.val (basisVector 2)) 1 * (g.val (basisVector 1)) 2
  have ha : a ≠ 0 := by
    intro h
    have hz : g.val (basisVector 0) = 0 := by simpa [a,h] using hge
    exact first_basis_ne_zero (g.val.injective (hz.trans (map_zero g.val).symm))
  apply (mem_pointStabilizer_iff g).mpr
  exact ⟨Units.mk0 a ha,by simpa only [Units.smul_def,Units.val_mk0] using hge⟩

end Atlas.G2

