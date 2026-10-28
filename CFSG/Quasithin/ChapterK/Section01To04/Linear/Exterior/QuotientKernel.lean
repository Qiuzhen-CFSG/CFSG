module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.RadicalGeometry
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.Stabilizers

/-!
# The quotient kernel on the SL₅(2) exterior square

On the literal quotient Λ²(F₂⁵)/Λ²(F₂⁴), the kernel is the subgroup of
last-column shears. A trivial quotient action preserves Λ²(F₂⁴), hence its
natural hyperplane. The exterior minors then force the upper-left block to
be the identity; the determinant and the binary field determine the last row.
This discharges the quotient-faithfulness step in K.3.2.3 without an assumed
parabolic quotient identification.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.2.3,
printed p.455, using the concrete geometry from §12.5.
-/

public section
open Representation Representation.SL5TenDimensional Representation.SL5ExteriorSquare

namespace CFSG.Quasithin.ChapterK.Linear.Exterior

/-- The literal action kernel on V/V₆ is the last-column radical. -/
theorem quotient_kernel (g : Group) :
    (∀ v : V, exteriorAction 2 g v - v ∈ V₆) ↔ g ∈ shearSubgroup := by
  constructor
  · intro h
    have hstab : g ∈ exteriorStabilizer V₆ := by
      apply (mem_subspaceStabilizer_iff_preserves _ _ _).mpr
      intro v hv
      simpa only [sub_add_cancel] using V₆.add_mem (h v) hv
    rw [exteriorStabilizer_V₆_eq_parabolic] at hstab
    have hrow (j : Fin 5) (hj : j.val < 4) : g.val 4 j = 0 :=
      (mem_parabolic_iff_lowerLeft_zero 4 g).mp hstab 4 j (by decide) hj
    have hlast : g.val 4 4 = 1 := by
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
      exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hne
    have hq (v : V) : shearQuotient (exteriorAction 2 g v) = shearQuotient v := by
      have he := (mem_V₆_iff_shearQuotient _).mp (h v)
      rwa [map_sub, sub_eq_zero] at he
    have hblock (i j : Fin 4) : g.val i.castSucc j.castSucc = if i = j then 1 else 0 := by
      have he := congrFun (hq (basis (![3,6,8,9] j))) i
      simp only [shearQuotient, LinearMap.coe_mk, AddHom.coe_mk, coordinates_action,
        coordinates_basis, Matrix.mulVec_single_one, Matrix.col_apply] at he
      fin_cases i <;> fin_cases j <;>
        simpa [actionMatrix, pair, hlast, hrow 0 (by decide), hrow 1 (by decide),
          hrow 2 (by decide), hrow 3 (by decide), -coordinates_apply] using he
    apply (mem_shearSubgroup g).mpr
    refine ⟨fun i => g.val i.castSucc 4, ?_⟩
    apply Subtype.ext
    rw [matrix_shear]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hrow 0 (by decide), hrow 1 (by decide), hrow 2 (by decide),
        hrow 3 (by decide), hlast]
    all_goals first
      | exact (hblock 0 0).symm
      | exact (hblock 0 1).symm
      | exact (hblock 0 2).symm
      | exact (hblock 0 3).symm
      | exact (hblock 1 0).symm
      | exact (hblock 1 1).symm
      | exact (hblock 1 2).symm
      | exact (hblock 1 3).symm
      | exact (hblock 2 0).symm
      | exact (hblock 2 1).symm
      | exact (hblock 2 2).symm
      | exact (hblock 2 3).symm
      | exact (hblock 3 0).symm
      | exact (hblock 3 1).symm
      | exact (hblock 3 2).symm
      | exact (hblock 3 3).symm
  · intro hg v
    obtain ⟨u, rfl⟩ := (mem_shearSubgroup g).mp hg
    change SL5ExteriorSquare.displacement (shear u) v ∈ V₆
    rw [shear_displacement]
    exact shearWedge_mem_V₆ _ _

end CFSG.Quasithin.ChapterK.Linear.Exterior
