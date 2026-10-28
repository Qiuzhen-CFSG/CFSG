module
public import Theory.Representation.BinaryParabolicExteriorSquare.PlaneSpan

/-!
# Point-radical displacement on the exterior square

An operator acting trivially on the natural four-space modulo its first
coordinate line acts trivially on the exterior six-space modulo the first
exterior three-space. Comparing the last three rows with the identity makes
the three surviving compound-matrix coordinates explicit.

This is the point-radical calculation used in Aschbacher--Smith 13.8.29(4),
printed p.964, to descend the second tensor through the actual two-core.
The exterior model retains the attribution of its imported ATLAS source.
-/

public section
open Atlas.Order20160A8.Bivectors
open Representation.BinaryParabolicExteriorSquare.PlaneSpan

namespace Representation.BinaryParabolicExteriorSquare

/-- Natural displacement in the fixed point gives exterior displacement in its three-space. -/
theorem exterior_displacement_of_point_displacement
    (A : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (hA : ∀ v, A.mulVec v - v ∈ Submodule.span (ZMod 2) {Pi.single 0 1})
    (x : Six) : exteriorMap A x - x ∈ firstSpace := by
  have hrow (i j : Fin 4) (hi : i ≠ 0) : A i j = if i = j then 1 else 0 := by
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hA (Pi.single j 1))
    have hh := congrFun hc i
    simp only [Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero, Pi.sub_apply,
      Matrix.mulVec_single] at hh
    have he : A i j = (Pi.single j 1 : Fin 4 → ZMod 2) i := sub_eq_zero.mp (by simpa using hh.symm)
    rw [he]
    by_cases hij : i = j
    · subst j; simp
    · simp [hij]
  change (exteriorMap A x - x) 3 = 0 ∧ (exteriorMap A x - x) 4 = 0 ∧
    (exteriorMap A x - x) 5 = 0
  simp [exteriorMap, compound, first, second, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hrow 1 _ (by decide),
    hrow 2 _ (by decide), hrow 3 _ (by decide)]

end Representation.BinaryParabolicExteriorSquare

