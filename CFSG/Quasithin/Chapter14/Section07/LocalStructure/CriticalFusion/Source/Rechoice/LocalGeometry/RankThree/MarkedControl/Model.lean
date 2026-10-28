module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.MarkedPartitions.Coordinates
public import Theory.Representation.SL2FourNaturalOrbits.BorelFactors

/-!
# Stabilizers of single displacement planes in the genuine cover

For a nonzero upper parameter t, the plane consists of (t²y,ty,0).
Its natural projection first forces an SL₂(4) stabilizer into the upper
Borel. The central coordinate is fixed by that Borel, so preservation of
this particular plane forces its diagonal entry to be one. Thus its full
SL₂(4) stabilizer is contained in the upper four-group.

This is the marked-cover calculation for Aschbacher--Smith 14.7.70,
printed p.1074. It proves the relative normalizer bound through the actual
quotient; it does not identify an ambient centralizer of V₂.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.MarkedControl
open Representation Representation.SL2FourNatural Representation.SL2FourCentralCover
open Matrix Matrix.SpecialLinearGroup MarkedPartitions

theorem upper_fixes_point (b r x : F) : binaryAction (upper b) (point r x) = point r x := by
  apply coordinates.injective
  change coordinates (fieldAction (upper b) (point r x)) = _
  rw [coordinates_upper, point_coordinates]
  simp

theorem diagonal_point (a : F) (ha : a ≠ 0) (r x : F) :
    binaryAction (diag2 a ha) (point r x) = point r (a * x) := by
  apply coordinates.injective
  rw [coordinates_diagonal, point_coordinates, point_coordinates]
  simp

/-- In the unquotiented cover, one selected displacement plane detects
precisely the unipotent part of an upper triangular actor. -/
theorem preserves_displacement_mem_upper (g : SL) (t : F) (ht : t ≠ 0)
    (h : ∀ y : F, ∃ z : F,
      binaryAction g (point (t ^ 2 * y) (t * y)) = point (t ^ 2 * z) (t * z)) :
    g ∈ upperUnipotent F := by
  obtain ⟨z, hz⟩ := h 1
  simp only [mul_one] at hz
  have hp := congrArg projection hz
  have hpact : projection (binaryAction g (point (t ^ 2) t)) =
      naturalRepresentation g (projection (point (t ^ 2) t)) :=
    LinearMap.congr_fun (projection.isIntertwining' g) _
  rw [hpact, point_projection, point_projection] at hp
  have h10 : g.val 1 0 = 0 := by
    have he := congrFun hp 1
    change (g.val *ᵥ ![t,0]) 1 = 0 at he
    have hh : g.val 1 0 * t = 0 := by
      simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, add_zero] using he
    exact (mul_eq_zero.mp hh).resolve_right ht
  obtain ⟨b, a, ha, hg⟩ := rankOneBorel_factor ⟨g, (mem_rankOneBorel_iff g).mpr h10⟩
  change g = SpecialLinearGroup.transvection zero_ne_one b * diag2 a ha at hg
  have hact : binaryAction g (point (t ^ 2) t) = point (t ^ 2) (a * t) := by
    rw [hg, ← BorelFactors.upper_eq_transvection, map_mul, Module.End.mul_apply,
      diagonal_point, upper_fixes_point]
  rw [hact] at hz
  obtain ⟨hz1, hza⟩ := (point_eq_iff _ _ _ _).mp hz
  have hz' : z = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 ht)
    simpa only [mul_one] using hz1.symm
  have ha1 : a = 1 := by
    rw [hz', mul_one] at hza
    apply mul_right_cancel₀ ht
    simpa only [one_mul] using hza
  subst a
  rw [hg]
  have hd : diag2 1 ha = (1 : SL) := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [diag2_coe']
  rw [hd, mul_one]
  exact (mem_upperUnipotent F _).mpr ⟨b, rfl⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.MarkedControl
