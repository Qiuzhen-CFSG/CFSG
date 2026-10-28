module

public import Theory.AlgebraicGroup.Bor1.BorelHomogeneousSpace
public import Theory.AlgebraicGroup.Borel.Conjugation.theorem_1_6_2_b
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy

/-!
The algebraic final step of Borel conjugacy.

A Borel fixing a point of the Pluecker orbit of another Borel equals the
corresponding conjugate: the point stabilizer gives containment, and maximal
connected solvability gives equality. The unconditional conjugacy theorem is
imported from the complete-orbit construction; the fixed-point lemmas below
also expose the algebraic last step for callers with their own orbit model.

Source: Borel, *Linear Algebraic Groups*, Section 11.1, final paragraph;
GLS3, Theorem 1.6.2(b). The imported unresolved numbered conjugacy theorem is
not used, only the independently proved preservation of Borel subgroups by
conjugation in the fixed-point lemmas.
-/

universe u

namespace Theory.AlgebraicGroup.BorelIntersectionGeometry

open Bor1

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- Any two Borel subgroups are conjugate.

The complete flag-orbit construction and the solvable fixed-point argument are
carried out in `BorelGeometricConjugacy.conjugacy`. This namespace-local
export is the interface used by the Borel-intersection assembly. It does not
use the unresolved numbered theorem from the legacy conjugation module.
-/
public theorem borels_conjugate {B C : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) (hC : IsBorelSubgroup C) :
    ∃ g : Variety.Point G, C = B.conjugate g := by
  exact BorelGeometricConjugacy.conjugacy hB hC

/-- Maximality turns the stabilizer containment at a fixed orbit point into
equality with a conjugate Borel. -/
public theorem borel_conjugate_of_homogeneousSpace_fixed
    {R B : ClosedSubgroup G} (hR : IsBorelSubgroup R) (hB : IsBorelSubgroup B)
    (x : borelHomogeneousSpace R)
    (hfix : ∀ b : Variety.Point G, b ∈ B.toSubgroup → b • x = x) :
    ∃ g : Variety.Point G, B = R.conjugate g := by
  obtain ⟨g, hg⟩ := subgroup_le_conjugate_of_homogeneousSpace_fixed R B.toSubgroup x hfix
  have hRg := hR.conjugate g
  exact ⟨g, (hB.maximal (R.conjugate g) hRg.connected hRg.solvable hg).symm⟩

/-- Two Borels with fixed points on one Borel homogeneous space are conjugate.
Only one complete homogeneous space will therefore be needed by the geometric
assembly, as in the maximal-dimension choice of Borel in the source. -/
public theorem borels_conjugate_of_common_homogeneousSpace_fixed
    {R B C : ClosedSubgroup G}
    (hR : IsBorelSubgroup R) (hB : IsBorelSubgroup B) (hC : IsBorelSubgroup C)
    (x y : borelHomogeneousSpace R)
    (hBfix : ∀ b : Variety.Point G, b ∈ B.toSubgroup → b • x = x)
    (hCfix : ∀ c : Variety.Point G, c ∈ C.toSubgroup → c • y = y) :
    ∃ g : Variety.Point G, C = B.conjugate g := by
  obtain ⟨b, hb⟩ := borel_conjugate_of_homogeneousSpace_fixed hR hB x hBfix
  obtain ⟨c, hc⟩ := borel_conjugate_of_homogeneousSpace_fixed hR hC y hCfix
  refine ⟨c * b⁻¹, ?_⟩
  rw [hb, ClosedSubgroup.conjugate_conjugate]
  simpa only [inv_mul_cancel_right] using hc

end Theory.AlgebraicGroup.BorelIntersectionGeometry
