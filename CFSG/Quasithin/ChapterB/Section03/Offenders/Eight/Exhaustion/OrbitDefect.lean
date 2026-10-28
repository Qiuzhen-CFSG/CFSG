module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Exhaustion.OrbitDefect.OrbitProfile
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Exhaustion.OrbitDefect.PairGeometry
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Exhaustion.OrbitDefect.KleinGeometry

/-!
# Degree-eight orbit defect

The orbit-profile theorem reduces an elementary abelian action without fixed
coordinates and with full fixed codimension at most rank plus one to two
possibilities: four pair orbits, and the independent orbit pattern 4+2+2.
The group orders and the independence assertion are part of the conclusion.
The pair normal form then gives conjugacy to `D` or to a hyperplane of `D`,
while labeling the 4+2+2 orbits gives conjugacy to the exceptional subgroup.
Together these prove membership in the source case-(b) family from the three
structural hypotheses, independently of the offender reduction supplying them.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, Proposition B.3.2(5), printed pp. 83–84.
-/

public section

namespace CFSG.Quasithin.ChapterB.Offenders.EightExhaustion

open Representation.BinaryOffender

/-- An elementary degree-eight action without fixed coordinates and with full
fixed codimension at most rank plus one belongs to the case-(b) family.
This is the structural orbit-classification step for B.3.2(5). -/
theorem caseBFamily_of_defect_le_one
    (A : Subgroup (Equiv.Perm (Fin 8))) (hA : IsElementaryTwo A)
    (hmove : ∀ x : Fin 8, ∃ a ∈ A, a x ≠ x)
    (hdef : fixedCodim (BinaryPermutation.representation (Fin 8)) A ≤ rank A + 1) :
    CaseBFamily 8 (by decide) A := by
  rcases orbit_profile_of_defect_le_one A hA hmove hdef with
    ⟨horb, hcard⟩ | ⟨horb, hcount, hcard, _⟩
  · exact caseBFamily_of_pair_orbits A hA horb hcard
  · exact Or.inr (Or.inl
      (isConjugateTo_exceptional_of_three_orbits A hA horb hcount hcard))

end CFSG.Quasithin.ChapterB.Offenders.EightExhaustion
