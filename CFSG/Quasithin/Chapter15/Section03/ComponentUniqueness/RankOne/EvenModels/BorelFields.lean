module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.SmallLinear
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BorelContracts
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane.UnitaryField

/-!
# Field restrictions from the actual normal four-group

Once the local intersection is the Borel, its invariance of the original
four-group supplies the hypotheses of the concrete PSL₂ and PSU₃ root
calculations. Both force fixed-field degree two. In the unitary case the
four-group is also identified with the centre of the component Sylow.
The linear-two case is then excluded by the already proved PSL₂(4) case.

The Borel equality is an explicit, undischarged output of the separate
parabolic inspection; these are conditional deductions, not a proof of
the full larger-field paragraph of 15.3.43.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
proof of 15.3.43, printed p.1140.
-/

public section

open Subgroup
open CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)
include c

omit [Finite G] in
theorem borel_normalizes_plane (hB : M ⊓ L = borel L S) :
    borel L S ≤ normalizer (V₂ : Set G) := by
  rw [← hB]
  exact (le_inf inf_le_left (inf_le_right.trans c.component_le)).trans c.plane_two_normalized

/-- Full Borel invariance forces the linear field to have four elements. -/
theorem linear_borel_degree_eq_two {n : ℕ}
    (hm : ClassicalGroup.IsPSL L 2 (2 ^ n)) (hB : M ⊓ L = borel L S) : n = 2 := by
  obtain ⟨P, hP⟩ := component_sylow c
  exact RankTwo.RankOnePlane.linear_plane_degree_eq_two hm P hP c.plane_two_le
    (plane_le_component c) c.plane_two_card (borel_normalizes_plane c hB)

/-- This conditional linear branch has no remaining field or small-model premise. -/
theorem not_linear_borel {n : ℕ}
    (hm : ClassicalGroup.IsPSL L 2 (2 ^ n)) (hB : M ⊓ L = borel L S) : False := by
  have hn := linear_borel_degree_eq_two c hm hB
  exact not_linear_two_four c (by simpa only [hn, show (2 : ℕ) ^ 2 = 4 from rfl] using hm)

/-- The unitary parameter is the fixed-field order, not the matrix-field order. -/
theorem unitary_borel_degree_eq_two {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSU L 3 (2 ^ n)) (hB : M ⊓ L = borel L S) :
    n = 2 ∧ V₂ = (center (S ⊓ L : Subgroup G)).map (S ⊓ L).subtype := by
  obtain ⟨P, hP⟩ := component_sylow c
  exact RankTwo.RankOnePlane.unitary_plane_degree_eq_two hn hm P hP c.plane_two_le
    (plane_le_component c) (plane_isKleinFour c) (borel_normalizes_plane c hB)

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels
