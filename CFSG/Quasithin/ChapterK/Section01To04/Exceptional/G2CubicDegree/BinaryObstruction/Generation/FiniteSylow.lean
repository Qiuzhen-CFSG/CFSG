module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Generation.ModelInput
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Generation.FiniteSylow.Generators
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Generation.FiniteSylow.Case0
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Generation.FiniteSylow.Case1
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Generation.FiniteSylow.Case2
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Generation.FiniteSylow.Case3
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Generation.FiniteSylow.Case4
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Generation.FiniteSylow.Case5
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Generation.FiniteSylow.Case6
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Generation.FiniteSylow.Case7

/-!
# An involution supplement for every elementary eight in binary G₂

The six root coordinates give exhaustive coverage by eight elementary
subgroups of the actual Sylow subgroup. For each one, checked octonion matrix
words recover C, E, F, R and S from three subgroup elements and a derived
conjugate of one of its elements.
The existing root generation theorem then gives the whole G₂(2), and hence
its commutator subgroup. The conjugator is explicitly in that commutator.

This discharges the finite Sylow premise consumed by the representation lift
in `Generation`. Source: Guralnick--Malle, Classification of 2F-modules I,
Proposition 4.3, manuscript pp.10--11, especially the outer-involution
supplement on p.11. The literal octonion conventions are those of the licensed
ATLAS port (LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff).
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction
open Atlas.G2

namespace FiniteSylow

theorem candidate_supplement_generates (i : Fin 8) :
    candidate i ⊔ Subgroup.zpowers (supplement i) = ⊤ := by
  apply eq_top_of_basic_letters
  fin_cases i
  · exact recover_case_0 _ (recoveryLetter_mem 0)
  · exact recover_case_1 _ (recoveryLetter_mem 1)
  · exact recover_case_2 _ (recoveryLetter_mem 2)
  · exact recover_case_3 _ (recoveryLetter_mem 3)
  · exact recover_case_4 _ (recoveryLetter_mem 4)
  · exact recover_case_5 _ (recoveryLetter_mem 5)
  · exact recover_case_6 _ (recoveryLetter_mem 6)
  · exact recover_case_7 _ (recoveryLetter_mem 7)

end FiniteSylow

/-- Every elementary eight in the actual positive-root Sylow subgroup has a
supplement obtained by conjugation inside the actual derived group. -/
theorem sylowRankThreeGeneration : SylowRankThreeGeneration := by
  intro E hEU hE hc
  obtain ⟨i,rfl⟩ := FiniteSylow.elementary_eight_coverage E hEU hE hc
  refine ⟨FiniteSylow.chosen i, FiniteSylow.chosen_mem i, FiniteSylow.conjugator i, ?_⟩
  change commutator (Model (ZMod 2)) ≤
    FiniteSylow.candidate i ⊔ Subgroup.zpowers (FiniteSylow.supplement i)
  rw [FiniteSylow.candidate_supplement_generates]
  exact le_top

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction
