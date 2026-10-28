module

public import Theory.SpecificGroups.Monster.Construction.QuasithinObstruction.Kernel
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.MonsterLocalObstruction
public import Theory.Quasithin.InvolutionCentralizerQuotientRank

/-!
# The independent Monster rank filter for I.1.3

The literal local C subgroup of the fixed Griess carrier centralizes griessZ
and surjects onto the lattice Leech central quotient. Its kernel is now
proved to be a two-group. The checked coprime-kernel lifting theorem
therefore transfers the target's rank-three witness into this involution
centralizer, contradicting quasithinness and hence strong quasithinness.

The source applications inherit finiteness from a finite group equipped
with an actual isomorphism to the Griess carrier. In particular they apply
to the simple SQTK domain of I.1.3, without any assumption about Monster
order or simplicity, the earlier A.2.15(2) rank bound, or central covers.
The existing Monster section and its representative equation are retained.

Sources: Aschbacher--Smith, A.2.19 and I.1.3; Aschbacher, *Sporadic Groups*,
27.5--27.9 and 28.12--28.13.
-/

public section
namespace CFSG.Quasithin.ChapterI.SQTKMultipliers.RankFilters.Monster
universe u
open Sporadic.Monster Sporadic.Monster.Construction
open Sporadic.Monster.Construction.QuasithinObstruction
open ChapterA.MonsterLocalObstruction
open Atlas.Conway

/-- The checked kernel property on the existing literal section data. -/
theorem monsterQuotientData_kernel_isTwoGroup :
    IsPGroup 2 monsterQuotientData.quotientMap.ker :=
  localToLeechQuotient_kernel_isTwoGroup

/-- The rank-three lattice witness lifts inside the actual involution centralizer. -/
theorem monster_three_le_twoLocalPrimeRank [Finite GriessGroup] :
    3 ≤ twoLocalPrimeRank 3 GriessGroup := by
  exact leechCentralQuotient_three_le_primeRank.trans
    (Theory.Quasithin.primeRank_le_twoLocalPrimeRank_of_centralizer_two_quotient
      monsterQuotientData.involution_order monsterQuotientData.numerator
      monsterQuotientData.centralizes monsterQuotientData.quotientMap
      monsterQuotientData.surjective monsterQuotientData_kernel_isTwoGroup 3 (by decide))

/-- The Griess carrier is not quasithin whenever it is finite. -/
theorem monster_not_quasithin [Finite GriessGroup] : ¬ IsQuasithin GriessGroup := by
  intro h
  have hb := isQuasithin_iff_twoLocalPrimeRank.mp h 3 (by decide) (by decide)
  have hr := monster_three_le_twoLocalPrimeRank
  omega

/-- The same local obstruction excludes strong quasithinness. -/
theorem monster_not_stronglyQuasithin [Finite GriessGroup] :
    ¬ IsStronglyQuasithin GriessGroup :=
  fun h => monster_not_quasithin h.quasithin

/-- Transport the obstruction using only source-inherited finiteness. -/
theorem not_quasithin_of_equiv {S : Type*} [Group S] [Finite S]
    (e : S ≃* GriessGroup) : ¬ IsQuasithin S := by
  let : Finite GriessGroup := Finite.of_surjective e e.surjective
  exact fun h => monster_not_quasithin (Theory.GroupTheory.isQuasithin_of_equiv e h)

/-- The independent Monster exclusion for the simple source domain of I.1.3. -/
theorem not_stronglyQuasithin_of_equiv {S : Type*} [Group S] [Finite S]
    (e : S ≃* GriessGroup) : ¬ IsStronglyQuasithin S :=
  fun h => not_quasithin_of_equiv e h.quasithin

/-- The Monster branch is impossible for SQTK, including the full known-simple class. -/
theorem not_sqtk_of_equiv {S : Type u} [Group S] [Finite S]
    (K : GroupClass.{u}) (e : S ≃* GriessGroup) : ¬ IsSQTK K S :=
  fun h => not_stronglyQuasithin_of_equiv e h.stronglyQuasithin

end CFSG.Quasithin.ChapterI.SQTKMultipliers.RankFilters.Monster
