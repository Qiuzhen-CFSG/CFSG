module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ThreeInner

/-!
# The linear odd-prime branch of E.1.14(7)

The source assumes finite SQTK G, simple L = F*(G), G = LT for a Sylow
two-subgroup T, and an actual PSL₃(p) model for an odd prime p. The theorem
below discharges the inner p=3 branch by the explicit solvable generating
parabolics. Larger prime fields and proper almost-simple extensions remain
separate obligations; no unconditional E.1.14(7) theorem is claimed here.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.14(7), printed p.214, and A.2.3(2), printed p.33.
-/

public section
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration

/-- Application to the source socle when p=3 and the ambient group equals its socle. -/
theorem isEGenerated_one_of_pslThreeThree_socle_eq_top {G : Type*} [Group G] [Finite G]
    (hmodel : ClassicalGroup.IsPSL (Theory.GroupTheory.generalizedFitting G) 3 3)
    (hL : Theory.GroupTheory.generalizedFitting G = ⊤) : IsEGenerated 1 G := by
  apply isEGenerated_one_of_isPSL_three_three
  exact hmodel.of_mulEquiv ((MulEquiv.subgroupCongr hL).trans Subgroup.topEquiv).symm

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration
