module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.SpanSplitting
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic
public import Theory.GroupTheory.SylowFixedNormalClosureSplitting

/-!
# Source B.2.14 splitting for the actual local span

Odd-index Sylow averaging proves the universal splitting clause for a
Sylow omega-center seed in a group of characteristic two. The resulting
source theorem applies to the same internal normal closure, component,
and Sylow map already checked in `span_split_of_source`.

Source: Aschbacher–Smith, Lemmas B.2.13–14, printed p.78, and the use in
15.3.32, printed p.1133. The extraspecial-elimination assembly also uses
this universal theorem for its original local normal closures.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry
universe u

/-- The splitting clause of B.2.14 follows from its original hypotheses. -/
theorem sourceB214Splitting : SourceB214Splitting.{u} := by
  intro H _ _ hchar P Z _ hZ
  exact Theory.GroupTheory.omegaCenter_subgroup_normalClosure_split P
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hchar) Z hZ

/-- The genuine local span splits over its component module and global fixers. -/
theorem span_split {G : Type u} [Group G] [Finite G]
    (d : LocalData G) {I : Subgroup G} (hchar : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (hI : I = c.L ⊔ d.S) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S) (hZ : Nat.card d.Z = 2) :
    d.UI I = d.componentModule I c.L ⊔ (d.UI I ⊓ centralizer (I : Set G)) :=
  span_split_of_source sourceB214Splitting d hchar c hnormal hI P hP hZ

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry
