module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.ProfileRegularity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.TensorChapter12Application

/-!
# U₄ recognition with the source regularity premises discharged

DGS (11.5) and (11.7) give elementary original Sylow quotients at both
endpoints of the quadratic profile. Injecting the actual simple roots in
these quotients, before regularity is assumed, excludes the defective
affine panel and proves both remainder-kernel containments. The existing
complete tensor and equation construction then gives the marked U₄
comparison and the literal Chapter 12 catalogue entry. No field size or
perfectness restriction is introduced; both orientations and all positive
fixed-field degrees, including the binary case, remain.

The actual profile, actor maps, quotient/split and rotation order four
still belong to their earlier DGS producers. This closes their selected
U₄ recognition consumer, not exhaustive source-profile selection.
Source: DGS (11.5)--(11.7), pp.173--175 and Theorem D, p.224;
Fong--Seitz I (6A)(b), II (8B), pp.201--202; AS 12.2.2.
-/

@[expose] public noncomputable section
open Subgroup Representation Matrix Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
open Theory.PSL2.SemilinearCoverage
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open Representation.OrthogonalFourMinus Representation.OrthogonalFourMinus.FiniteModel
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
section Marked
variable {G X F k : Type*} [Group G] [Group X]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (fi : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,F))
  (fj : (S ⊔ L j).subgroupOf (parabolic L S j) →* SL(2,k))
  (hfi : Function.Surjective fi) (hfj : Function.Surjective fj)
  (hki : fi.ker = (pCore 2 (parabolic L S i)).subgroupOf ((S ⊔ L i).subgroupOf (parabolic L S i)))
  (hkj : fj.ker = (pCore 2 (parabolic L S j)).subgroupOf ((S ⊔ L j).subgroupOf (parabolic L S j)))
  (hfields : Nat.card F = Nat.card k ^ 2)
  (hindexi : (commonBorel L S).relIndex (parabolic L S i) = Nat.card F + 1)
  (hindexj : (commonBorel L S).relIndex (parabolic L S j) = Nat.card k + 1)
  (helem : IsElementaryAbelian 2 ((parabolic L S i).pCoreIn 2))
  (hQi : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := S) i
    IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
  (hQj : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := S) j
    IsElementaryAbelian 2 (S ⧸ ((parabolic L S j).pCoreIn 2).subgroupOf S))
  (hne : ⁅(parabolic L S j).pCoreIn 2,(parabolic L S j).pCoreIn 2⁆ ≠ ⊥)
  (n : ℕ) [NeZero n] (hk : Nat.card k = 2^n)
open BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open UnitaryPresentation

include mark h split fi hfi hki fj hfj hkj hfields hindexi hindexj helem hQi hQj hne hk hm hij in
/-- The original quadratic profile supplies the full U₄ catalogue comparison;
both kernel containments are now proved from its Sylow quotients. -/
theorem marked_quadratic_profile_unitaryFour_catalogue :
    Chapter6.Source.RankOneGeneric.Global.ConcreteAmalgamComparison
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) := by
  have hVi := (QuadrangleStructure.regularity_of_sylow_core Q mark h split i hQi).1
  have hVj := (QuadrangleStructure.regularity_of_sylow_core Q mark h split j hQj).1
  exact marked_quadratic_unitaryFour_catalogue Q mark h split hm i j hij hVi hVj fi fj hfi hfj hki hkj
    hfields hindexi hindexj helem hQi hQj hne n hk

end Marked
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source.FongSeitzBinary
open ChapterF.Source.FongSeitzBinary.UnitarySource
open ChapterF.Source
variable {G X F k : Type*} [Group G] [Finite G] [Group X]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P)
  (mark : Iso (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
  (split : SplitData Q.tits)
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (fi : ((Global.sourceS L H) ⊔ (![L,R] : Fin 2 → Subgroup G) i).subgroupOf (parabolic (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H) i) →* SL(2,F))
  (fj : ((Global.sourceS L H) ⊔ (![L,R] : Fin 2 → Subgroup G) j).subgroupOf (parabolic (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H) j) →* SL(2,k))
  (hfi : Function.Surjective fi) (hfj : Function.Surjective fj)
  (hki : fi.ker = (pCore 2 (parabolic (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H) i)).subgroupOf (((Global.sourceS L H) ⊔ (![L,R] : Fin 2 → Subgroup G) i).subgroupOf (parabolic (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H) i)))
  (hkj : fj.ker = (pCore 2 (parabolic (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H) j)).subgroupOf (((Global.sourceS L H) ⊔ (![L,R] : Fin 2 → Subgroup G) j).subgroupOf (parabolic (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H) j)))
  (hfields : Nat.card F = Nat.card k ^ 2)
  (hindexi : (commonBorel (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H)).relIndex (parabolic (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H) i) = Nat.card F + 1)
  (hindexj : (commonBorel (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H)).relIndex (parabolic (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H) j) = Nat.card k + 1)
  (helem : IsElementaryAbelian 2 ((parabolic (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H) i).pCoreIn 2))
  (hQi : letI := QuadrangleStructure.original_core_normal_in_sylow (L := (![L,R] : Fin 2 → Subgroup G)) (S := (Global.sourceS L H)) i
    IsElementaryAbelian 2 ((Global.sourceS L H) ⧸ ((parabolic (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H) i).pCoreIn 2).subgroupOf (Global.sourceS L H)))
  (hQj : letI := QuadrangleStructure.original_core_normal_in_sylow (L := (![L,R] : Fin 2 → Subgroup G)) (S := (Global.sourceS L H)) j
    IsElementaryAbelian 2 ((Global.sourceS L H) ⧸ ((parabolic (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H) j).pCoreIn 2).subgroupOf (Global.sourceS L H)))
  (hne : ⁅(parabolic (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H) j).pCoreIn 2,(parabolic (![L,R] : Fin 2 → Subgroup G) (Global.sourceS L H) j).pCoreIn 2⁆ ≠ ⊥)
  (m : ℕ) [NeZero m] (hk : Nat.card k = 2^m)

include D h hmany hn hpsl hH d mark split hm hij fi fj hfi hfj hki hkj hfields hindexi hindexj helem hQi hQj hne hk in
/-- The actual Chapter12 source receives the constructed U₄ comparison,
with F.1.1 discharged from its original proper-K/KnownSimple preparation.
Both endpoint orientations and the smallest fixed fields are retained. -/
theorem rankOne_unitaryFour_quadratic_profile_comparison :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2
  exact marked_quadratic_profile_unitaryFour_catalogue Q mark hf split hm i j hij fi fj hfi hfj hki hkj
    hfields hindexi hindexj helem hQi hQj hne m hk

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
