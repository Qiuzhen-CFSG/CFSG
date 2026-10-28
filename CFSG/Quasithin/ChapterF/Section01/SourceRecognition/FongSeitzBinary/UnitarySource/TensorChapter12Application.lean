module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.TensorComparisonApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.Chapter12

/-!
# The original Chapter 12 consumer of U₄ source recognition

The ChosenModule preparation supplies genuine F.1.1 from the original
proper-K and full KnownSimple hypotheses. Applying the constructed U₄
source comparison at its quadratic profile gives the concrete amalgam
catalogue entry, including either orientation and the smallest fields.
The earlier profile, cover and row selection remain explicit source inputs;
no source equation, tensor realization or FourData is assumed.
Source: Aschbacher--Smith 12.2.1 and F.1.1; Fong--Seitz I (6A)(b),
pp.37--38, and II (8B), pp.201--202.
-/

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
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
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

include D h hmany hn hpsl hH d mark hm hij hVi hVj fi fj hfi hfj hki hkj hfields hindexi hindexj helem hQi hQj hne hk in
/-- The actual Chapter12 source receives the constructed U₄ comparison,
with F.1.1 discharged from its original proper-K/KnownSimple preparation.
Both endpoint orientations and the smallest fixed fields are retained. -/
theorem rankOne_unitaryFour_quadratic_source_comparison :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2
  exact marked_quadratic_unitaryFour_catalogue Q mark hf split hm i j hij hVi hVj fi fj hfi hfj hki hkj
    hfields hindexi hindexj helem hQi hQj hne m hk

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
