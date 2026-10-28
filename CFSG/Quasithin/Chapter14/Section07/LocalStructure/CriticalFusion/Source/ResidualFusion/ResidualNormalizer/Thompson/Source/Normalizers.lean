module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Components.Decomposition.SourceSolvability
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable.Normalizers
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# The original residual normalizer from earlier source theorems

The component argument constructs solvability of J(DR₁); the original
solvable Thompson argument then proves N_G(K)=H. Maximality follows from
1.2.7 on the same K. Full known-simple Theorems A and C instantiate that
uniqueness input in the final export. The only remaining earlier inputs are
the original structural and faithful classifications, the A₅ module clause,
and the separately owned 14.7.10 and 14.7.31 source implications.

Source: Aschbacher–Smith14.7.67(3–4), printed pp.1070–1071.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 ResidualNormalizer Rechoice.Goldschmidt
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- Literal source14.7.67(4), with the nonsolvable branch discharged. -/
theorem Data.normalizer_K_eq_H_of_source
    (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (baumann : LocalControl.Earlier14710.{u}) (weakClosure : Theorem14731.{u}) :
    normalizer (K F : Set G) = F.H ∧ IsMaximalTwoLocal F.H := by
  have hsol := d.residual_thompson_solvable_of_source structural uniqueness faithful modules
  have he := d.normalizer_K_eq_H_of_solvable_source structural uniqueness modules
    baumann weakClosure hsol
  exact ⟨he, he ▸ (d.residual_normalizer_unique faithful uniqueness).1⟩

/-- The full catalogue discharges the universal uniqueness theorem internally. -/
theorem Data.normalizer_K_eq_H_of_known_simple_source
    (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (baumann : LocalControl.Earlier14710.{u}) (weakClosure : Theorem14731.{u}) :
    normalizer (K F : Set G) = F.H ∧ IsMaximalTwoLocal F.H := by
  apply d.normalizer_K_eq_H_of_source structural ?_ faithful modules baumann weakClosure
  intro X _ _ hX S K hK
  exact Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
    (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y)) hX S hK

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
