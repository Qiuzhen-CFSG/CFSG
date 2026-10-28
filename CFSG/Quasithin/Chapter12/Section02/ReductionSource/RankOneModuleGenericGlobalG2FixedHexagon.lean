module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2FixedHexagon
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2WeylLocalization

/-!
# The literal G₂ graph and the generic/global exit

The full marked torus has exactly two fixed neighbors at either endpoint,
including over F₄. Together with the established girth bound, diameter six
forces the actual canonical Weyl relation. The existing completion comparison
then gives an actual G₂ model at the original exponent n > 1.

This application retains both original parabolics and their whole overlap.
The displayed diameter bound remains to be proved from the original ambient
hypotheses. Exhaustive amalgam selection and original uniqueness also remain;
this conditional result does not complete the generic/global theorem.
Source: Aschbacher–Smith F.3.6, F.4.8 and F.4.24–26, printed pp.272,278,
287–288, and 5.3.3–4, p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- A diameter-six proof for the actual source graph gives the strict
rank-two output, without a supplied Weyl relation or recognition certificate. -/
theorem rankOne_globalExit_of_g2_diameter
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hdiam : let P : Bool → Subgroup G := fun i =>
        ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) (if i then 0 else 1)
      ∀ v w : RankTwo.Vertex P, (RankTwo.graph P).dist v w ≤ 6) :
    RankOneModule.GlobalExit G := by
  obtain ⟨hF,hiso⟩ := d.g2_ambient_recognition_of_diameter
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F e hdiam
  exact Or.inl ⟨n,hn,ClassificationModels.IsRankTwoModel.g2 hn
    ⟨F,inferInstance,inferInstance,hF,hiso⟩⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
