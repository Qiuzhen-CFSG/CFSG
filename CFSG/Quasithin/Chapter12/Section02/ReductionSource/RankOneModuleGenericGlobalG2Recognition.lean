module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Recognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2Thompson

/-!
# The prepared Chapter 12 G₂ branch

The original normalizer indices are at most the original field degree n.
The Thompson order bound then forces a twelve-cycle in the actual coset
graph. The checked fixed-torus and completion comparison recognize ambient
G as the concrete G₂ model. This supplies GlobalExit at n>1, including n=2,
without a diameter, Weyl relation, or recognition premise.

Both parabolic maps and their whole overlap are retained. The actual compatible
G₂ comparison and the earlier preparation, including original uniqueness,
remain inputs. Exhaustive comparison and the other model rows remain with the
generic-global assembly; this result completes its prepared G₂ recognition row.
Source: Aschbacher–Smith F.4.24–44, pp.287–296, and 5.3.2–4, p.659,
applied in Chapter 12 on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The actual prepared G₂ comparison gives the strict rank-two global output,
with geometric smallness and completion recognition discharged. -/
theorem rankOne_globalExit_of_g2_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    RankOneModule.GlobalExit G := by
  obtain ⟨hF,hiso⟩ := d.g2_ambient_recognition
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F he
  exact Or.inl ⟨n,hn,ClassificationModels.IsRankTwoModel.g2 hn
    ⟨F,inferInstance,inferInstance,hF,hiso⟩⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
