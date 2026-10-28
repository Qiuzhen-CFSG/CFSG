module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Centralizers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalFieldFour

/-!
# Central-involution control for the original G₂ completion

The marked Chapter12 G₂ pair now supplies both the literal full-normalizer
conditions of 5.3.1 and the central-involution bounds needed in 5.3.3. The
right bound uses the actual parabolic torus action on the highest-root center,
a fixed involution of the original Sylow subgroup, and the already proved
right maximality, including field order four. No center-action, fixed-point,
or extra centralizer hypothesis is imposed.

The original Preparation retains the earlier uniqueness input. The compatible
G₂ comparison remains explicit, and this does not construct the exhaustive
F.1.12 comparison or recognize the ambient completion. Those obligations and
the final GlobalExit assembly remain with the generic-global owner.
Source: Aschbacher–Smith 5.3.1–3, pp.658–659, F.4.31, and the original
Chapter12 application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The G₂ normalizer pair and its two ambient central-involution bounds,
with the source factors and original Sylow markings retained. -/
theorem rankOne_global_g2_normalizer_centralizer_conditions
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
    Chapter5.Section03GreenExtension.SourceLocalConditions
      (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) ∧
    ∀ i : Fin 2, ∀ z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype,
      orderOf z = 2 → centralizer ({z} : Set G) ≤ normalizer (![L,residual H] i : Set G) := by
  exact ⟨D.rankOne_global_g2_normalizer_local_conditions_all h hmany hn hpsl hH d hp F he,
    d.g2_central_involution_centralizers
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F he⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
