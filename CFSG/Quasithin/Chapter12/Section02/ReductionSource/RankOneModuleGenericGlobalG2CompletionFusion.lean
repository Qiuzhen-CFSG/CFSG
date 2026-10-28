module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2CompletionFusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2CenterKernel

/-!
# Fusion in the actual G₂ factor join for the Chapter 12 setup

The compatible source maps transport the involution reduction into
J = L ∨ O²(H). The already proved marked nonfusion separates the two
classes in ambient G, so every ambient fusion between involutions of the
original S is realized by an element of this literal J. This supplies the
fusion comparison used in the centralizer and Thompson-order steps of the
source recognition argument. It neither identifies J with the G₂ model
nor establishes J = G. Exhaustive compatible comparison, original uniqueness
and the remaining completion/ambient recognition obligations stay explicit.

Source: Aschbacher–Smith F.4.30, F.4.35 and F.4.43, pp.290,292,296,
and 5.3.3, p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original two local factors already realize all ambient involution
fusion within S, at every original field exponent n > 1. -/
theorem rankOne_global_g2_completion_controls_involution_fusion
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
        (G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F)).reverse))
    (x y : G) (hx : x∈Global.sourceS L H) (hy : y∈Global.sourceS L H)
    (hx2 : orderOf x=2) (hy2 : orderOf y=2) :
    IsConj x y ↔ ∃ g∈L⊔residual H, g*x*g⁻¹=y :=
  d.g2_completion_controls_involution_fusion
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F he x y hx hy hx2 hy2

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
