module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeConstruction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The prime-actor amalgam on the original chosen module

The original chosen-module input supplies the left group DS, its index,
concrete quotient and self-normalizing Sylow. Thus genuine F.1.1 requires
only the right-factor geometry and the zero-core branch. Construction of
that right factor, and the subsequent source model exclusions, remain with
`qt-d-1222-rankone-cartan-local-to-global`; no normalization conclusion is
assumed or asserted here.

Source: Aschbacher--Smith, 5.2.2, printed p.647, and the original 12.2.2
application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B E L₂ : Subgroup G} (D : ChosenModule T L V)
include D

/-- Apply the constructed left side to the literal original prime-actor pair.
The remaining input is the right geometry, with no left-model callback. -/
theorem rankOne_prime_hypothesisF11_of_right
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (he : CartanPrimeActor A H p E)
    (d : Prime.RightData T L H B L₂)
    (hz : (Prime.generated L H E L₂).pCoreIn 2 = ⊥) :
    ChapterF.Source.HypothesisF11 ![E ⊔ Global.sourceS L H, L₂] (Global.sourceS L H) :=
  d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hH c he hz

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
