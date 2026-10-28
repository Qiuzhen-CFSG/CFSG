module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.TitsSecondCentralizer
public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.TransferConstruction

/-!
# The actual transfers in the original marked Tits branch

The local transfer construction applies to the original source witnesses and
constructs both nested index-two subgroups, their literal Sylow image, and the
compatible excluded root. This discharges the transfer-data premise of
`source_tits_second_centralizer_of_transfers`. The quotient-centralizer argument
and final second-centralizer assembly remain with that theorem's owner.

Source: Aschbacher--Smith 14.2.22, printed p.989, and F.4.31, pp.290–291;
Parrott (1972), Lemma 8, printed pp.682–683.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The two transfers exist for exactly the witnesses of the original marked
Tits source branch; no new source hypothesis is needed. -/
theorem source_tits_second_transfer_data
    (_hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (_hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (_hM : IsOrderingMaximal T M)
    (_hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (_hcard : Nat.card (localModule T M) = 4)
    (_e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (_hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (_hmodel : ChapterF.GreenBook.IsAtlasTitsAmalgam
      (RankTwoAmalgam.ofSubgroups H (H ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)))
        (sourceResidual M Mc ⊔ (T : Subgroup G)) inf_le_left inf_le_right))

    (z : G) (_hz : zpowers z = centralInvolutions T)
    (hp : Recognition.ParrottCentralizerHypotheses z)
    (hlocal : Recognition.ParrottLocalInputs z)
    (d : Recognition.ParrottSecondElementaryData z)
    (n : Recognition.ParrottNormalizerFusionData d) :
    Nonempty (Recognition.ParrottSecondTransferData n) := by
  exact n.exists_second_transfer_data_of_local_inputs hp hlocal

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
