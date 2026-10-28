module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.FullReeExclusion
public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.FromContainment
public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.TransferData
public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.TransferConstruction
public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.QuotientCentralizers

/-!
# The full second centralizer in the original marked Tits branch

The two transfers construct the literal quotient L/⟨v⟩. Its involution
centralizers lie in the prescribed Sylow subgroup, forcing C_G(v) ≤ N_G(F).
The local normalizer calculation then supplies every field of the full
second-centralizer data, including the ambient two-core, quotient, Sylow
position, and fusion in the original join. The supplied F and v are retained.

`source_tits_second_centralizer` discharges both premises of the earlier
conditional interface. No ambient N₂ or solvability of C_G(v) is required.
Ambient recognition is assembled in `TitsCompletion`.

Source: Aschbacher--Smith 14.2.22, printed p.989, and F.4.31, pp.290–291;
Parrott (1972), Lemma 8, printed pp.682–683.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]


/-- The actual transfer and quotient-centralizer conclusions supply every
second-centralizer field for the original source witnesses. Both construction
premises must still be discharged before the source theorem is complete. -/
theorem source_tits_second_centralizer_of_transfers
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
    (n : Recognition.ParrottNormalizerFusionData d)
    (t : Recognition.ParrottSecondTransferData n)
    (hcent : ∀ x ∈ t.quotientSylow, orderOf x = 2 →
      centralizer ({x} : Set t.Quotient) ≤ t.quotientSylow) :
    Recognition.ParrottSecondCentralizerData n := by
  exact n.second_centralizer_data_of_containment_of_local_inputs hp hlocal
    (t.le_normalizer_of_quotient_centralizers hp hlocal hcent)

/-- The original marked source configuration determines the entire second
involution centralizer, with no transfer or quotient-centralizer callbacks. -/
theorem source_tits_second_centralizer
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
    (n : Recognition.ParrottNormalizerFusionData d)
    : Recognition.ParrottSecondCentralizerData n := by
  obtain ⟨t⟩ := n.exists_second_transfer_data_of_local_inputs hp hlocal
  exact n.second_centralizer_data_of_containment_of_local_inputs hp hlocal
    (t.le_normalizer_of_local_inputs hp hlocal)

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
