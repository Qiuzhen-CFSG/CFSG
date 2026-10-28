module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCounts.T3

/-!
# Lower bound for the true star centralizer

These stabilizer transversals give only lower bounds. Every permutation,
word identity, fixed point and distinct image is checked by the Lean kernel.
GAP is used solely to discover the witnesses; its right-composition words
are reversed for Lean. See `source/generate.py` and `source/centralizers.g`.
The input generators are the certified ATLAS J4 max1 star action in `StarDefs`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

@[expose] public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCountsCertificate
open Janko4.Cardinality.QuotientCount.Image
open Janko4.Cardinality.QuotientCount.Image.StarOrderCertificate
open Janko4.Simplicity.Max1Fusion.QuotientInvolutions Theory.GroupTheory

theorem centralizer_true_card_ge : 21504 ≤ Nat.card (Subgroup.centralizer ({starBase true} : Set StarGroup)) := by
  have h0 := card_mul_le (generated tGen0) (generated tGen1) tLevel1_le tRep0 0
    (fun _ => word_mem _ _ (gen_mem _) _) tRep0_inj
    tLevel1_fix
  have h1 := card_mul_le (generated tGen1) (generated tGen2) tLevel2_le tRep1 2
    (fun _ => word_mem _ _ (gen_mem _) _) tRep1_inj
    tLevel2_fix
  have h2 := card_mul_le (generated tGen2) (generated tGen3) tLevel3_le tRep2 3
    (fun _ => word_mem _ _ (gen_mem _) _) tRep2_inj
    tLevel3_fix
  have h3 := card_mul_le (generated tGen3) ⊥ bot_le tRep3 4
    (fun _ => word_mem _ _ (gen_mem _) _) tRep3_inj
    (fun k => by have hk := k.property; simp only [Subgroup.mem_bot] at hk; simp [hk])
  have hle := card_generated_le_centralizer true tGen0 tLevel0_le tLevel0_centralizes
  simp only [Subgroup.card_bot, mul_one] at h3
  omega

end Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCountsCertificate
