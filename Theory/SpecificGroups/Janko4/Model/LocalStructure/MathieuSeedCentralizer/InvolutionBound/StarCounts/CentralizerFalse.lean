module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCounts.F2

/-!
# Lower bound for the false star centralizer

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

theorem centralizer_false_card_ge : 7680 ≤ Nat.card (Subgroup.centralizer ({starBase false} : Set StarGroup)) := by
  have h0 := card_mul_le (generated fGen0) (generated fGen1) fLevel1_le fRep0 0
    (fun _ => word_mem _ _ (gen_mem _) _) fRep0_inj
    fLevel1_fix
  have h1 := card_mul_le (generated fGen1) (generated fGen2) fLevel2_le fRep1 1
    (fun _ => word_mem _ _ (gen_mem _) _) fRep1_inj
    fLevel2_fix
  have h2 := card_mul_le (generated fGen2) ⊥ bot_le fRep2 4
    (fun _ => word_mem _ _ (gen_mem _) _) fRep2_inj
    (fun k => by have hk := k.property; simp only [Subgroup.mem_bot] at hk; simp [hk])
  have hle := card_generated_le_centralizer false fGen0 fLevel0_le fLevel0_centralizes
  simp only [Subgroup.card_bot, mul_one] at h2
  omega

end Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCountsCertificate
