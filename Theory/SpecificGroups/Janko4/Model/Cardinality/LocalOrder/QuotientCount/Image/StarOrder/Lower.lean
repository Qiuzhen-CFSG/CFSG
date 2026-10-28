module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder.Level6

/-!
# The certified lower bound for the star group

Successive point-fixing subgroups supply disjoint cosets with sizes
24, 23, 22, 21, 20, 16, and 3. Every representative is a certified word in
the star generators. Their product is 244823040.
-/

namespace Janko4.Cardinality.QuotientCount.Image.StarOrderCertificate
open Theory.GroupTheory

private theorem level0_step :
    24 * Nat.card (generated gen1) ≤ Nat.card (generated gen0) :=
  card_mul_le (generated gen0) (generated gen1) level1_le rep0 0
    (fun _ => word_mem _ _ (gen_mem _) _) rep0_inj level1_fix

private theorem level1_step :
    23 * Nat.card (generated gen2) ≤ Nat.card (generated gen1) :=
  card_mul_le (generated gen1) (generated gen2) level2_le rep1 1
    (fun _ => word_mem _ _ (gen_mem _) _) rep1_inj level2_fix

private theorem level2_step :
    22 * Nat.card (generated gen3) ≤ Nat.card (generated gen2) :=
  card_mul_le (generated gen2) (generated gen3) level3_le rep2 2
    (fun _ => word_mem _ _ (gen_mem _) _) rep2_inj level3_fix

private theorem level3_step :
    21 * Nat.card (generated gen4) ≤ Nat.card (generated gen3) :=
  card_mul_le (generated gen3) (generated gen4) level4_le rep3 3
    (fun _ => word_mem _ _ (gen_mem _) _) rep3_inj level4_fix

private theorem level4_step :
    20 * Nat.card (generated gen5) ≤ Nat.card (generated gen4) :=
  card_mul_le (generated gen4) (generated gen5) level5_le rep4 4
    (fun _ => word_mem _ _ (gen_mem _) _) rep4_inj level5_fix

private theorem level5_step :
    16 * Nat.card (generated gen6) ≤ Nat.card (generated gen5) :=
  card_mul_le (generated gen5) (generated gen6) level6_le rep5 5
    (fun _ => word_mem _ _ (gen_mem _) _) rep5_inj level6_fix

public theorem starGroup_card_ge : 244823040 ≤ Nat.card StarGroup := by
  have h0 := level0_step
  have h1 := level1_step
  have h2 := level2_step
  have h3 := level3_step
  have h4 := level4_step
  have h5 := level5_step
  have h6 := level6_bound
  have hle : Nat.card (generated gen0) ≤ Nat.card StarGroup :=
    Nat.card_le_card_of_injective (Subgroup.inclusion level0_le)
      (Subgroup.inclusion_injective level0_le)
  omega

end Janko4.Cardinality.QuotientCount.Image.StarOrderCertificate
