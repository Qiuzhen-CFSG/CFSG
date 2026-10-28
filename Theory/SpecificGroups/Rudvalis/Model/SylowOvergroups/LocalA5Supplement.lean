module
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.LocalA5Placement
public import Theory.SpecificGroups.Rudvalis.Model.SylowInvariantPair.Definitions

/-!
# The full Sylow supplement of a local A₅ section in Rudvalis

A nontrivial local two-core puts the Sylow supplement inside a two-local.
The native normalizer catalogue places that two-local in max4 or max6.
The factor five excludes max4. In max6 the full Sylow order and the odd
factor fifteen already exhaust the order, so the whole supplement is max6.
This uses no prescribed order for the original component or its two-core.

Source: Aschbacher–Smith A.3.14(12) and 10.2.9, printed pp.48–49 and
750–751. Identification of the component inside this supplement is separate.
-/

public section
open Subgroup Theory.GroupTheory
namespace Rudvalis.SylowOvergroups
open RadicalCoverage.LocalCover

/-- The full Sylow supplement is the actual max6 carrier up to an ambient
conjugating automorphism; no core-order assumption is needed. -/
theorem local_fifteen_supplement_eq_max6 (P : Sylow 2 Model) (B : Subgroup Model)
    (hB : (B.subgroupOf (B ⊔ (P : Subgroup Model))).IsSubnormal)
    (hcore : pCore 2 B ≠ ⊥) (hodd : 15 ∣ Nat.card B) :
    ∃ e : Model ≃* Model, (B ⊔ (P : Subgroup Model)).map e.toMonoidHom = max6 := by
  let H := B ⊔ (P : Subgroup Model)
  have hQ : H.pCoreIn 2 ≠ ⊥ := by
    intro hzero
    have hle := map_mono (f := H.subtype) (pCoreIn_le_of_subnormal 2 hB)
    rw [pCoreIn_subgroupOf 2 B H le_sup_left,map_subgroupOf_eq_of_le
      ((B.pCoreIn_le 2).trans le_sup_left)] at hle
    change B.pCoreIn 2 ≤ H.pCoreIn 2 at hle
    rw [hzero] at hle
    apply hcore
    apply map_injective B.subtype_injective
    simpa only [pCoreIn, Subgroup.map_bot] using le_bot_iff.mp hle
  have hHN : H ≤ normalizer (H.pCoreIn 2 : Set Model) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hlocal : IsTwoLocal (normalizer (H.pCoreIn 2 : Set Model)) :=
    ⟨_,hQ,isPGroup_pCoreIn 2 H,rfl⟩
  rcases twoLocal_cover P _ hlocal (le_sup_right.trans hHN) with ⟨e,he⟩ | ⟨e,he⟩
  · have hd := card_dvd_of_le ((map_mono (le_sup_left.trans hHN)).trans he)
    rw [card_map_of_injective e.injective,max4_card] at hd
    have : 15 ∣ 344064 := hodd.trans hd
    norm_num at this
  · refine ⟨e,?_⟩
    have hle : H.map e.toMonoidHom ≤ max6 := (map_mono hHN).trans he
    apply eq_of_le_of_card_ge hle
    have hp : Nat.card P = 16384 := by
      rw [Nat.card_congr (P.equiv SylowInvariantPair.sylow).toEquiv]
      exact IntrinsicSylow.localP_card
    have hpH : 16384 ∣ Nat.card H := by
      simpa only [hp] using (card_dvd_of_le (show (P : Subgroup Model) ≤ H from le_sup_right))
    have hoH : 15 ∣ Nat.card H := hodd.trans (card_dvd_of_le (show B ≤ H from le_sup_left))
    have hlarge : 245760 ∣ Nat.card H :=
      (show Nat.Coprime 16384 15 by decide).mul_dvd_of_dvd_of_dvd hpH hoH
    rw [card_map_of_injective e.injective,max6_card]
    exact Nat.le_of_dvd (Nat.card_pos) hlarge

/-- An A₅ quotient supplies the odd factor needed in the supplement theorem. -/
theorem local_a5_supplement_eq_max6 (P : Sylow 2 Model) (B : Subgroup Model)
    (hB : (B.subgroupOf (B ⊔ (P : Subgroup Model))).IsSubnormal)
    (hcore : pCore 2 B ≠ ⊥)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    ∃ e : Model ≃* Model, (B ⊔ (P : Subgroup Model)).map e.toMonoidHom = max6 := by
  apply local_fifteen_supplement_eq_max6 P B hB hcore
  have hi : (pCore 2 B).index = 60 := by
    change Nat.card (B ⧸ pCore 2 B) = 60
    rw [Nat.card_congr eB.toEquiv,nat_card_alternatingGroup]
    norm_num
  rw [←(pCore 2 B).card_mul_index,hi]
  exact dvd_mul_of_dvd_right (by norm_num : 15 ∣ 60) _

/-- Normalization by the full Sylow retains normality of the original component
inside the identified supplement. -/
theorem normalized_a5_max6_placement (P : Sylow 2 Model) (B : Subgroup Model)
    (hPB : (P : Subgroup Model) ≤ normalizer (B : Set Model))
    (hcore : pCore 2 B ≠ ⊥)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    ∃ e : Model ≃* Model,
      (B ⊔ (P : Subgroup Model)).map e.toMonoidHom = max6 ∧
      ((B.map e.toMonoidHom).subgroupOf max6).Normal := by
  have hn : (B.subgroupOf (B ⊔ (P : Subgroup Model))).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hPB)
  obtain ⟨e,he⟩ := local_a5_supplement_eq_max6 P B hn.isSubnormal hcore eB
  refine ⟨e,he,?_⟩
  apply normal_subgroupOf_of_le_normalizer
  rw [←he]
  exact (map_mono (sup_le B.le_normalizer hPB)).trans (le_normalizer_map e.toMonoidHom)

end Rudvalis.SylowOvergroups
