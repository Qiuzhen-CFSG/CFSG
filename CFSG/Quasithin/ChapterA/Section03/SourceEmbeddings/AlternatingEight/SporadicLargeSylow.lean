module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.SporadicLocal
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.EvenFaithfulSylow
public import CFSG.Quasithin.MainConverse.SporadicLocal.HS
public import CFSG.Quasithin.MainConverse.SporadicLocal.He
public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru

/-!
# Excluding HS, Held and Rudvalis from the original local A₈ row

If O₂(B) is nontrivial, the two-local order obstruction applies. Otherwise B
is A₈, and even characteristic makes the original Sylow act faithfully on it.
Aut(A₈) is S₈, so this Sylow has order at most 128. The concrete HS, He and Ru
carriers each contain a two-subgroup of order divisible by 256, a contradiction.

Source: Aschbacher–Smith A.3.12 and 15.3.32(3), printed pp.47–48 and1133.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
variable {G : Type*} [Group G] [Finite G]

private theorem higmanSims_twoPower : 256 ∣ Nat.card Sporadic.LeechRelated.HS.Carrier := by
  apply dvd_trans (b := Nat.card Sporadic.LeechRelated.HS.EvenLocalCandidates.subgroup)
  · rw [Sporadic.LeechRelated.HS.EvenLocalCandidates.subgroup_card]
    decide
  · exact card_subgroup_dvd_card _

private theorem held_twoPower : 256 ∣ Nat.card Held.He := by
  open Held.LocalPairs.SylowGeometry.Calculations in
  have hp := representative_isPGroup
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hl := Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.representative_card_ge_of_orbit_labels
    Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.orbitSizeLabel_eq_card_orbit
  have hn8 : 8 ≤ n := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    exact (by decide : 2 ^ 8 ≤ 1024).trans (hn ▸ hl)
  have hd : 256 ∣ Nat.card Held.LocalPairs.SylowGeometry.Calculations.representative := by
    rw [hn]
    exact pow_dvd_pow 2 hn8
  exact hd.trans (card_subgroup_dvd_card _)

private theorem rudvalis_twoPower : 256 ∣ Nat.card Rudvalis.Model := by
  rw [Rudvalis.model_card]
  decide

/-- The full original local A₈ configuration excludes HS, including a trivial two-core. -/
theorem not_higmanSims (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (e : G ≃* Sporadic.LeechRelated.HS.Carrier) : False := by
  by_cases hc : pCore 2 B = ⊥
  · have hE := MainConverse.evenCharacteristic_of_model_equiv e
      MainConverse.SporadicLocal.hs_evenCharacteristic
    apply not_twoPower_dvd_of_core_eq_bot S (hE S) hB hn h hc
    rw [Nat.card_congr e.toEquiv]
    exact higmanSims_twoPower
  · exact not_higmanSims_of_core_ne_bot S B hn h hc e

/-- The full original local A₈ configuration excludes Held. -/
theorem not_held (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (e : G ≃* Held.He) : False := by
  by_cases hc : pCore 2 B = ⊥
  · have hE := MainConverse.SporadicLocal.he_evenCharacteristic_of_equiv e
    apply not_twoPower_dvd_of_core_eq_bot S (hE S) hB hn h hc
    rw [Nat.card_congr e.toEquiv]
    exact held_twoPower
  · exact not_held_of_core_ne_bot S B hn h hc e

/-- The full original local A₈ configuration excludes Rudvalis. -/
theorem not_rudvalis (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (e : G ≃* Rudvalis.Model) : False := by
  by_cases hc : pCore 2 B = ⊥
  · have hE := MainConverse.evenCharacteristic_of_model_equiv e
      MainConverse.SporadicLocal.ru_evenCharacteristic
    apply not_twoPower_dvd_of_core_eq_bot S (hE S) hB hn h hc
    rw [Nat.card_congr e.toEquiv]
    exact rudvalis_twoPower
  · exact not_rudvalis_of_core_ne_bot S B hn h hc e

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
