module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow

/-!
# Cardinal constraints on the deleted-five block in the normal branch

An alternating-five block with commutator module of order sixteen forces
960 to divide the ambient order. The Sylow bound in the normal branch of
13.5.15 forbids 512 from dividing that order. These two constraints are
shared by the actual Theorem C model inspections.

Source: Aschbacher--Smith, 13.5.15, printed p.921.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The quotient supplied by the actual alternating-five module model has order sixty. -/
theorem alternatingFive_quotient_card (K : Subgroup G)
    (hK : ChapterC.IsAlternatingBlock K 5) : Nat.card (K ⧸ pCore 2 K) = 60 := by
  obtain ⟨e⟩ := hK.2.2.quotient_iso
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num

omit [Finite G] in
/-- The literal deleted-five block forces the factor 960 in the ambient order. -/
theorem card_dvd_of_alternatingFive (K : Subgroup G)
    (hK : ChapterC.IsAlternatingBlock K 5)
    (hcard : Nat.card ((ChapterC.blockU K).map K.subtype) = 16) :
    960 ∣ Nat.card G := by
  have hU : Nat.card (ChapterC.blockU K) = 16 := by
    rwa [card_map_of_injective K.subtype_injective] at hcard
  have hcore : 16 ∣ Nat.card (pCore 2 K) := by
    rw [← hU]
    exact card_dvd_of_le ChapterC.blockU_le_core
  apply dvd_trans _ K.card_subgroup_dvd_card
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 K), alternatingFive_quotient_card K hK]
  exact Nat.mul_dvd_mul_left 60 hcore

/-- The source Sylow bound excludes a ninth binary factor in the ambient order. -/
theorem not_fiveHundredTwelve_dvd_of_sylow_bound (T : Sylow 2 G)
    (hT : Nat.card T ≤ 256) : ¬512 ∣ Nat.card G := by
  intro hd
  have hp : 2 ^ 9 ∣ Nat.card T := T.pow_dvd_card_of_pow_dvd_card hd
  have hb := Nat.le_of_dvd (Nat.card_pos (α := T)) hp
  norm_num at hb
  omega

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
