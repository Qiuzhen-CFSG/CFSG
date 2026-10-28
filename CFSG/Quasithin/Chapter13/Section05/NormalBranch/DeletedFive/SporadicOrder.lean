module

public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive.Cardinality
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import Theory.Mathieu.M11.Properties.Order
public import Theory.Mathieu.M24.Properties.Order
public import Theory.Mathieu.SmallModuleRanks.M12
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.SpecificGroups.Held.TwoPartDivisibility
public import Theory.SpecificGroups.Rudvalis.Model.Order

/-!
# The order and rank part of the sporadic inspection

The literal deleted-five block forces a factor 960, excluding M11 and J1.
The elementary module has order sixteen, exceeding the two-rank bound of
M12. The remaining five large sporadics have orders divisible by 512,
contrary to the source Sylow bound. Thus only M22, M23 and J2 need their
marked local-action arguments.

Source: Aschbacher--Smith, 13.5.15, printed p.921, inspecting Theorem C.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
open ChapterC ClassificationModels
variable {G : Type*} [Group G] [Finite G]

/-- The source markings reduce the sporadic list to its three local-action rows. -/
theorem sporadic_remaining_models (K : Subgroup G)
    (hK : IsAlternatingBlock K 5)
    (hE : IsElementaryAbelian 2 ((blockU K).map K.subtype))
    (hcard : Nat.card ((blockU K).map K.subtype) = 16)
    (T : Sylow 2 G) (hT : Nat.card T ≤ 256)
    (hmodel : ChapterA.Section02.IsTheoremCSporadicModel G) :
    Nonempty (G ≃* Sporadic.Mathieu.M22) ∨
      Nonempty (G ≃* Sporadic.Mathieu.M23) ∨
      Nonempty (G ≃* Sporadic.LeechRelated.J2.Carrier) := by
  have h960 := card_dvd_of_alternatingFive K hK hcard
  have h512 := not_fiveHundredTwelve_dvd_of_sylow_bound T hT
  rcases hmodel with ⟨name, hne, ⟨e⟩⟩ | ⟨e⟩
  · cases name with
    | m11 =>
      have hc : Nat.card G = 7920 :=
        (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m11_order
      rw [hc] at h960
      exact (by decide : ¬960 ∣ 7920) h960 |>.elim
    | m12 =>
      let E := (blockU K).map K.subtype
      let : IsElementaryAbelian 2 E := hE
      have helem : IsElementaryAbelian 2 (E.map e.toMonoidHom) :=
        IsElementaryAbelian.map _
      have hb := (primeRank_le_iff_elementary_card_le Sporadic.Mathieu.M12).mp
        Sporadic.Mathieu.m12_twoRank_le_three (E.map e.toMonoidHom) helem
      have hmap : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
        card_map_of_injective e.injective
      have hb' : Nat.card E ≤ 2 ^ 3 := by
        rw [← hmap]
        exact hb
      rw [hcard] at hb'
      norm_num at hb'
    | m22 => exact Or.inl ⟨e⟩
    | m23 => exact Or.inr (Or.inl ⟨e⟩)
    | m24 =>
      apply False.elim (h512 _)
      rw [Nat.card_congr e.toEquiv]
      change 512 ∣ Nat.card Sporadic.Mathieu.M24
      rw [Sporadic.Mathieu.m24_order]
      decide
    | j2 => exact Or.inr (Or.inr ⟨e⟩)
    | j3 => exact (hne rfl).elim
    | j4 =>
      apply False.elim (h512 _)
      rw [Nat.card_congr e.toEquiv]
      change 512 ∣ Nat.card Janko4.Model
      rw [Janko4.Cardinality.model_card]
      decide
    | hs =>
      apply False.elim (h512 _)
      rw [Nat.card_congr e.toEquiv]
      change 512 ∣ Nat.card Sporadic.LeechRelated.HS.Carrier
      rw [Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier]
      decide
    | he =>
      apply False.elim (h512 _)
      rw [Nat.card_congr e.toEquiv]
      exact (by decide : 512 ∣ 2 ^ 10).trans Held.two_pow_ten_dvd_card
    | ru =>
      apply False.elim (h512 _)
      rw [Nat.card_congr e.toEquiv]
      change 512 ∣ Nat.card Rudvalis.Model
      rw [Rudvalis.model_card]
      decide
  · obtain ⟨e⟩ := e
    have hc : Nat.card G = 175560 :=
      (Nat.card_congr e.toEquiv).trans Janko1.card_model
    rw [hc] at h960
    exact (by decide : ¬960 ∣ 175560) h960 |>.elim

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
