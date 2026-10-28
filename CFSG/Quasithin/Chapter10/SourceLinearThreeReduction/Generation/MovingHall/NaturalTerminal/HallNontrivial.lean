module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.Source

/-!
# Nontrivial original Hall images on the natural pair

The genuine E.2.2 Cartan data contain a cyclic group of order at least three.
Equality of Hall orders therefore makes the original odd Hall subgroup
nontrivial. Its image on any actual paired quotient by the orbit two-core
is nontrivial as well: an odd subgroup cannot lie in that two-core.

Source: Aschbacher--Smith E.2.2 and 10.2.3(4), printed pp.215,745--746.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {B : Subgroup H}

/-- The original Hall subgroup is nontrivial, without restricting the
component to A₅ or changing the chosen fundamental setup. -/
theorem Context.hall_ne_bot (ctx : Context D H B) : B ≠ ⊥ := by
  obtain ⟨hP,n,_,hgn,d,hm,_⟩ :=
    source_hstar_cartan_data_of_generation_gt_one D ctx.hstar ctx.large
  have hcard := d.hall.card_eq (hm.symm ▸ ctx.hall)
  rw [Nat.card_congr (subgroupOfEquivOfLe d.hall_le).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (hm.symm ▸ ctx.hall_le)).toEquiv] at hcard
  intro he
  have hcyc : Nat.card d.witness.cyclicGroup ≤ 1 := by
    calc
      Nat.card d.witness.cyclicGroup ≤ Nat.card d.witness.abelianGroup :=
        Nat.card_le_card_of_injective (inclusion d.witness.cyclic_le)
          (inclusion_injective d.witness.cyclic_le)
      _ = 1 := by rw [hcard,he,card_bot]
  have hpow : 4 ≤ 2^n := by
    have hn2 : 2 ≤ n := lt_of_lt_of_le ctx.large hgn
    exact pow_le_pow_right₀ (by decide : 1 ≤ (2:ℕ)) hn2
  rw [d.witness.card] at hcyc
  omega

/-- Nontriviality is retained by the literal ambient Hall image. -/
theorem Context.hall_image_ne_bot (ctx : Context D H B) : B.map H.subtype ≠ ⊥ := by
  intro he
  exact ctx.hall_ne_bot ((map_eq_bot_iff_of_injective _ H.subtype_injective).mp he)

/-- On an actual paired quotient by O₂(L₀), the original Hall has nontrivial
image in at least one factor. The quotient marking refers to the literal map. -/
theorem Context.hall_not_le_pair_kernel (ctx : Context D H B)
    {F : Type*} [Field F]
    (e : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (SL(2,F) × SL(2,F)))
    (q₁ q₂ : localOrbit T L →* SL(2,F))
    (he : ∀ x : localOrbit T L,
      e (QuotientGroup.mk' (pCore 2 (localOrbit T L)) x) = (q₁ x,q₂ x))
    (hBR : B.map H.subtype ≤ localOrbit T L) :
    ¬ (B.map H.subtype).subgroupOf (localOrbit T L) ≤ q₁.ker ⊓ q₂.ker := by
  let P := (B.map H.subtype).subgroupOf (localOrbit T L)
  intro hk
  have hPcore : P ≤ pCore 2 (localOrbit T L) := by
    intro x hx
    have hpair : (q₁ x,q₂ x) = 1 := Prod.ext (hk hx).1 (hk hx).2
    have hxq : QuotientGroup.mk' (pCore 2 (localOrbit T L)) x = 1 := by
      apply e.injective
      rw [he,hpair,map_one]
    exact (QuotientGroup.eq_one_iff x).mp hxq
  have hodd : Odd (Nat.card P) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBR).toEquiv]
    exact ctx.odd_card_of_le_hall_image _ le_rfl
  have hp : IsPGroup 2 P := pCore_isPGroup.to_le hPcore
  have hcard : Nat.card P = 1 := hp.card_eq_or_dvd.resolve_right hodd.not_two_dvd_nat
  have hPbot : P = ⊥ := by
    apply Subgroup.card_eq_one.mp hcard
  apply ctx.hall_image_ne_bot
  have hmap := congrArg (map (localOrbit T L).subtype) hPbot
  simpa only [P,map_subgroupOf_eq_of_le hBR,Subgroup.map_bot] using hmap

end CFSG.Quasithin.Chapter10.MovingHall
