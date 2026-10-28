module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.QuotientOrder
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.ConstrainedModels
/-!
# The source field in the remaining constrained SL₅(2) case

The actual perfect action is inner on the component's simple quotient and
surjects onto the original simple quotient. Hence its order divides the
component quotient order. For SL₅(2), natural-group order formulas force
the source field to have four elements and its full quotient to be SL₃(4).
Its center has order three and is retained throughout the conclusion.

ModelReduction applies the result to the actual C.2.8 configuration.
Exclusion of this last constrained row remains with the same task.
Source: Aschbacher--Smith C.4.5--8, pp.152--154, and 4.4.6, p.620.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
private theorem card_binary_five {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) : Nat.card PSL(5,F) = 9999360 := by
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
  norm_num [hF,Fin.prod_univ_succ] at hc
  exact hc

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

theorem constrained_natural_central_order_dvd {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hN : (B.subgroupOf M).Normal)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) :
    Nat.card (coreCentralQuotient L) ∣ Nat.card (coreCentralQuotient K) := by
  obtain ⟨g,hg⟩ := constrained_natural_action_quotient D S h hN e K hK hq hout
  let := hq
  let Q := coreCentralQuotient K
  let : IsSimpleGroup Q := hq.simple
  let X := conjugateSpanBy B M
  let A := X.subgroupOf H
  let C := coreCentralActorImage K A
  have hXH : X ≤ H := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  let := h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hXH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hXH).symm.surjective
  let : Group.IsPerfect C := coreCentralActorImage_perfect K A
    (h.constrained_span_normalizes_intrinsic K hK hq)
  let : Group.IsSolvable (MulAut.Outer Q) := h.constrained_core_central_outer_solvable K hq
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp hc)).elim
  obtain ⟨f,hf,_⟩ := MulAut.perfect_subgroup_exists_inner_lift C hz
  have hd : Nat.card (coreCentralQuotient L) ∣ Nat.card C := by
    rw [←Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hg).toEquiv]
    exact g.ker.card_quotient_dvd_card
  exact hd.trans (Subgroup.card_dvd_of_injective f hf)

/-- Only the full SL₃(4) source quotient has simple central quotient whose
order can divide the binary degree-five order. Its cubic center is retained. -/
theorem natural_binary_five_order_forces_field_four
    (hd : Nat.card (coreCentralQuotient L) ∣ 9999360) :
    S.field.degree = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) ∧
      Nat.card (center (L ⧸ pCore 2 L)) = 3 := by
  have hb : Nat.card (coreCentralQuotient L) ≤ 9999360 := Nat.le_of_dvd (by decide) hd
  have hz := Nat.le_of_dvd (by decide : 0 < 3) (quotient_center_card_dvd_three D S)
  have hc := card_eq_card_quotient_mul_card_subgroup (center (L ⧸ pCore 2 L))
  change Nat.card (L ⧸ pCore 2 L) = Nat.card (coreCentralQuotient L) * _ at hc
  have hq : 4 ≤ Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) S.nonbinary
  cases S.natural with
  | sl3 hm =>
    have hf : S.field.degree ≤ 3 := by
      by_contra! hf
      have hq' : 16 ≤ Nat.card S.field.Carrier := by
        rw [S.field.card_eq]
        exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 ≤ S.field.degree)
      have hl := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.pow_le_pow_left hq' 3)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq' 3) 1))
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq' 2) 1)
      have he : Nat.card (L ⧸ pCore 2 L) =
          Nat.card S.field.Carrier ^ 3 * (Nat.card S.field.Carrier ^ 3 - 1) *
            (Nat.card S.field.Carrier ^ 2 - 1) := by
        rw [Nat.card_congr hm.some.groupEquiv.toEquiv,linear_three_order]
      norm_num at hl
      nlinarith
    have hf2 : S.field.degree = 2 := by
      by_contra hne
      have hf3 : S.field.degree = 3 := by have := S.nonbinary; omega
      have hcF : Nat.card S.field.Carrier = 8 := by rw [S.field.card_eq,hf3]; decide
      have he : Nat.card (L ⧸ pCore 2 L) = 16482816 := by
        rw [Nat.card_congr hm.some.groupEquiv.toEquiv,linear_three_order,hcF]
        norm_num
      have hz1 : Nat.card (center (L ⧸ pCore 2 L)) = 1 := by
        rw [Nat.card_congr (centerCongr hm.some.groupEquiv).toEquiv,
          Atlas.ExceptionalSupport.card_sl_center]
        norm_num [hcF]
      rw [he,hz1,mul_one] at hc
      omega
    refine ⟨hf2,⟨hm.some.groupEquiv⟩,?_⟩
    rw [Nat.card_congr (centerCongr hm.some.groupEquiv).toEquiv,
      Atlas.ExceptionalSupport.card_sl_center]
    norm_num [S.field.card_eq,hf2]
  | sp4 hm =>
    have hz1 : Nat.card (center (L ⧸ pCore 2 L)) = 1 := by
      rw [Nat.card_congr (centerCongr hm.some.groupEquiv).toEquiv,
        Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot,card_bot]
    rw [hz1,mul_one] at hc
    exact (quotient_order_not_dvd_binary_five D S (hc.symm ▸ hd)).elim
  | g2 hm =>
    have hz1 : Nat.card (center (L ⧸ pCore 2 L)) = 1 := by
      rw [Nat.card_congr (centerCongr hm.some.groupEquiv).toEquiv,
        Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot (by omega),card_bot]
    rw [hz1,mul_one] at hc
    exact (quotient_order_not_dvd_binary_five D S (hc.symm ▸ hd)).elim

/-- The actual remaining constrained star has source field four and full
SL₃ source quotient; PSL₃(4) is not substituted for that quotient. -/
theorem constrained_natural_field_four {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hN : (B.subgroupOf M).Normal)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K) :
    S.field.degree = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) ∧
      Nat.card (center (L ⧸ pCore 2 L)) = 3 := by
  obtain ⟨es⟩ := constrained_natural_star_linear_five_two D S h hN e K hK hq hout hfK
  have hd := constrained_natural_central_order_dvd D S h hN e K hK hq hout
  rw [Nat.card_congr (h.constrained_star_central_equiv K hK hq hout hfK).toEquiv,
    Nat.card_congr (QuotientGroup.congr _ _ es (FixedElementary.map_center es)).toEquiv] at hd
  change Nat.card (coreCentralQuotient L) ∣ Nat.card PSL(5,ZMod 2) at hd
  rw [card_binary_five (by simp : Nat.card (ZMod 2) = 2)] at hd
  exact natural_binary_five_order_forces_field_four D S hd
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
