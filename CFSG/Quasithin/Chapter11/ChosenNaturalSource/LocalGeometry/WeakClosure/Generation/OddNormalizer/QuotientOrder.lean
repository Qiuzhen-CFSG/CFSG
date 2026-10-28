module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.NaturalAction
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourcePlacement

/-!
# Full covering orders in ordinary pushing-up components

The central kernel of an ordinary component is a two-group. Consequently
projection to its central quotient preserves the original covering residual
modulo its two-core, including the cubic center of SL₃. Lagrange's theorem
therefore retains the full natural quotient order. That order never divides
|SL₅(2)|: the small fields fail divisibility, and larger fields exceed its order.
OrdinaryModels applies these bounds to the actual C.2.8 component.

Source: Aschbacher--Smith C.3.2--5, pp.149--150, and 4.4.6, p.620.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
theorem linear_three_order {F : Type*} [Field F] [Finite F] :
    Nat.card SL(3,F) = Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  let q := Nat.card F
  have hq : 1 < q := Finite.one_lt_card
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  have hs : Nat.card SL(3,F) = Nat.card PSL(3,F) * Nat.gcd 3 (q - 1) := by
    simpa only [Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin] using
      card_eq_card_quotient_mul_card_subgroup (center SL(3,F))
  rw [← hs] at hc
  simp only [Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero,
    Nat.reduceAdd, pow_one, Fin.prod_univ_zero, mul_one] at hc
  have h1 : q ^ 3 - q = q * (q ^ 2 - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
    ring
  have h2 : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one, ← pow_succ]
  have he : Nat.card SL(3,F) * (q - 1) =
      (q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1)) * (q - 1) := by
    calc
      _ = (q ^ 3 - 1) * ((q ^ 3 - q) * (q ^ 3 - q ^ 2)) := hc
      _ = _ := by rw [h1,h2]; ring
  exact Nat.eq_of_mul_eq_mul_right (show 0 < q - 1 by omega) he

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

theorem quotient_order_not_dvd_binary_five :
    ¬ Nat.card (L ⧸ pCore 2 L) ∣ 9999360 := by
  intro hd
  have hb : Nat.card (L ⧸ pCore 2 L) ≤ 9999360 := Nat.le_of_dvd (by decide) hd
  have hq : 4 ≤ Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) S.nonbinary
  have hf : Nat.card S.field.Carrier = 4 ∨ 8 ≤ Nat.card S.field.Carrier := by
    by_cases h : S.field.degree = 2
    · left; rw [S.field.card_eq,h]; decide
    · right; rw [S.field.card_eq]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) (by have := S.nonbinary; omega : 3 ≤ S.field.degree)
  cases S.natural with
  | sl3 hm =>
    rw [Nat.card_congr hm.some.groupEquiv.toEquiv,linear_three_order] at hd hb
    rcases hf with hf | hf
    · norm_num [hf] at hd
    · have hle := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.pow_le_pow_left hf 3)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hf 3) 1))
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hf 2) 1)
      norm_num at hle
      omega
  | sp4 hm =>
    rw [Nat.card_congr hm.some.groupEquiv.toEquiv,
      Theory.SpecificGroups.SymplecticFour.card_sp] at hd hb
    rcases hf with hf | hf
    · norm_num [hf] at hd
    · have hle := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.pow_le_pow_left hf 4)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hf 2) 1))
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hf 4) 1)
      norm_num at hle
      omega
  | g2 hm =>
    rw [Nat.card_congr hm.some.groupEquiv.toEquiv,Atlas.G2.card_Model] at hb
    have hle := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left hq 6)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 6) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    norm_num at hle
    omega

omit D S in
theorem ordinary_natural_quotient_card_dvd {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : IsComponent H K) :
    Nat.card (L ⧸ pCore 2 L) ∣ Nat.card (K ⧸ center K) := by
  let BH := B.subgroupOf H
  let BK := BH.subgroupOf K
  have hBH : B ≤ H := h.component_le.trans h.local_le
  have hBK : BH ≤ K := h.ordinary_component_contains_original K hK
  let eb : BK ≃* B := (subgroupOfEquivOfLe hBK).trans (subgroupOfEquivOfLe hBH)
  let f := (QuotientGroup.mk' (center K)).comp BK.subtype
  let := hK.2
  have hz : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot h.oddCore_eq_bot K)
  have hk : IsPGroup 2 f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    change IsPGroup 2 ((QuotientGroup.mk' (center K)).comp BK.subtype).ker
    rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk',hz]
    exact pCore_isPGroup.comap_of_injective BK.subtype BK.subtype_injective
  let ec := f.rangeRestrict.quotientPCoreEquivOfSurjective f.rangeRestrict_surjective hk
  let eq : (L ⧸ pCore 2 L) ≃* (f.range ⧸ pCore 2 f.range) :=
    e.symm.trans ((QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)).symm.trans ec)
  rw [Nat.card_congr eq.toEquiv]
  exact (Subgroup.card_quotient_dvd_card (pCore 2 f.range)).trans
    f.range.card_subgroup_dvd_card
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
