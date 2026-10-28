module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.SmallSylow
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import Theory.SpecificGroups.Janko4.Model.Cardinality

/-!
# The final two ordinary rows force the original full SL₃(4) quotient

The projected residual order retains the original module quotient as a
factor, including any fixed vectors lost under central projection. The
certified J₄ and Rudvalis orders then exclude all symplectic and G₂ choices,
and every linear field larger than four. Their only surviving actor is
full SL₃(4), whose center still has order three.

The original C.2.8 pair, relative normality, inclusion-compatible quotient
and original V are retained. Source applies this reduction to the literal
Hall kernel. The two local model exclusions remain with the current owner.
Source: Aschbacher--Smith C.3.5, p.150, and 4.4.6, p.620.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

private theorem product_order_field_four (n : ℕ)
    (hn : n = 145926144000 ∨ n = 86775571046077562880)
    (hd : Nat.card D.chosenCentralQuotient * Nat.card (L ⧸ pCore 2 L) ∣ n) :
    S.field.degree = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) ∧
      Nat.card (center (L ⧸ pCore 2 L)) = 3 := by
  have hnpos : 0 < n := by rcases hn with rfl | rfl <;> decide
  have hnb : n ≤ 86775571046077562880 := by rcases hn with rfl | rfl <;> decide
  have hb := (Nat.le_of_dvd hnpos hd).trans hnb
  have hlo := S.nonbinary
  cases S.natural with
  | sl3 hm =>
    rw [Nat.card_congr hm.some.linearEquiv.toEquiv, Nat.card_fun, Nat.card_fin,
      Nat.card_congr hm.some.groupEquiv.toEquiv,linear_three_order] at hd hb
    have hf : S.field.degree ≤ 6 := by
      by_contra! hf
      have hq : 128 ≤ Nat.card S.field.Carrier := by
        rw [S.field.card_eq]
        exact Nat.pow_le_pow_right (by decide : 0 < 2) hf
      have hl := Nat.mul_le_mul (Nat.pow_le_pow_left hq 3)
        (Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hq 3)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 3) 1))
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1))
      norm_num at hl
      omega
    have hf2 : S.field.degree = 2 := by
      rcases hn with rfl | rfl <;> interval_cases hh : S.field.degree <;>
        first | rfl | norm_num [S.field.card_eq,hh] at hd
    refine ⟨hf2,⟨hm.some.groupEquiv⟩,?_⟩
    rw [Nat.card_congr (centerCongr hm.some.groupEquiv).toEquiv,
      Atlas.ExceptionalSupport.card_sl_center]
    norm_num [S.field.card_eq,hf2]
  | sp4 hm =>
    rw [Nat.card_congr hm.some.linearEquiv.toEquiv, Nat.card_fun, Nat.card_sum, Nat.card_fin,
      Nat.card_congr hm.some.groupEquiv.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp] at hd hb
    norm_num only [Nat.reduceAdd] at hd hb
    have hf : S.field.degree ≤ 4 := by
      by_contra! hf
      have hq : 32 ≤ Nat.card S.field.Carrier := by
        rw [S.field.card_eq]
        exact Nat.pow_le_pow_right (by decide : 0 < 2) hf
      have hl := Nat.mul_le_mul (Nat.pow_le_pow_left hq 4)
        (Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hq 4)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1))
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 4) 1))
      norm_num at hl
      omega
    rcases hn with rfl | rfl <;> interval_cases hh : S.field.degree <;>
      norm_num [S.field.card_eq,hh] at hd
  | g2 hm =>
    rw [Nat.card_congr hm.some.linearEquiv.toEquiv,
      Module.natCard_eq_pow_finrank (K := S.field.Carrier),Atlas.G2.Natural.finrank_space,
      Nat.card_congr hm.some.groupEquiv.toEquiv,Atlas.G2.card_Model] at hd hb
    have hf : S.field.degree ≤ 3 := by
      by_contra! hf
      have hq : 16 ≤ Nat.card S.field.Carrier := by
        rw [S.field.card_eq]
        exact Nat.pow_le_pow_right (by decide : 0 < 2) hf
      have hl := Nat.mul_le_mul (Nat.pow_le_pow_left hq 6)
        (Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hq 6)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 6) 1))
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1))
      norm_num at hl
      omega
    rcases hn with rfl | rfl <;> interval_cases hh : S.field.degree <;>
      norm_num [S.field.card_eq,hh] at hd

/-- The product-order obstruction common to both actual component projections.
The conclusion retains the full cubic center of the original quotient. -/
theorem field_four_of_product_order_dvd (n : ℕ)
    (hn : n = 145926144000 ∨ n = 86775571046077562880)
    (hd : Nat.card D.chosenCentralQuotient * Nat.card (L ⧸ pCore 2 L) ∣ n) :
    S.field.degree = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) ∧
      Nat.card (center (L ⧸ pCore 2 L)) = 3 :=
  product_order_field_four D S n hn hd

/-- The surviving ordinary row has the original full cubic cover at field four. -/
theorem ordinary_last_models {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hBL : B ≤ L) (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B.pCoreIn 2)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : IsComponent H K) :
    (Nonempty (K ⧸ center K ≃* Janko4.Model) ∨
      Nonempty (K ⧸ center K ≃* Rudvalis.Model)) ∧
    S.field.degree = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) ∧
      Nat.card (center (L ⧸ pCore 2 L)) = 3 := by
  obtain ⟨n,hn,⟨ek⟩⟩ := ordinary_remaining_models D S h e K hK
  have hd := ordinary_natural_product_card_dvd D S h hBL hc hVB K hK
  rw [Nat.card_congr ek.toEquiv] at hd
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact (no_ordinary_natural_small_sylow D S h hBL hc hVB K hK .m24 (by simp) ek).elim
  · exact (no_ordinary_natural_small_sylow D S h hBL hc hVB K hK .j2 (by simp) ek).elim
  · change Nat.card D.chosenCentralQuotient * Nat.card (L ⧸ pCore 2 L) ∣ Nat.card Janko4.Model at hd
    rw [Janko4.Cardinality.model_card] at hd
    exact ⟨Or.inl ⟨ek⟩,product_order_field_four D S _ (Or.inr rfl) hd⟩
  · exact (no_ordinary_natural_small_sylow D S h hBL hc hVB K hK .he (by simp) ek).elim
  · change Nat.card D.chosenCentralQuotient * Nat.card (L ⧸ pCore 2 L) ∣ Nat.card Rudvalis.Model at hd
    rw [Rudvalis.model_card] at hd
    exact ⟨Or.inr ⟨ek⟩,product_order_field_four D S _ (Or.inl rfl) hd⟩

open Chapter4 Chapter4.Section04
/-- The source configuration after the finite ordinary exclusions. -/
@[expose] def PushingUpFieldFourCase (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G,
    PushLE L (oddActorResidual L A) J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
    H ⊓ normalizer (L : Set G) < H ∧ V ≤ J.pCoreIn 2 ∧
    let B := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let M := H ⊓ normalizer (L : Set G)
    let R := J.pCoreIn 2
    ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W ∧
    (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G) ∧
    (B.subgroupOf M).Normal ∧ V ≤ B.pCoreIn 2 ∧
    (∃ e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L),
      ∀ b : B, e (QuotientGroup.mk' (pCore 2 B) b) =
        QuotientGroup.mk' (pCore 2 L)
          (inclusion ((map_subtype_le _).trans inf_le_left) b)) ∧
    ¬ ExceptionalQuotient (B ⧸ pCore 2 B) ∧ 64 ≤ Nat.card W ∧
    (∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
      V.map (MulAut.conj (c : G)).toMonoidHom ≤ W) ∧
    S.field.degree = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) ∧
    Nat.card (center (L ⧸ pCore 2 L)) = 3 ∧
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ M.subgroupOf H ∧ B.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      (Nonempty (K ⧸ center K ≃* Janko4.Model) ∨
        Nonempty (K ⧸ center K ≃* Rudvalis.Model))

/-- The actual covering residual retains its original module and only two model rows. -/
theorem pushingUp_field_four_case {A : Subgroup G} (hc : PushingUpRemainingCase L V A) :
    PushingUpFieldFourCase D S A := by
  obtain ⟨J,H,W,hpush,hH,hJH,hstrict,hVJ,hC,hcover,hN,⟨e,he⟩,hno,hsize,hVW,
    K,hK,hKn,hout,hBK,hWK,_⟩ := hc
  have hBL := (map_subtype_le (solvableResidual (L ⊓ H : Subgroup G))).trans inf_le_left
  have hVM : V ≤ H ⊓ normalizer (L : Set G) :=
    le_inf ((hVJ.trans (pCoreIn_le 2 J)).trans hJH) (D.le_component.trans L.le_normalizer)
  have hVB := covering_module_le_core D S hBL hC.component_le hVM hN hcover
  obtain ⟨hk,hf,hl,hz⟩ := ordinary_last_models D S hC hBL hcover hVB e K hK
  exact ⟨J,H,W,hpush,hH,hJH,hstrict,hVJ,hC,hcover,hN,hVB,⟨e,he⟩,hno,hsize,hVW,
    hf,hl,hz,K,hK,hKn,hout,hBK,hWK,hk⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
