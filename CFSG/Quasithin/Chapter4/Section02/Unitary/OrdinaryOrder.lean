module
public import CFSG.Quasithin.Chapter4.Section02.Unitary.OrdinaryFinite
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.WordCoverage
/-!
# The module and unitary section both contribute to the component order

In the literal ordinary central quotient, let B be the image of the source
span and E the image of its elementary module. The quotient B/E is nontrivial:
otherwise full movement by the abelian E would kill E. The unitary section
therefore survives in B/E, so 64·6048 divides the component quotient order.
The certified Held Sylow of order at most 1024 contradicts its two-part 2048.
This removes the Held row without a new local catalogue or model-order premise.

Source: Aschbacher–Smith C.3.1(8), pp.149–151, in the original unitary
4.2.12–13 and 4.4.6 application. Final odd-normalizer assembly remains with
qt-d-13316-source.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}
local notation "D" => commutator (Atlas.G2.Model (ZMod 2))

/-- Both the actual module image and its unitary quotient contribute to the order. -/
theorem unitary_ordinary_module_order_dvd
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D) (K : Subgroup H) (hK : IsComponent H K) :
    64 * 6048 ∣ Nat.card (K ⧸ center K) := by
  obtain ⟨_,he,hn,hmove,hcard,_⟩ := h.unitary_ordinary_module_image a K hK
  let X := conjugateSpanBy L M
  let A := (X.subgroupOf H).subgroupOf K
  let q := QuotientGroup.mk' (center K)
  let B := A.map q
  let E := ((V.subgroupOf H).subgroupOf K).map q
  let := he
  change E = ⁅E,B⁆ at hmove
  change 64 ≤ Nat.card E at hcard
  have hEB : E ≤ B := map_mono (subgroupOf_mono K (subgroupOf_mono H h.module_le))
  let U := E.subgroupOf B
  let : U.Normal := normal_subgroupOf_of_le_normalizer hn
  have hXH : X ≤ H := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  let e : A ≃* X := (subgroupOfEquivOfLe (h.ordinary_span_le K hK)).trans
    (subgroupOfEquivOfLe hXH)
  let f : X →* B := (q.subgroupMap A).comp e.symm.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective A).comp e.symm.surjective
  have hquot : 6048 ∣ Nat.card (B ⧸ U) := by
    by_contra hh
    have hz := h.unitary_span_hom_eq_one_of_order_not_dvd a hh
      ((QuotientGroup.mk' U).comp f)
    have hBU : (⊤ : Subgroup B) ≤ U := by
      intro b _
      obtain ⟨x,rfl⟩ := hf b
      exact (QuotientGroup.eq_one_iff _).mp (DFunLike.congr_fun hz x)
    have hBE : B ≤ E := fun b hb => hBU (show (⟨b,hb⟩ : B) ∈ ⊤ from mem_top _)
    have hEq : B = E := le_antisymm hBE hEB
    have hbot : E = ⊥ := by
      rw [hEq] at hmove
      apply hmove.trans
      apply commutator_eq_bot_iff_le_centralizer.mpr
      intro x hx y hy
      exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨y,hy⟩ : E) ⟨x,hx⟩)
    rw [hbot,card_bot] at hcard
    omega
  have h64 : 64 ∣ Nat.card E := by
    obtain ⟨d,hd⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
    rw [hd] at hcard ⊢
    exact pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      (show 2 ^ 6 ≤ 2 ^ d from hcard))
  have hprod : 64 * 6048 ∣ Nat.card B := by
    rw [← U.card_mul_index,index_eq_card]
    apply Nat.mul_dvd_mul _ hquot
    rwa [Nat.card_congr (subgroupOfEquivOfLe hEB).toEquiv]
  exact hprod.trans B.card_subgroup_dvd_card
/-- The actual Held carrier has insufficient two-part for this source module. -/
theorem no_unitary_ordinary_held
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D) (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* Held.He) : False := by
  have hd := h.unitary_ordinary_module_order_dvd a K hK
  rw [Nat.card_congr e.toEquiv] at hd
  have hpow : 2 ^ 11 ∣ Nat.card Held.He := (by decide : 2 ^ 11 ∣ 64 * 6048).trans hd
  obtain ⟨S,hS⟩ := Held.LocalPairs.SylowGeometry.Calculations.exists_representative_sylow
    Held.LocalPairs.SylowGeometry.Calculations.representative_isPGroup
    Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.normalizer_eq
  have hsmall : Nat.card S ≤ 1024 := by
    rw [hS]
    exact (Nat.card_le_card_of_surjective _
      Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.normalForm_surjective).trans
      (by rw [Nat.card_fin])
  have hlarge : 2 ^ 11 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card hpow
  have := Nat.le_of_dvd (Nat.card_pos (α := S)) hlarge
  omega
open ChapterA.Section02 ClassificationModels

/-- Only the actual J₄ and Rudvalis central quotient models remain. -/
theorem unitary_ordinary_two_sporadic_models
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D) (K : Subgroup H) (hK : IsComponent H K) :
    ∃ n : SporadicName, (n = .j4 ∨ n = .ru) ∧
      Nonempty (K ⧸ center K ≃* n.Carrier) := by
  obtain ⟨n,hn,⟨e⟩⟩ := h.unitary_ordinary_three_sporadic_models a K hK
  rcases hn with rfl | rfl | rfl
  · exact ⟨.j4,by simp,⟨e⟩⟩
  · exact (h.no_unitary_ordinary_held a K hK e).elim
  · exact ⟨.ru,by simp,⟨e⟩⟩

end CFSG.Quasithin.ChapterC.HypothesisC28
