module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.AmbientControl
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PlaneCentralizerCard
public import Theory.GroupTheory.ConjugationOrbitSize
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# Fusion of involutions in the original HS point core

The central cyclic four injects the square-one elements of the point core
into their complement. There are therefore at most 32 square-one elements.
For a seed point outside the marked involution line, the full plane
centralizer has order 256. Its orbit under the marked involution centralizer
has length 30, exhausting the square-one elements other than one and the
marked involution. Seed fusion then fuses every point-core involution to
the marked involution.

This is a direct consequence of the exact HS1--HS2 local hypotheses
preceding Aschbacher--Smith I.4.8, printed p.418.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims

private theorem square_one_card_le {Q : Type*} [Group Q] [Finite Q]
    (h : CoreShape Q) : ({q : Q | q ^ 2 = 1} : Set Q).ncard ≤ 32 := by
  classical
  obtain ⟨e⟩ := h.center_model
  let c : center Q := e.symm (Multiplicative.ofAdd (1 : ZMod 4))
  have hc : (c : Q) ^ 2 ≠ 1 := by
    intro hh
    have hh' : c ^ 2 = 1 := Subtype.ext hh
    have he := congrArg e hh'
    have hn : (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 ≠ 1 := by decide +kernel
    exact hn (by simpa only [map_pow, map_one, MulEquiv.apply_symm_apply, c] using he)
  let S : Set Q := {q | q ^ 2 = 1}
  have hi : Set.InjOn (fun q : Q => (c : Q) * q) S :=
    (mul_right_injective (c : Q)).injOn
  have hm : (fun q : Q => (c : Q) * q) '' S ⊆ Sᶜ := by
    rintro _ ⟨q, hq, rfl⟩ hh
    apply hc
    change q ^ 2 = 1 at hq
    change ((c : Q) * q) ^ 2 = 1 at hh
    rw [(show Commute (c : Q) q from (mem_center_iff.mp c.property q).symm).mul_pow,
      hq, mul_one] at hh
    exact hh
  have hle := Set.ncard_le_ncard hm
  rw [hi.ncard_image] at hle
  have hsum := Set.ncard_add_ncard_compl S
  rw [h.card] at hsum
  change S.ncard ≤ 32
  omega

variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private theorem seed_plane_centralizer (h : TypeAt z V) (w : G)
    (hw : w ∈ V) (hwz : w ∉ zpowers z) :
    Nat.card (centralizer ({z} : Set G) ⊓ centralizer ({w} : Set G) : Subgroup G) = 256 := by
  let := h.elementary
  let W := zpowers z ⊔ zpowers w
  have hWV : W ≤ V := sup_le (zpowers_le.mpr h.involution_mem_seed) (zpowers_le.mpr hw)
  have hcomm : Commute z w := congrArg Subtype.val
    (mul_comm (⟨z, h.involution_mem_seed⟩ : V) ⟨w, hw⟩)
  have hw2 : w ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian w hw
  have hW : Nat.card W = 4 := by
    rw [card_sup_zpowers_of_normalizing_involution _ _ hw2 hwz]
    · rw [Nat.card_zpowers, h.involution]
    · apply centralizer_le_normalizer
      rw [zpowers_eq_closure, centralizer_closure]
      exact mem_centralizer_singleton_iff.mpr hcomm.symm
  have hC : centralizer (W : Set G) =
      centralizer ({z} : Set G) ⊓ centralizer ({w} : Set G) := by
    ext g
    simp only [mem_inf]
    have he : g ∈ centralizer (W : Set G) ↔ W ≤ centralizer ({g} : Set G) := by
      constructor
      · intro hg x hx
        exact mem_centralizer_singleton_iff.mpr (hg x hx)
      · intro hg x hx
        exact mem_centralizer_singleton_iff.mp (hg hx)
    rw [he, sup_le_iff, zpowers_le, zpowers_le]
    simp only [mem_centralizer_singleton_iff]
    constructor <;> rintro ⟨hz, hw⟩ <;> exact ⟨hz.symm, hw.symm⟩
  rw [← hC]
  exact h.plane_centralizer_card W hWV hW

/-- Every involution in the original marked point core is conjugate in the
original ambient group to the original marked involution. -/
theorem TypeAt.centralizer_core_involution_isConj (h : TypeAt z V)
    (q : G) (hq : q ∈ (involutionCentralizer z).pCoreIn 2) (hq2 : orderOf q = 2) :
    IsConj q z := by
  classical
  let H := involutionCentralizer z
  let Q := H.pCoreIn 2
  have hz1 : z ≠ 1 := by intro he; simpa [he] using h.involution
  have hq1 : q ≠ 1 := by intro he; simp [he] at hq2
  by_cases hqz : q = z
  · exact hqz ▸ IsConj.refl z
  have hVQ : V ≤ Q := by
    change V ≤ (pCore 2 H).map H.subtype
    rw [← h.centralizer_fitting]
    exact h.seed_le_core
  have hzQ : z ∈ Q := hVQ h.involution_mem_seed
  have heQ : CoreShape Q := (h.centralizer_core.of_equiv
    (MulEquiv.subgroupCongr h.centralizer_fitting)).of_equiv
      ((pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective)
  let S : Set G := {x | x ∈ Q ∧ x ^ 2 = 1}
  have hS : S.ncard ≤ 32 := by
    have he : S = Subtype.val '' ({x : Q | x ^ 2 = 1} : Set Q) := by
      ext x
      constructor
      · rintro ⟨hx, hx2⟩
        exact ⟨⟨x, hx⟩, Subtype.ext hx2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.property, congrArg Subtype.val hx⟩
    rw [he, Set.ncard_image_of_injective _ Subtype.val_injective]
    exact square_one_card_le heQ
  let T := S \ ({1, z} : Set G)
  have hT : T.ncard ≤ 30 := by
    have hz2 : z ^ 2 = 1 := h.involution ▸ pow_orderOf_eq_one z
    have hins : ({1, z} : Set G) ⊆ S := by
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact ⟨Q.one_mem, one_pow 2⟩
      · have hx' := Set.mem_singleton_iff.mp hx
        exact hx' ▸ ⟨hzQ, hz2⟩
    have hc := Set.ncard_sdiff_add_ncard_of_subset hins
    have hp : ({1, z} : Set G).ncard = 2 := by simp [hz1.symm]
    rw [hp] at hc
    change T.ncard + 2 = S.ncard at hc
    omega
  obtain ⟨w, hw, hwz⟩ : ∃ w ∈ V, w ∉ zpowers z := by
    by_contra hn
    have hv : V ≤ zpowers z := by
      intro w hw
      by_contra hnw
      exact hn ⟨w, hw, hnw⟩
    have hc := card_le_of_le hv
    rw [h.seed_card, Nat.card_zpowers, h.involution] at hc
    omega
  have hw1 : w ≠ 1 := fun he => hwz (he ▸ (zpowers z).one_mem)
  have hwne : w ≠ z := fun he => hwz (he ▸ mem_zpowers z)
  let : MulAction H G := MulAction.compHom G
    (ConjAct.toConjAct.toMonoidHom.comp H.subtype)
  let O := MulAction.orbit H w
  have hs : MulAction.stabilizer H w =
      (centralizer ({z} : Set G) ⊓ centralizer ({w} : Set G)).subgroupOf H := by
    ext g
    change (g : G) * w * (g : G)⁻¹ = w ↔
      (g : G) ∈ centralizer ({z} : Set G) ∧ (g : G) ∈ centralizer ({w} : Set G)
    rw [and_iff_right g.property, mem_centralizer_singleton_iff,
      mul_inv_eq_iff_eq_mul]
  have hO : O.ncard = 30 := by
    have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H w)
    rw [Nat.card_prod, hs, Nat.card_congr (subgroupOfEquivOfLe
      (show centralizer ({z} : Set G) ⊓ centralizer ({w} : Set G) ≤ H from inf_le_left)).toEquiv,
      seed_plane_centralizer h w hw hwz, h.centralizer_card] at hc
    change O.ncard * 256 = 7680 at hc
    omega
  have hOT : O ⊆ T := by
    rintro x ⟨g, rfl⟩
    have hwQ : (⟨w, pCoreIn_le 2 H (hVQ hw)⟩ : H) ∈ pCore 2 H := by
      obtain ⟨v, hv, he⟩ := hVQ hw
      have hvw : v = ⟨w, pCoreIn_le 2 H (hVQ hw)⟩ := Subtype.ext he
      exact hvw ▸ hv
    have hxQ : (g : G) * w * (g : G)⁻¹ ∈ Q :=
      ⟨g * ⟨w, pCoreIn_le 2 H (hVQ hw)⟩ * g⁻¹,
        (inferInstance : (pCore 2 H).Normal).conj_mem _ hwQ g, rfl⟩
    have hw2 : w ^ 2 = 1 := by
      let := h.elementary
      exact elemPow_eq_one_of_isElementaryAbelian w hw
    refine ⟨⟨hxQ, ?_⟩, ?_⟩
    · change ((g : G) * w * (g : G)⁻¹) ^ 2 = 1
      simpa only [map_pow, map_one, MulAut.conj_apply] using congrArg (MulAut.conj (g : G)) hw2
    · change (g : G) * w * (g : G)⁻¹ ∉ ({1, z} : Set G)
      intro hx
      rcases Set.mem_insert_iff.mp hx with hx | hx
      · exact hw1 ((MulAut.conj (g : G)).injective (hx.trans (map_one _).symm))
      · have hzfix : (MulAut.conj (g : G)) z = z := by
          change (g : G) * z * (g : G)⁻¹ = z
          rw [mem_centralizer_singleton_iff.mp g.property, mul_inv_cancel_right]
        exact hwne ((MulAut.conj (g : G)).injective
          ((Set.mem_singleton_iff.mp hx).trans hzfix.symm))
  have he : O = T := Set.eq_of_subset_of_ncard_le hOT (hO ▸ hT)
  have hqin : q ∈ O := by
    rw [he]
    exact ⟨⟨hq, hq2 ▸ pow_orderOf_eq_one q⟩, by simp [hq1, hqz]⟩
  obtain ⟨g, hg⟩ := hqin
  obtain ⟨m, hm⟩ := h.seed_transitive (⟨w, hw⟩ : V) ⟨z, h.involution_mem_seed⟩
    (fun he => hw1 (congrArg Subtype.val he))
    (fun he => hz1 (congrArg Subtype.val he))
  have hqw : IsConj q w := (isConj_iff.mpr ⟨(g : G), hg⟩).symm
  have hwz' : IsConj w z := isConj_iff.mpr ⟨(m : G), congrArg Subtype.val hm⟩
  exact hqw.trans hwz'

end CFSG.Quasithin.HigmanSims
