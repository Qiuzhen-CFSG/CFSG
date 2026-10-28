module

public import CFSG.Quasithin.ChapterF.Section09.Basic
public import Mathlib.GroupTheory.Index

/-!
# The index and Sylow-normalizer calculations for suitable involutions

For the original F.9.1 setup, `Tᵤ` is the centralizer of `u` in `T`, and
`T₀` centralizes its image modulo the actual central point `V₁`. The map
`t ↦ [u,t]` from `T₀` into `V₁` has kernel `Tᵤ`. The nontrivial action
of `Q_H` makes this map surjective, proving the index two and generation
claims. If an element outside `T₀` normalized `Tᵤ`, the two point-valued
commutator maps on `Q_H` would have the same kernel, hence agree. Their
product would centralize `Q_H`, contrary to the second suitability condition.

This supplies the `Q_H` version of Lemma 14.6.3(1), including
`N_T(Tᵤ) = T₀`. The ambient normalizers in 14.6.3(2), (4) require the
later local-group arguments. The conjugate `uᵗ` is explicitly `t⁻¹ut`,
as in the source's suitability condition (U2).

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, pp. 1021–1022.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter14.Section06
variable {G : Type*} [Group G] [Finite G]
variable {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)

/-- The literal subgroup `Tᵤ = C_T(u)`. -/
def suitableCentralizer (u : G) : Subgroup G :=
  (D.T : Subgroup G) ⊓ centralizer ({u} : Set G)

/-- The literal subgroup `T₀ = C_T(ũ)`, using the original `H/V₁` kernel. -/
def suitableQuotientCentralizer (u : G) : Subgroup G :=
  (D.T : Subgroup G) ⊓ h.kernel (zpowers u)

private theorem suitableCentralizer_le_quotient (u : G) (hu : u ∈ D.UH) :
    suitableCentralizer (D := D) u ≤ suitableQuotientCentralizer h u := by
  intro t ht
  refine ⟨ht.1, (h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))).mpr ⟨h.T_le_H ht.1, ?_⟩⟩
  have ht' : t ∈ centralizer (zpowers u : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
    exact ht.2
  intro a ha
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (ht' a ha)]
  exact D.V₁.one_mem

private theorem QH_le_suitableQuotientCentralizer (u : G) (hu : u ∈ D.UH) :
    D.QH ≤ suitableQuotientCentralizer h u := by
  intro q hq
  refine ⟨h.QH_le_T hq,
    (h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))).mpr ⟨pCoreIn_le 2 D.H hq, ?_⟩⟩
  intro a ha
  exact h.commutator_UH_QH_le_point
    (commutator_mem_commutator ((zpowers_le.mpr hu) ha) hq)

private def suitableCommutator (u : G) (hu : u ∈ D.UH) :
    suitableQuotientCentralizer h u →* D.V₁ where
  toFun t := ⟨⁅u, (t : G)⁆,
    ((h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))).mp t.property.2).2 u (mem_zpowers u)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := by
    apply Subtype.ext
    change ⁅u, (a : G) * (b : G)⁆ = ⁅u, (a : G)⁆ * ⁅u, (b : G)⁆
    have hb : ⁅u, (b : G)⁆ ∈ D.V₁ :=
      ((h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))).mp b.property.2).2 u (mem_zpowers u)
    have hc := h.H_centralizes (h.T_le_H a.property.1) _ hb
    rw [commutatorElement_mul_right_eq_mul_conj]
    calc
      _ = ⁅u, (a : G)⁆ * ((a : G) * ⁅u, (b : G)⁆) * (a : G)⁻¹ := by group
      _ = _ := by rw [← hc]; group

private theorem suitableCommutator_ker (u : G) (hu : u ∈ D.UH) :
    (suitableCommutator h u hu).ker =
      (suitableCentralizer (D := D) u).subgroupOf (suitableQuotientCentralizer h u) := by
  ext t
  change (⟨⁅u, (t : G)⁆, _⟩ : D.V₁) = 1 ↔ _
  rw [Subtype.ext_iff]
  change ⁅u, (t : G)⁆ = 1 ↔ (t : G) ∈ (D.T : Subgroup G) ∧
    (t : G) ∈ centralizer ({u} : Set G)
  rw [commutatorElement_eq_one_iff_mul_comm, mem_centralizer_singleton_iff]
  exact ⟨fun hc => ⟨t.property.1, hc.symm⟩, fun hc => hc.2.symm⟩

/-- Lemma 14.6.3(1): both indices, generation by `Q_H` and `Tᵤ`, and the
normalizer inside the original Sylow subgroup, from (U0), the index part
of (U1), and the `Q_H` form of (U2). -/
theorem suitable_involution_indices (u : G) (hu : u ∈ D.UH)
    (hindex : (suitableQuotientCentralizer h u).relIndex (D.T : Subgroup G) = 2)
    (hmove : ¬ D.QH ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (D.T : Subgroup G), t ∉ suitableQuotientCentralizer h u →
      ¬ D.QH ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G)) :
    (suitableCentralizer (D := D) u).relIndex (suitableQuotientCentralizer h u) = 2 ∧
      (suitableCentralizer (D := D) u).relIndex (D.T : Subgroup G) = 4 ∧
      suitableQuotientCentralizer h u = D.QH ⊔ suitableCentralizer (D := D) u ∧
      (D.T : Subgroup G) ⊓ normalizer (suitableCentralizer (D := D) u : Set G) =
        suitableQuotientCentralizer h u := by
  classical
  let Tu := suitableCentralizer (D := D) u
  let T0 := suitableQuotientCentralizer h u
  have hTu0 : Tu ≤ T0 := suitableCentralizer_le_quotient h u hu
  have hQ0 : D.QH ≤ T0 := QH_le_suitableQuotientCentralizer h u hu
  let f := suitableCommutator h u hu
  have hfrange : f.range ≠ ⊥ := by
    intro hb
    apply hmove
    intro q hq
    have hm : f ⟨q, hQ0 hq⟩ ∈ f.range := ⟨⟨q, hQ0 hq⟩, rfl⟩
    have hz : f ⟨q, hQ0 hq⟩ = 1 := by simpa only [hb, mem_bot] using hm
    have he : ⁅u, q⁆ = 1 := congrArg Subtype.val hz
    exact mem_centralizer_singleton_iff.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp he).symm
  have hfrangeCard : Nat.card f.range = 2 := by
    have hd := f.range.card_subgroup_dvd_card
    rw [h.point_card] at hd
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
      (fun hi => hfrange (card_eq_one.mp hi))
  have hTuIndex : Tu.relIndex T0 = 2 := by
    change (Tu.subgroupOf T0).index = 2
    rw [← suitableCommutator_ker h u hu, index_ker]
    exact hfrangeCard
  have hIndexFour : Tu.relIndex (D.T : Subgroup G) = 4 := by
    rw [← relIndex_mul_relIndex Tu T0 (D.T : Subgroup G) hTu0 inf_le_left,
      hTuIndex, hindex]
  have hgenerate : T0 = D.QH ⊔ Tu := by
    have hs : D.QH ⊔ Tu ≤ T0 := sup_le hQ0 hTu0
    have hi : (Tu.relIndex (D.QH ⊔ Tu) * (D.QH ⊔ Tu).relIndex T0).Prime := by
      rw [relIndex_mul_relIndex Tu (D.QH ⊔ Tu) T0 le_sup_right hs, hTuIndex]
      exact Nat.prime_two
    rcases Nat.prime_mul_iff.mp hi with ⟨_, hh⟩ | ⟨_, hh⟩
    · exact le_antisymm (relIndex_eq_one.mp hh) hs
    · exact (hmove (le_sup_left.trans ((relIndex_eq_one.mp hh).trans inf_le_right))).elim
  have hnormalTu : T0 ≤ normalizer (Tu : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hTu0).mp (normal_of_index_eq_two hTuIndex)
  refine ⟨hTuIndex, hIndexFour, hgenerate, le_antisymm ?_ (le_inf inf_le_left hnormalTu)⟩
  intro t ht
  by_contra ht0
  apply hproduct t ht.1 ht0
  intro q hq
  let v := (MulAut.conj t⁻¹) u
  have hv : v ∈ D.UH := by
    exact ((le_normalizer_conjugateSpanBy D.Vplus D.H
      (D.H.inv_mem (h.T_le_H ht.1))) u).mp hu
  have hcomm_u : ⁅u, q⁆ ∈ D.V₁ :=
    h.commutator_UH_QH_le_point (commutator_mem_commutator hu hq)
  have hcomm_v : ⁅v, q⁆ ∈ D.V₁ :=
    h.commutator_UH_QH_le_point (commutator_mem_commutator hv hq)
  have hsamezero : ⁅u, q⁆ = 1 ↔ ⁅v, q⁆ = 1 := by
    have hqT : q ∈ (D.T : Subgroup G) := h.QH_le_T hq
    have hqTu : q ∈ Tu ↔ ⁅u, q⁆ = 1 := by
      change (q ∈ (D.T : Subgroup G) ∧ q ∈ centralizer ({u} : Set G)) ↔ _
      rw [mem_centralizer_singleton_iff, commutatorElement_eq_one_iff_mul_comm]
      exact ⟨fun hh => hh.2.symm, fun hh => ⟨hqT, hh.symm⟩⟩
    have hqtTu : t * q * t⁻¹ ∈ Tu ↔ ⁅u, t * q * t⁻¹⁆ = 1 := by
      change (t * q * t⁻¹ ∈ (D.T : Subgroup G) ∧
        t * q * t⁻¹ ∈ centralizer ({u} : Set G)) ↔ _
      rw [mem_centralizer_singleton_iff, commutatorElement_eq_one_iff_mul_comm]
      exact ⟨fun hh => hh.2.symm,
        fun hh => ⟨(D.T : Subgroup G).mul_mem ((D.T : Subgroup G).mul_mem ht.1 hqT)
          ((D.T : Subgroup G).inv_mem ht.1), hh.symm⟩⟩
    have hc : ⁅u, t * q * t⁻¹⁆ = 1 ↔ ⁅v, q⁆ = 1 := by
      have hf := (MulAut.conj t⁻¹).injective.eq_iff
        (a := ⁅u, t * q * t⁻¹⁆) (b := 1)
      rw [map_one, map_commutatorElement] at hf
      have he : (MulAut.conj t⁻¹) (t * q * t⁻¹) = q := by
        change t⁻¹ * (t * q * t⁻¹) * (t⁻¹)⁻¹ = q
        group
      rw [he] at hf
      exact hf.symm
    exact hqTu.symm.trans (((ht.2 q).trans hqtTu).trans hc)
  have hcomm_eq : ⁅u, q⁆ = ⁅v, q⁆ := by
    obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : D.V₁)).mp h.point_card
    by_cases hzero : ⁅u, q⁆ = 1
    · exact hzero.trans (hsamezero.mp hzero).symm
    · have hzero' : ⁅v, q⁆ ≠ 1 := mt hsamezero.mpr hzero
      exact congrArg Subtype.val ((hz ⟨⁅u, q⁆, hcomm_u⟩
        (fun he => hzero (congrArg Subtype.val he))).trans
          (hz ⟨⁅v, q⁆, hcomm_v⟩ (fun he => hzero' (congrArg Subtype.val he))).symm)
  have hsquare : ⁅u, q⁆ * ⁅u, q⁆ = 1 := by
    have hh := pow_card_eq_one' (x := (⟨⁅u, q⁆, hcomm_u⟩ : D.V₁))
    rw [h.point_card, pow_two] at hh
    exact congrArg Subtype.val hh
  have hcentral := h.H_centralizes (h.UH_le_H hu) _ hcomm_v
  have hzero : ⁅u * v, q⁆ = 1 := by
    rw [commutatorElement_mul_left_eq_conj_mul, ← hcentral,
      mul_inv_cancel_right, ← hcomm_eq]
    exact hsquare
  exact mem_centralizer_singleton_iff.mpr
    (commutatorElement_eq_one_iff_mul_comm.mp hzero).symm

end CFSG.Quasithin.Chapter14.Section06
