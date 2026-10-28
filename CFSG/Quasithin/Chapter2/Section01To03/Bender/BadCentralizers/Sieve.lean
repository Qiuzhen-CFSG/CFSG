module

public import CFSG.Quasithin.Chapter1.Section01.ModelActions115
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.AlternatingInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.OddCharacteristicInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.EvenCharacteristicInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.InnerAlternatingInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.G2Inspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.G2SimpleInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.G2BinaryInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.BinaryLinearInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.SymplecticInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.TrialityInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.TitsInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.ReeInspection.UnipotentCenter
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.MathieuInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.MathieuTwelveInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.MathieuRemainingInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.JankoTwoInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.HigmanSimsInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.JankoFourInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.HeldInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.RudvalisInspection
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.InnerAction.Models
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock

/-!+# The full six-case component inspection in the source Bender argument

All six actual component-action alternatives of 1.1.5 are retained. The
marked model inspections exclude the non-Bender alternatives, including
the central two-quotients and the original Sylow-central sporadic marker.
An abstract cubic center is excluded by O(H)=1, without identifying covers.
The surviving prime-five model is transported to the genuine binary group.

This is the inspection implication on printed p.520 of Proposition 2.2.2.
The universal source classification itself belongs to qt-1-01 and its
quasisimple-involutions producer.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative

namespace CFSG.Quasithin.Chapter2.BenderFusion
open Chapter15.Section03.Candidates.ComponentStructure
open ClassificationModels Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

namespace BadCentralizers

private theorem no_cubic_center (H : Subgroup G) (K : Subgroup H)
    (hK : K.IsSubnormal) (hcore : pPrimeCore 2 H = ⊥)
    (e : center K ≃* Multiplicative (ZMod 3)) : False := by
  have hc : Nat.card (center K) = 3 := by
    rw [Nat.card_congr e.toEquiv]
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hKcore := hK.pPrimeCore_eq_bot hcore K
  have hb : center K = ⊥ := (pPrimeCore_eq_bot_iff.mp hKcore) _ inferInstance
    (by rw [hc]; decide)
  rw [hb, card_bot] at hc
  omega

private theorem fermatMersenne_odd {p : ℕ} (hp : IsFermatOrMersennePrime p) : Odd p := by
  apply hp.1.odd_of_ne_two
  rintro rfl
  rcases hp.2 with ⟨a, ha⟩ | ⟨a, ha⟩
  · have hlow : 2 ≤ 2 ^ (2 ^ a) := Nat.le_pow (by norm_num)
    omega
  · have hd : 2 ∣ 2 ^ a := dvd_pow_self _ (by rintro rfl; norm_num at ha)
    omega

private theorem fermatMersenne_adjacent_power {p : ℕ} (hp : IsFermatOrMersennePrime p) :
    ∃ k : ℕ, p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k := by
  rcases hp.2 with ⟨a, ha⟩ | ⟨a, ha⟩
  · exact ⟨2 ^ a, Or.inl (by rw [ha, Nat.add_sub_cancel])⟩
  · exact ⟨a, Or.inr ha⟩

end BadCentralizers

/-- The source's six alternatives imply a Bender model and inner action
of the original distinguished z. No model-selection premise is introduced. -/
theorem LocalControlWitness.bender_model_of_source115
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥) (L : Subgroup G) (hL : IsComponentIn L H)
    (hLM : ¬ L ≤ M) (h115 : HasModelAction115 (L.subgroupOf H) w.z) :
    IsBenderModel L ∧ ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹ := by
  let K := L.subgroupOf H
  let e : L ≃* K := (subgroupOfEquivOfLe hL.1).symm
  obtain ⟨a, ha, hmodel⟩ := h115
  have hinner (hi : a ∈ (MulAut.conj (G := K)).range) :
      ∃ t : L, ∀ x : L, ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹ := by
    obtain ⟨t, ht⟩ := hi
    refine ⟨e.symm t, ?_⟩
    intro x
    have hh := ha (e x)
    rw [← ht] at hh
    exact hh
  let qE : (L ⧸ pCore 2 L) ≃* (K ⧸ pCore 2 K) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  cases hmodel with
  | lie hs hm hi =>
    have hzin := hinner hi
    have hsL : IsSimpleGroup L := (MulEquiv.isSimpleGroup_congr e).mpr hs
    rcases hm with hb | hr | ⟨n, hn, hnL⟩
    · exact ⟨hb.of_mulEquiv e, hzin⟩
    · exfalso
      cases hr with
      | linear f hf iso =>
        obtain ⟨F, _, _, hF, ⟨r⟩⟩ := iso
        exact w.false_of_inner_even_psl3_component H S hUS hST L hL hLM hsL
          F (by omega) hF (e.trans r) hzin
      | symplectic f hf iso =>
        exact w.false_of_inner_psp4_model H S hUS hST hcore L hL hLM hf
          (iso.of_mulEquiv e) hzin
      | g2 f hf iso =>
        exact w.false_of_inner_even_g2_model H S hUS hST hcore L hL hLM hsL hf
          (iso.of_mulEquiv e) hzin
      | triality f hf iso =>
        exact w.false_of_inner_triality_model H S hUS hST hcore L hL hLM hsL f
          (by omega) (iso.of_mulEquiv e) hzin
      | ree m hm iso =>
        obtain ⟨d, ⟨r⟩⟩ := iso
        exact w.false_of_inner_ree_component H S hUS hST hcore L hL hLM hsL m hm
          (e.trans (r.trans d.modelEquiv)) hzin
      | symplectic_derived iso =>
        obtain ⟨r⟩ := iso
        exact w.false_of_inner_psp4_two_derived_component H S hUS hST hcore L hL hLM
          (e.trans r) hzin
      | g2_derived iso =>
        obtain ⟨r⟩ := iso
        exact w.false_of_inner_g2_binary_component H S hUS hST hcore L hL hLM hsL
          (e.trans r) hzin
      | tits iso =>
        obtain ⟨r⟩ := iso
        exact w.false_of_inner_tits_component H S hUS hST hcore L hL hLM (e.trans r) hzin
    · exact (w.false_of_inner_binary_psl_model H S hUS hST hcore L hL hLM hsL hn
        (hnL.of_mulEquiv e) hzin).elim
  | two_cover _ _ hm hi =>
    have hzin := hinner hi
    exfalso
    rcases hm with hl | hg
    · obtain ⟨F, _, _, hF, ⟨r⟩⟩ := hl
      exact w.false_of_inner_psl3_twoCore_component H S hUS hST hcore L hL hLM F
        (n := 2) (by decide) (by simpa using hF) (qE.trans r) hzin
    · exact w.false_of_inner_g2_four_twoCore_model H S hUS hST hcore L hL hLM
        (hg.of_mulEquiv qE) hzin
  | six σ hσ ha6 =>
    exfalso
    rcases ha6 with ⟨r, hr⟩ | ⟨_, ⟨rZ⟩, _⟩
    · apply w.false_of_alternating_six_component H S hUS hST L hL (e.trans r) σ hσ
      intro x
      have he : a (r.symm x) = r.symm (MulAut.conjNormal σ x) := by
        apply r.injective
        apply Subtype.ext
        rw [r.apply_symm_apply]
        change (r (a (r.symm x)) : Equiv.Perm (Fin 6)) = σ * (x : Equiv.Perm (Fin 6)) * σ⁻¹
        simpa only [r.apply_symm_apply] using hr (r.symm x)
      have hh := ha (r.symm x)
      rw [he] at hh
      exact hh
    · exact BadCentralizers.no_cubic_center H K hL.2.1 hcore rZ
  | seven σ hσ ha7 =>
    exfalso
    rcases ha7 with ⟨r, hr⟩ | ⟨_, ⟨rZ⟩, _⟩
    · apply w.false_of_alternating_seven_component H S hUS hST L hL (e.trans r) σ hσ
      intro x
      have he : a (r.symm x) = r.symm (MulAut.conjNormal σ x) := by
        apply r.injective
        apply Subtype.ext
        rw [r.apply_symm_apply]
        change (r (a (r.symm x)) : Equiv.Perm (Fin 7)) = σ * (x : Equiv.Perm (Fin 7)) * σ⁻¹
        simpa only [r.apply_symm_apply] using hr (r.symm x)
      have hh := ha (r.symm x)
      rw [he] at hh
      exact hh
    · exact BadCentralizers.no_cubic_center H K hL.2.1 hcore rZ
  | odd hm hi =>
    have hzin := hinner hi
    rcases hm with h3 | ⟨p, hp, h2⟩
    · exfalso
      obtain ⟨F, _, _, hF, ⟨r⟩⟩ := h3
      let : Fintype F := Fintype.ofFinite F
      let f : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by
        simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
      exact w.false_of_inner_psl3_three_component H S hUS hST L hL hLM
        (e.trans (r.trans (Atlas.fieldEquivPSL 3 f))) hzin
    · obtain ⟨F, _, _, hF, ⟨r⟩⟩ := h2
      let : Fact p.Prime := ⟨hp.1⟩
      let : Fintype F := Fintype.ofFinite F
      let f : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
        simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
      obtain ⟨k, hk⟩ := BadCentralizers.fermatMersenne_adjacent_power hp
      have hp5 := w.prime_eq_five_of_inner_psl2_component H S hUS hST L hL hLM
        (BadCentralizers.fermatMersenne_odd hp) hk
        (e.trans (r.trans (Atlas.fieldEquivPSL 2 f))) hzin
      exact ⟨InnerActionModels.bender_model_of_psl2_five F (hF.trans hp5) (e.trans r), hzin⟩
  | sporadic name hnj hm hi =>
    have hzin := hinner hi.1
    obtain ⟨r⟩ := hm
    exfalso
    cases name with
    | m11 =>
      exact w.false_of_inner_m11_twoCore_component H S hUS hST hcore L hL hLM
        (qE.trans r) hzin
    | m12 =>
      exact w.false_of_inner_m12_twoCore_component H S hUS hST hcore L hL hLM
        (qE.trans r) hzin
    | m22 =>
      exact w.false_of_inner_m22_twoCore_component H S hUS hST hcore L hL hLM
        (qE.trans r) hzin
    | m23 =>
      exact w.false_of_inner_m23_twoCore_component H S hUS hST hcore L hL hLM
        (qE.trans r) hzin
    | m24 =>
      exact w.false_of_inner_m24_twoCore_component H S hUS hST hcore L hL hLM
        (qE.trans r) hzin
    | j2 =>
      exact w.false_of_inner_j2_twoCore_component H S hUS hST hcore L hL hLM
        (qE.trans r) hzin
    | j3 => exact hnj rfl
    | j4 =>
      exact w.false_of_inner_j4_twoCore_component H S hUS hST hcore L hL hLM
        (qE.trans r) hzin
    | hs =>
      exact w.false_of_inner_hs_twoCore_component H S hUS hST hcore L hL hLM
        (qE.trans r) hzin
    | he =>
      exact w.false_of_inner_held_twoCore_component H S hUS hST hcore L hL hLM
        (qE.trans r) hzin
    | ru =>
      exact w.false_of_inner_rudvalis_twoCore_component H S hUS hST hcore L hL hLM
        (qE.trans r) hzin

end CFSG.Quasithin.Chapter2.BenderFusion
