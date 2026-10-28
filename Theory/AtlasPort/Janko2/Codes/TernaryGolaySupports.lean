/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/TernaryGolaySupports.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Codes.TernaryGolay

/-!
# TernaryGolaySupports

Supports of weight-six ternary Golay words form the Steiner system
S(5,6,12). The weight identity bounds intersections; pairing opposite words
counts 132 hexads, and counting flags establishes existence through five points.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/TernaryGolaySupports.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators

def ternarySupport (w : TernaryWord) : Finset (Fin 12) :=
  Finset.univ.filter (fun i => w i ≠ 0)

theorem ternarySupport_card (w : TernaryWord) : (ternarySupport w).card = ternaryWeight w := rfl

theorem ternaryWeight_neg (w : TernaryWord) : ternaryWeight (-w) = ternaryWeight w := by
  simp [ternaryWeight]

theorem ternarySupport_neg (w : TernaryWord) : ternarySupport (-w) = ternarySupport w := by
  ext i; simp [ternarySupport]

/-- Over F3, at a common nonzero coordinate exactly one of sum and difference vanishes. -/
theorem ternaryWeight_add_sub (u v : TernaryWord) :
    ternaryWeight (u+v) + ternaryWeight (u-v) +
      3*(ternarySupport u ∩ ternarySupport v).card =
      2*ternaryWeight u + 2*ternaryWeight v := by
  have h : ∀ a b : ZMod 3,
      (if a+b ≠ 0 then 1 else 0 : ℕ) + (if a-b ≠ 0 then 1 else 0) +
        3*(if a ≠ 0 ∧ b ≠ 0 then 1 else 0) =
        2*(if a ≠ 0 then 1 else 0) + 2*(if b ≠ 0 then 1 else 0) := by decide
  simpa only [ternaryWeight, ternarySupport, ← Finset.filter_and,
    Finset.card_filter, Pi.add_apply, Pi.sub_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib] using congrArg (fun f : Fin 12 → ℕ => ∑ i, f i)
      (funext (fun i => h (u i) (v i)))

theorem ternaryGolay_hexad_intersection (u v : TernaryWord)
    (hu : u ∈ ternaryGolay) (hv : v ∈ ternaryGolay)
    (hwu : ternaryWeight u = 6) (hwv : ternaryWeight v = 6)
    (hi : 5 ≤ (ternarySupport u ∩ ternarySupport v).card) :
    v = u ∨ v = -u := by
  by_cases ha : u+v = 0
  · right; exact eq_neg_of_add_eq_zero_right ha
  by_cases hs : u-v = 0
  · left; exact (sub_eq_zero.mp hs).symm
  have h1 := ternaryGolay_minimum (u+v) (ternaryGolay.add_mem hu hv) ha
  have h2 := ternaryGolay_minimum (u-v) (ternaryGolay.sub_mem hu hv) hs
  have he := ternaryWeight_add_sub u v
  omega

def ternaryHexads : Set (Finset (Fin 12)) :=
  {B | ∃ w : ternaryGolay, ternaryWeight w.val = 6 ∧ ternarySupport w.val = B}

theorem ternaryHexads_card (B : Finset (Fin 12)) (hB : B ∈ ternaryHexads) : B.card = 6 := by
  obtain ⟨w, hw, rfl⟩ := hB
  exact hw

theorem ternaryHexads_unique_through_five (S B C : Finset (Fin 12))
    (hS : S.card = 5) (hB : B ∈ ternaryHexads) (hC : C ∈ ternaryHexads)
    (hSB : S ⊆ B) (hSC : S ⊆ C) : B = C := by
  obtain ⟨u, hu, rfl⟩ := hB
  obtain ⟨v, hv, rfl⟩ := hC
  have hi : 5 ≤ (ternarySupport u.val ∩ ternarySupport v.val).card := by
    rw [← hS]
    exact Finset.card_le_card (Finset.subset_inter hSB hSC)
  rcases ternaryGolay_hexad_intersection u.val v.val u.prop v.prop hu hv hi with he | he
  · rw [he]
  · rw [he, ternarySupport_neg]


abbrev TernarySixWords := {w : ternaryGolay // ternaryWeight w.val = 6}

def ternarySixSupport (w : TernarySixWords) : ternaryHexads :=
  ⟨ternarySupport w.val.val, w.val, w.prop, rfl⟩

def ternarySixNeg (w : TernarySixWords) : TernarySixWords :=
  ⟨-w.val, by simpa [ternaryWeight_neg] using w.prop⟩

theorem ternarySixNeg_ne (w : TernarySixWords) : ternarySixNeg w ≠ w := by
  intro h
  have hz : w.val.val = 0 := by
    funext i
    have he := congrFun (congrArg (fun t : TernarySixWords => t.val.val) h) i
    have hc : ∀ a : ZMod 3, -a = a → a = 0 := by decide
    exact hc (w.val.val i) he
  have hw := w.prop
  rw [hz] at hw
  have : ternaryWeight (0 : TernaryWord) = 0 := (ternaryWeight_eq_zero _).mpr rfl
  omega

theorem ternarySixSupport_fiber (w v : TernarySixWords) :
    ternarySixSupport v = ternarySixSupport w ↔ v = w ∨ v = ternarySixNeg w := by
  constructor
  · intro h
    have hs := congrArg Subtype.val h
    have hi : 5 ≤ (ternarySupport w.val.val ∩ ternarySupport v.val.val).card := by
      change ternarySupport v.val.val = ternarySupport w.val.val at hs
      rw [hs, Finset.inter_self, ternarySupport_card, w.prop]
      decide
    rcases ternaryGolay_hexad_intersection w.val.val v.val.val w.val.prop v.val.prop
      w.prop v.prop hi with he | he
    · left; exact Subtype.ext (Subtype.ext he)
    · right; exact Subtype.ext (Subtype.ext he)
  · rintro (rfl|rfl)
    · rfl
    · apply Subtype.ext
      exact ternarySupport_neg _

theorem ternarySixSupport_fiber_card (B : ternaryHexads) :
    Nat.card {w : TernarySixWords // ternarySixSupport w = B} = 2 := by
  classical
  obtain ⟨w, hw, hB⟩ := B.prop
  let r : TernarySixWords := ⟨w, hw⟩
  have hr : ternarySixSupport r = B := Subtype.ext hB
  let e : {v : TernarySixWords // ternarySixSupport v = B} ≃
      ({r, ternarySixNeg r} : Finset TernarySixWords) :=
    Equiv.subtypeEquivRight (fun v => by
      rw [← hr, ternarySixSupport_fiber]; simp)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_pair (ternarySixNeg_ne r).symm]

theorem ternaryHexads_count : Nat.card ternaryHexads = 132 := by
  classical
  let := Fintype.ofFinite ternaryHexads
  have h := Nat.card_congr (Equiv.sigmaFiberEquiv ternarySixSupport)
  rw [Nat.card_sigma] at h
  simp only [ternarySixSupport_fiber_card, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, ← Nat.card_eq_fintype_card] at h
  have hw : Nat.card TernarySixWords = 264 := ternaryGolay_weight_distribution 6
  rw [hw] at h
  omega

abbrev TernaryFiveSets := {S : Finset (Fin 12) // S.card = 5}
abbrev TernaryHexadFlags := (B : ternaryHexads) × (B.val.powersetCard 5)

def ternaryFlagFiveSet (f : TernaryHexadFlags) : TernaryFiveSets :=
  ⟨f.2.val, (Finset.mem_powersetCard.mp f.2.prop).2⟩

theorem ternaryFlagFiveSet_injective : Function.Injective ternaryFlagFiveSet := by
  rintro ⟨B,S⟩ ⟨C,T⟩ h
  have hST : S.val = T.val := congrArg Subtype.val h
  have hB := Finset.mem_powersetCard.mp S.prop
  have hC := Finset.mem_powersetCard.mp T.prop
  have hBC : B = C := Subtype.ext (ternaryHexads_unique_through_five S.val B.val C.val
    hB.2 B.prop C.prop hB.1 (hST ▸ hC.1))
  subst C
  exact congrArg (fun U : B.val.powersetCard 5 => (Sigma.mk B U : TernaryHexadFlags)) (Subtype.ext hST)

theorem ternaryHexadFlags_card : Nat.card TernaryHexadFlags = 792 := by
  classical
  let := Fintype.ofFinite ternaryHexads
  rw [Nat.card_sigma]
  have hc (B : ternaryHexads) : Nat.card (B.val.powersetCard 5) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powersetCard,
      ternaryHexads_card B.val B.prop]
    decide
  simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, ternaryHexads_count]

theorem ternaryFiveSets_card : Nat.card TernaryFiveSets = 792 := by
  let e : TernaryFiveSets ≃ ((Finset.univ : Finset (Fin 12)).powersetCard 5) :=
    Equiv.subtypeEquivRight (fun _ => by simp)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  decide

theorem ternaryFlagFiveSet_bijective : Function.Bijective ternaryFlagFiveSet := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  exact ⟨ternaryFlagFiveSet_injective, ternaryHexadFlags_card.trans ternaryFiveSets_card.symm⟩

theorem ternaryHexads_steiner (S : Finset (Fin 12)) (hS : S.card = 5) :
    ∃! B : Finset (Fin 12), B ∈ ternaryHexads ∧ S ⊆ B := by
  obtain ⟨⟨B,T⟩, h⟩ := ternaryFlagFiveSet_bijective.surjective ⟨S,hS⟩
  have hT : T.val = S := congrArg Subtype.val h
  have hB : S ⊆ B.val := hT ▸ (Finset.mem_powersetCard.mp T.prop).1
  refine ⟨B.val, ⟨B.prop, hB⟩, ?_⟩
  intro C hC
  exact ternaryHexads_unique_through_five S C B.val hS hC.1 B.prop hC.2 hB
end Atlas.Codes
