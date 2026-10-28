/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Fischer/ParkerOrderedFactorSet.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Fischer.ParkerFactorSet

/-!
# Ordered-basis Parker factor sets

Finite sums over ordered basis indices construct the bilinear correction
and trilinear term. Expanding the sums proves the polarization formula and
additive defect needed for the Golay specialization.

Source: Gerald Höhn, ATLAS, `Atlas/Fischer/ParkerOrderedFactorSet.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Definitions remain exposed because downstream coordinate proofs unfold them.
-/

@[expose] public section


namespace Atlas.Fischer

open scoped BigOperators
private theorem parker_ite_add (p : Prop) [Decidable p] (x y : ParkerBit) :
    (if p then x + y else 0) = (if p then x else 0) + (if p then y else 0) := by
  split <;> simp_all


def parkerOrderedTheta {n : ℕ} (t : Fin n → Fin n → Fin n → ParkerBit)
    (a b c : Fin n → ParkerBit) : ParkerBit :=
  ∑ i, ∑ j, ∑ k, if j < k then a i * b j * c k * t i j k else 0

def parkerOrderedBeta {n : ℕ} (d : Fin n → Fin n → ParkerBit)
    (a b : Fin n → ParkerBit) : ParkerBit :=
  ∑ i, ∑ j, a i * b j * d i j

def parkerOrderedFactorSet {n : ℕ} (t : Fin n → Fin n → Fin n → ParkerBit)
    (d : Fin n → Fin n → ParkerBit) (a b : Fin n → ParkerBit) : ParkerBit :=
  parkerOrderedTheta t a b b + parkerOrderedBeta d a b

theorem parkerOrderedTheta_add_left {n : ℕ}
    (t : Fin n → Fin n → Fin n → ParkerBit) (a a' b c : Fin n → ParkerBit) :
    parkerOrderedTheta t (a + a') b c =
      parkerOrderedTheta t a b c + parkerOrderedTheta t a' b c := by
  simp [parkerOrderedTheta, add_mul, parker_ite_add, Finset.sum_add_distrib]

theorem parkerOrderedTheta_add_middle {n : ℕ}
    (t : Fin n → Fin n → Fin n → ParkerBit) (a b b' c : Fin n → ParkerBit) :
    parkerOrderedTheta t a (b + b') c =
      parkerOrderedTheta t a b c + parkerOrderedTheta t a b' c := by
  simp [parkerOrderedTheta, mul_add, add_mul, parker_ite_add, Finset.sum_add_distrib]

theorem parkerOrderedTheta_add_right {n : ℕ}
    (t : Fin n → Fin n → Fin n → ParkerBit) (a b c c' : Fin n → ParkerBit) :
    parkerOrderedTheta t a b (c + c') =
      parkerOrderedTheta t a b c + parkerOrderedTheta t a b c' := by
  simp [parkerOrderedTheta, mul_add, add_mul, parker_ite_add, Finset.sum_add_distrib]

theorem parkerOrderedBeta_add_left {n : ℕ}
    (d : Fin n → Fin n → ParkerBit) (a a' b : Fin n → ParkerBit) :
    parkerOrderedBeta d (a + a') b =
      parkerOrderedBeta d a b + parkerOrderedBeta d a' b := by
  simp [parkerOrderedBeta, add_mul, Finset.sum_add_distrib]

theorem parkerOrderedBeta_add_right {n : ℕ}
    (d : Fin n → Fin n → ParkerBit) (a b b' : Fin n → ParkerBit) :
    parkerOrderedBeta d a (b + b') =
      parkerOrderedBeta d a b + parkerOrderedBeta d a b' := by
  simp [parkerOrderedBeta, mul_add, add_mul, Finset.sum_add_distrib]

theorem parkerOrderedFactorSet_defect {n : ℕ}
    (t : Fin n → Fin n → Fin n → ParkerBit)
    (d : Fin n → Fin n → ParkerBit) (a b c : Fin n → ParkerBit) :
    parkerOrderedFactorSet t d a b + parkerOrderedFactorSet t d (a + b) c +
      parkerOrderedFactorSet t d b c + parkerOrderedFactorSet t d a (b + c) =
        parkerOrderedTheta t a b c + parkerOrderedTheta t a c b := by
  simp only [parkerOrderedFactorSet, parkerOrderedTheta_add_left,
    parkerOrderedTheta_add_middle, parkerOrderedTheta_add_right,
    parkerOrderedBeta_add_left, parkerOrderedBeta_add_right]
  ring_nf
  simp only [show (2 : ParkerBit) = 0 from rfl, mul_zero, add_zero, zero_add]

theorem parkerOrderedTheta_polarize {n : ℕ}
    (t : Fin n → Fin n → Fin n → ParkerBit)
    (hs : ∀ i j k, t i j k = t i k j) (hz : ∀ i j, t i j j = 0)
    (a b c : Fin n → ParkerBit) :
    parkerOrderedTheta t a b c + parkerOrderedTheta t a c b =
      ∑ i, ∑ j, ∑ k, a i * b j * c k * t i j k := by
  have hswap : parkerOrderedTheta t a c b =
      ∑ i, ∑ j, ∑ k, if k < j then a i * b j * c k * t i j k else 0 := by
    unfold parkerOrderedTheta
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    split
    · rw [hs i k j]
      ring
    · rfl
  rw [hswap]
  unfold parkerOrderedTheta
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rcases lt_trichotomy j k with h | h | h
  · simp [h, not_lt_of_gt h]
  · subst k
    simp [hz]
  · simp [h, not_lt_of_gt h]

end Atlas.Fischer
