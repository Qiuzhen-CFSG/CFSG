module
public import Theory.GroupAction.SymplecticRankThree.PolarityDesign
public import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
public import Mathlib.Tactic.Ring

/-!
# The symplectic rank-three intersection parameters

The double-counting equation with subdegrees q(q+1) and q³ forces
μ=q+1 and λ=q−1 once μ is positive. Divisibility by q+1 gives a positive
integer multiplier; the degree bound makes it less than two for every q≥2.
Closed neighborhoods then form the actual reflexive symmetric incidence
relation with block size q²+q+1 and pairwise intersections q+1.

This constructs the polarity design from graph parameters. Neither an
identification with projective space nor group recognition is assumed.
Positivity of μ is discharged from primitive orbital connectivity in the
rank-three action consumer.

Source: D. G. Higman, *Finite permutation groups of rank 3*, Math. Z. 86
(1964), Lemmas 5 and 8 and the first paragraph of Theorem 2, pp.148,153–154.
-/

public noncomputable section
namespace Theory.GroupAction.SymplecticRankThree

/-- The arithmetic in Higman Theorem 2 from its double-counting equation.
Only q ≥ 2 is required, including for the strict inequality excluding a
second positive multiple of q+1. -/
theorem parameters_of_counting {q l m : ℕ} (hq : 2 ≤ q) (hm : 0 < m)
    (h : (q*(q+1)) * (q*(q+1)-l-1) = q^3*m) :
    l = q-1 ∧ m = q+1 := by
  have hq0 : 0 < q := by omega
  have he : (q+1)*(q*(q+1)-l-1) = q^2*m := by
    apply Nat.eq_of_mul_eq_mul_left hq0
    nlinarith [h]
  have hcop : Nat.Coprime (q+1) (q^2) := by
    simpa only [Nat.add_comm] using (Nat.coprime_add_self_left.mpr
      (Nat.coprime_one_left q)).pow_right 2
  have hd : q+1 ∣ m := hcop.dvd_of_dvd_mul_left (he ▸ dvd_mul_right (q+1) _)
  obtain ⟨t, ht⟩ := hd
  have hz : q*(q+1)-l-1 = q^2*t := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < q+1)
    rw [he, ht]
    ring
  have ht0 : 0 < t := by
    by_contra h
    have : t = 0 := by omega
    simp only [this, mul_zero] at ht
    omega
  have ht2 : t < 2 := by
    by_contra hn
    have hb : q^2*2 ≤ q^2*t := Nat.mul_le_mul_left _ (by omega)
    have hb' : q*(q+1)-l-1 < q*(q+1) := by
      have : 0 < q*(q+1) := Nat.mul_pos hq0 (by omega)
      omega
    have hqq : q ≤ q^2 := by nlinarith
    nlinarith [hz]
  have ht1 : t = 1 := by omega
  rw [ht1, mul_one] at ht hz
  refine ⟨?_, ht⟩
  have he' : q*(q+1) = q^2+q := by ring
  rw [he'] at hz
  have : 0 < q^2 := pow_pos hq0 _
  omega

namespace SimpleGraph
variable {Ω : Type*} [Fintype Ω] (Γ : SimpleGraph Ω) [DecidableRel Γ.Adj]

/-- The rank-three intersection parameters obtained from the actual SRG count.
Positivity of μ must come from the source action's primitivity/connectedness. -/
theorem symplectic_parameters {q l m : ℕ} (hq : 2 ≤ q)
    (h : Γ.IsSRGWith (q^3+q^2+q+1) (q*(q+1)) l m) (hm : 0 < m) :
    l = q-1 ∧ m = q+1 := by
  apply parameters_of_counting hq hm
  have he := h.param_eq Γ (by positivity)
  have hn : q^3+q^2+q+1-q*(q+1)-1 = q^3 := by
    have : q*(q+1) = q^2+q := by ring
    rw [this]
    omega
  simpa only [hn] using he

omit [Fintype Ω] [DecidableRel Γ.Adj] in
private theorem closed_inter_of_adj {a b : Ω} (hab : Γ.Adj a b) :
    (insert a (Γ.neighborSet a) ∩ insert b (Γ.neighborSet b)) =
      insert a (insert b (Γ.commonNeighbors a b)) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, SimpleGraph.mem_neighborSet,
    SimpleGraph.mem_commonNeighbors]
  constructor
  · rintro ⟨ha,hb⟩
    rcases ha with rfl | ha
    · exact Or.inl rfl
    rcases hb with rfl | hb
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨ha,hb⟩)
  · rintro (rfl | rfl | hx)
    · exact ⟨Or.inl rfl, Or.inr hab.symm⟩
    · exact ⟨Or.inr hab, Or.inl rfl⟩
    · exact ⟨Or.inr hx.1, Or.inr hx.2⟩

omit [Fintype Ω] [DecidableRel Γ.Adj] in
private theorem closed_inter_of_not_adj {a b : Ω} (hne : a ≠ b) (hab : ¬ Γ.Adj a b) :
    (insert a (Γ.neighborSet a) ∩ insert b (Γ.neighborSet b)) =
      Γ.commonNeighbors a b := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, SimpleGraph.mem_neighborSet,
    SimpleGraph.mem_commonNeighbors]
  constructor
  · rintro ⟨ha,hb⟩
    rcases ha with rfl | ha
    · rcases hb with hb | hb
      · exact (hne hb).elim
      · exact (hab hb.symm).elim
    rcases hb with rfl | hb
    · exact (hab ha).elim
    · exact ⟨ha,hb⟩
  · intro hx
    exact ⟨Or.inr hx.1, Or.inr hx.2⟩

/-- Closed neighborhoods form the symmetric polarity design in Higman Lemma 8.
This constructs incidence; no projective coordinates are assumed. -/
@[expose] def polarityDesign {q l m : ℕ} (hq : 2 ≤ q)
    (h : Γ.IsSRGWith (q^3+q^2+q+1) (q*(q+1)) l m) (hm : 0 < m) :
    PolarityDesign Ω q where
  incident a b := b = a ∨ Γ.Adj a b
  refl a := Or.inl rfl
  symm := by
    intro a b h
    exact h.elim (fun he => Or.inl he.symm) (fun ha => Or.inr ha.symm)
  block_card := by
    intro a
    change (insert a (Γ.neighborSet a)).ncard = _
    rw [Set.ncard_insert_of_notMem (by simp)]
    change Nat.card (Γ.neighborSet a)+1 = _
    rw [Nat.card_eq_fintype_card, Γ.card_neighborSet_eq_degree, h.regular a]
    ring
  intersection_card := by
    intro a b hab
    change (insert a (Γ.neighborSet a) ∩ insert b (Γ.neighborSet b)).ncard = _
    obtain ⟨hl,hm'⟩ := symplectic_parameters Γ hq h hm
    by_cases ha : Γ.Adj a b
    · rw [closed_inter_of_adj Γ ha, Set.ncard_insert_of_notMem
        (by simp only [Set.mem_insert_iff]; exact not_or_intro hab (Γ.notMem_commonNeighbors_left a b)),
        Set.ncard_insert_of_notMem (Γ.notMem_commonNeighbors_right a b)]
      change Nat.card (Γ.commonNeighbors a b)+1+1 = _
      rw [Nat.card_eq_fintype_card, h.of_adj a b ha, hl]
      omega
    · rw [closed_inter_of_not_adj Γ hab ha]
      change Nat.card (Γ.commonNeighbors a b) = _
      rw [Nat.card_eq_fintype_card, h.of_not_adj hab ha, hm']

end SimpleGraph
end Theory.GroupAction.SymplecticRankThree
