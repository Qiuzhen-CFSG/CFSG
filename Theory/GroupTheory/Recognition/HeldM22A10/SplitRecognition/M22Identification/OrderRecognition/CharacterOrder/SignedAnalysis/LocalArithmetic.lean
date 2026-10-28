module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.Boundary

/-!
# Local divisibility for Janko's signed-character exclusions

The actual Sylow subgroups and the supplied normalizer complements give the
required factors of the ambient order and its exact two- and three-parts.
An irreducible degree is always a positive natural number; multiplying by a
sign gives an integer divisor of the order. The E16 restriction congruence is
transported with the same sign on the degree and the involution value.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Lemmas 11–12, pp.13–14.
-/

noncomputable section
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.SignedAnalysis
open LocalModelDichotomy
variable {G : Type*} [Group G] [Finite G]

/-- Only the actual local subgroup orders are needed for the divisibility
contradictions in Lemmas 11 and 12. -/
public theorem local_order_factors (D : LocalData G) (k : TwistedModel ≃* D.centralizer)
    (L : LocalAnalysisData D k) :
    128 ∣ Nat.card G ∧ 5 ∣ Nat.card G ∧ 9 ∣ Nat.card G ∧ 7 ∣ Nat.card G := by
  have h2 : 128 ∣ Nat.card G := by
    simpa only [D.sylow_card] using D.sylow.toSubgroup.card_subgroup_dvd_card
  obtain ⟨K, _, ⟨e⟩⟩ := L.normalizer_F
  have hk : Nat.card K = 120 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm]
    norm_num
  have h5 : 5 ∣ Nat.card G := by
    have hd := K.card_subgroup_dvd_card.trans
      (Subgroup.normalizer (CaseII.F D k : Set G)).card_subgroup_dvd_card
    rw [hk] at hd
    exact dvd_trans (by norm_num : 5 ∣ 120) hd
  let P : Sylow 3 G := Classical.choice inferInstance
  have hp : Nat.card P = 9 := (L.sylow_three P).2.1
  have h3 : 9 ∣ Nat.card G := by
    simpa only [hp] using P.toSubgroup.card_subgroup_dvd_card
  obtain ⟨A, ha, _⟩ := L.nonabelian_twenty_one
  have h7 : 7 ∣ Nat.card G := by
    have hd := A.card_subgroup_dvd_card
    rw [ha] at hd
    exact dvd_trans (by norm_num : 7 ∣ 21) hd
  exact ⟨h2, h5, h3, h7⟩

public theorem not_twenty_seven_dvd_order (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k) :
    ¬ 27 ∣ Nat.card G := by
  let P : Sylow 3 G := Classical.choice inferInstance
  intro h
  have hd := P.pow_dvd_card_of_pow_dvd_card (n := 3) h
  rw [(L.sylow_three P).2.1] at hd
  norm_num at hd

public theorem not_two_fifty_six_dvd_order (D : LocalData G) :
    ¬ 256 ∣ Nat.card G := by
  intro h
  have hd := D.sylow.pow_dvd_card_of_pow_dvd_card (n := 8) h
  rw [D.sylow_card] at hd
  norm_num at hd

/-- A signed degree is an integer divisor; the underlying irreducible degree
remains the positive natural number `hχ.degree`. -/
public theorem signed_degree_dvd_order {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    s * (hχ.degree : ℤ) ∣ (Nat.card G : ℤ) := by
  have h : (hχ.degree : ℤ) ∣ (Nat.card G : ℤ) := by exact_mod_cast hχ.degree_dvd_card
  rcases hs with rfl | rfl <;> simpa using h

/-- The restriction congruence with the sign kept on both the degree and value. -/
public theorem signed_degree_congruence (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (s t : ℤ) (hs : s = 1 ∨ s = -1) (ht : (s : ℂ) * χ D.z = (t : ℂ)) :
    16 ∣ s * (hχ.degree : ℤ) + 15 * t := by
  rcases hs with rfl | rfl
  · simp only [Int.cast_one, one_mul] at ht ⊢
    exact degree_congruence_mod_sixteen D k L hχ t ht
  · have hv : χ D.z = ((-t : ℤ) : ℂ) := by
      push_cast
      linear_combination -ht
    have hc := degree_congruence_mod_sixteen D k L hχ (-t) hv
    have he : (-1 : ℤ) * hχ.degree + 15 * t = -((hχ.degree : ℤ) + 15 * (-t)) := by ring
    rw [he]
    exact dvd_neg.mpr hc

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.SignedAnalysis
