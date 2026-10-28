module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Statements
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Orders and central quotients of the odd linear-three alternatives

Both groups denoted (S)L₃(p) have central quotient PSL₃(p). The quotient
transport uses the actual multiplicative equivalence and its map on centers.
Their orders differ only by the scalar factor gcd(3,p-1), between one and
three. Monotonicity of p³(p³-1)(p²-1) excludes the fixed exceptional orders
in C.2.7 when p ≥ 5.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
1.3.8, printed p.514. Matrix orders and perfectness are reused from the
attributed ATLAS ports imported above; see LICENSES/ATLAS.txt.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.LinearThreeExclusion

variable {Q : Type*} [Group Q]

private def centerQuotientCongr {D : Type*} [Group D] (e : Q ≃* D) :
    (Q ⧸ center Q) ≃* (D ⧸ center D) :=
  QuotientGroup.congr (center Q) (center D) e (by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (centerCongr e ⟨x, hx⟩).property
    · intro y hy
      exact ⟨e.symm y, (centerCongr e.symm ⟨y, hy⟩).property, e.apply_symm_apply y⟩)

/-- Passing to the center quotient preserves projective models of degree at least three. -/
theorem projective_center_model {n q : ℕ} (hn : 3 ≤ n)
    (hm : ClassicalGroup.IsPSL Q n q) :
    ClassicalGroup.IsPSL (Q ⧸ center Q) n q := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let _ := Atlas.sl_perfect (F := F) n hn
  have hz : center PSL(n,F) = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot SL(n,F)
  exact ⟨F, inferInstance, inferInstance, hF,
    ⟨(centerQuotientCongr e).trans
      ((QuotientGroup.quotientMulEquivOfEq hz).trans (QuotientGroup.quotientBot))⟩⟩

/-- The two source covers have the same projective central quotient. -/
theorem linearThree_center_model {p : ℕ} (hm : XiEmbedding.LinearThreeModel p Q) :
    ClassicalGroup.IsPSL (Q ⧸ center Q) 3 p := by
  rcases hm with ⟨F, _, _, hF, ⟨e⟩⟩ | hm
  · exact ⟨F, inferInstance, inferInstance, hF, ⟨centerQuotientCongr e⟩⟩
  · exact projective_center_model (by decide) hm

/-- A fraction-free order formula retaining the possible scalar factor. -/
theorem linearThree_order {p : ℕ} (hm : XiEmbedding.LinearThreeModel p Q) :
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ 3 ∧
      Nat.card Q * d = p ^ 3 * (p ^ 3 - 1) * (p ^ 2 - 1) := by
  rcases hm with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩
  · refine ⟨1, by decide, by decide, ?_⟩
    rw [mul_one, Nat.card_congr e.toEquiv,
      Subgroup.card_eq_card_quotient_mul_card_subgroup (center SL(3,F)),
      Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin,
      Matrix.PSL3.LinearThree.card_projective_mul_scalar, hF]
  · refine ⟨Nat.gcd 3 (p - 1), Nat.gcd_pos_of_pos_left _ (by decide),
      Nat.gcd_le_left _ (by decide), ?_⟩
    rw [Nat.card_congr e.toEquiv, ← hF,
      Matrix.PSL3.LinearThree.card_projective_mul_scalar]

private theorem orderPolynomial_mono {a b : ℕ} (h : a ≤ b) :
    a ^ 3 * (a ^ 3 - 1) * (a ^ 2 - 1) ≤
      b ^ 3 * (b ^ 3 - 1) * (b ^ 2 - 1) :=
  Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left h 3)
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 3) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)

/-- The alternating, triple-cover, binary G₂ and binary degree-four orders are too small. -/
theorem not_linearThree_of_small_order {p : ℕ} (hp : 5 ≤ p)
    (hc : Nat.card Q ≤ 20160) : ¬ XiEmbedding.LinearThreeModel p Q := by
  intro hm
  obtain ⟨d, _, hd, ho⟩ := linearThree_order hm
  have hlow := orderPolynomial_mono hp
  have hu := Nat.mul_le_mul hc hd
  norm_num at hlow hu
  omega

/-- Neither Sp₄(4) nor L₅(2) has an odd-prime linear-three order. -/
theorem not_linearThree_of_large_exceptional_order {p : ℕ} (hp : 5 ≤ p)
    (hc : Nat.card Q = 979200 ∨ Nat.card Q = 9999360) :
    ¬ XiEmbedding.LinearThreeModel p Q := by
  intro hm
  obtain ⟨d, hdpos, hd, ho⟩ := linearThree_order hm
  rcases hc with hc | hc
  · rw [hc] at ho
    have hplt : p < 7 := by
      by_contra hh
      have hl := orderPolynomial_mono (show 7 ≤ p by omega)
      norm_num at hl
      omega
    interval_cases p <;> norm_num at ho <;> omega
  · rw [hc] at ho
    have hplt : p < 9 := by
      by_contra hh
      have hl := orderPolynomial_mono (show 9 ≤ p by omega)
      norm_num at hl
      omega
    interval_cases p <;> norm_num at ho <;> omega

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.LinearThreeExclusion
