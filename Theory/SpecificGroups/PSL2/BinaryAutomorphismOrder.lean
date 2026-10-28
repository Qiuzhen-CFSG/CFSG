module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import Theory.FieldTheory.FiniteAutomorphismOrder
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The two-part of the automorphism order of binary PSL₂

Semilinear coverage maps the actual field automorphism group onto the outer
quotient. Its order is the field degree n, while the inner subgroup is an image
of PSL₂. Thus the full automorphism order divides q(q² − 1)n. Removing the odd
factor q² − 1 bounds every actual Sylow two-subgroup by qn.

Source: the PSL₂ automorphism calculation of GLS4, Chapter 4, Lemma 3.1(a),
and the comparison used by Aschbacher–Smith, 16.3.4, printed p.1178.
-/

namespace Theory.PSL2.BinaryAutomorphismOrder
open BenderSuzuki.MatrixGroups BenderSuzuki.ZD.Linear Subgroup

private noncomputable def fieldActionHom {F : Type*} [Field F] [CharP F 2] :
    (F ≃+* F) →* MulAut (PSL2MatrixGroup F) where
  toFun := fieldAut
  map_one' := by
    ext x
    obtain ⟨y, rfl⟩ := BenderSuzuki.Converse.pi_surjective x
    rw [fieldAut_apply_pi]
    rfl
  map_mul' σ τ := by
    ext x
    obtain ⟨y, rfl⟩ := BenderSuzuki.Converse.pi_surjective x
    change fieldAut (σ * τ) (BenderSuzuki.Converse.pi F y) =
      fieldAut σ (fieldAut τ (BenderSuzuki.Converse.pi F y))
    rw [fieldAut_apply_pi, fieldAut_apply_pi, fieldAut_apply_pi]
    rfl

/-- The full automorphism order divides `q(q² − 1)n` for `q = 2ⁿ`. -/
public theorem aut_card_dvd {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) :
    Nat.card (MulAut (PSL2MatrixGroup F)) ∣ (2 ^ n * ((2 ^ n) ^ 2 - 1)) * n := by
  let B := PSL2MatrixGroup F
  let I := MulAut.innerSubgroup B
  let q := QuotientGroup.mk' I
  let f := q.comp (fieldActionHom (F := F))
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective I x
    obtain ⟨g, σ, rfl⟩ := semilinear_coverage a
    refine ⟨σ, ?_⟩
    have hg : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
    change q (fieldAut σ) = q (MulAut.conj g * fieldAut σ)
    rw [map_mul, hg, one_mul]
  have ho : Nat.card (MulAut B ⧸ I) ∣ n := by
    rw [← FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hF]
    exact card_dvd_of_surjective f hf
  have hi : Nat.card I ∣ Nat.card B := card_range_dvd (MulAut.conj : B →* MulAut B)
  have hB : Nat.card B = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [← Nat.card_congr (sl2QuotientEquiv F).toEquiv,
      BenderSuzuki.External.huppert614_card_specialLinearGroup, hF]
  rw [← I.card_mul_index]
  exact Nat.mul_dvd_mul (hB ▸ hi) ho

/-- Each actual Sylow two-subgroup of the full automorphism group has order at most `2ⁿn`. -/
public theorem sylow_aut_card_le {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (A : Sylow 2 (MulAut (PSL2MatrixGroup F))) :
    Nat.card A ≤ 2 ^ n * n := by
  obtain ⟨k, hk⟩ := A.isPGroup'.exists_card_eq
  have hdiv : Nat.card A ∣ (2 ^ n * n) * ((2 ^ n) ^ 2 - 1) := by
    simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (A : Subgroup _).card_subgroup_dvd_card.trans (aut_card_dvd hF)
  have hodd : Odd ((2 ^ n) ^ 2 - 1) := by
    apply Nat.Even.sub_odd (by have := Nat.one_le_pow (n * 2) 2 (by omega); simpa [pow_mul] using this)
    · rw [← pow_mul]
      exact (Nat.even_pow' (by omega)).2 even_two
    · exact odd_one
  have hcop : Nat.Coprime (Nat.card A) ((2 ^ n) ^ 2 - 1) := by
    rw [hk]
    exact (Nat.coprime_two_left.mpr hodd).pow_left k
  exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right hdiv)

end Theory.PSL2.BinaryAutomorphismOrder
