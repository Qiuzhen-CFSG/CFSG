module

public import Theory.CommutativeAlgebra.HilbertSamuelMaximalIdeal
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Length

/-!
# Successive maximal-ideal quotients

The exact sequence between consecutive powers of the maximal ideal identifies
`length_R (m ^ n / m ^ (n + 1))` with the forward difference of the cumulative
Hilbert--Samuel function. Consequently its eventual degree is one less in
positive dimension. In dimension zero the maximal ideal is nilpotent, so these
graded lengths are eventually zero.

These are the finite-difference consequences of Stacks Project,
Proposition 10.60.9 (tag 00KQ), used when associated graded rings are compared
with homogeneous polynomial rings.
-/

open Filter

namespace NumericalPolynomial

noncomputable section

/-- Eventual numerical degree is unchanged after deleting the first term. -/
lemma HasDegree.comp_succ {f : ℕ → ℤ} {d : ℕ} (h : HasDegree f d) :
    HasDegree (fun n ↦ f (n + 1)) d := by
  obtain ⟨P, hP, hdegree, hrep⟩ := h
  refine ⟨P.taylor 1, (Polynomial.taylor_eq_zero 1 P).not.mpr hP, ?_, ?_⟩
  · simpa using (Polynomial.natDegree_taylor P 1).trans hdegree
  · rw [EventuallyRepresents, eventually_atTop] at hrep ⊢
    obtain ⟨N, hN⟩ := hrep
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [Polynomial.taylor_eval,
      show (n : ℚ) + 1 = ((n + 1 : ℕ) : ℚ) by norm_num,
      hN (n + 1) (hn.trans (Nat.le_add_right n 1))]

/-- Eventual numerical degree can be recovered after deleting the first term. -/
lemma HasDegree.of_comp_succ {f : ℕ → ℤ} {d : ℕ}
    (h : HasDegree (fun n ↦ f (n + 1)) d) : HasDegree f d := by
  obtain ⟨P, hP, hdegree, hrep⟩ := h
  refine ⟨P.taylor (-1), (Polynomial.taylor_eq_zero (-1) P).not.mpr hP, ?_, ?_⟩
  · simpa using (Polynomial.natDegree_taylor P (-1)).trans hdegree
  · rw [EventuallyRepresents, eventually_atTop] at hrep ⊢
    obtain ⟨N, hN⟩ := hrep
    refine ⟨N + 1, fun n hn ↦ ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    calc
      (P.taylor (-1)).eval ((N + 1 + k : ℕ) : ℚ) =
          P.eval ((N + k : ℕ) : ℚ) := by
        rw [Polynomial.taylor_eval]
        push_cast
        ring_nf
      _ = (f (N + k + 1) : ℚ) := hN (N + k) (Nat.le_add_right N k)
      _ = (f (N + 1 + k) : ℚ) := by
        congr 2
        all_goals omega

end

end NumericalPolynomial

namespace HilbertSamuel

noncomputable section

open IsLocalRing

/-- The quotient `I ^ n / I ^ (n + 1)` as an `R`-module. -/
public abbrev IdealSuccessiveQuotient {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) := AssociatedGradedPiece I n

/-- The length of the degree-`n` part of the maximal-ideal associated graded ring. -/
@[expose] public def maximalIdealGradedLength
    (R : Type*) [CommRing R] [IsLocalRing R]
    (n : ℕ) : ℤ :=
  (Module.length R (IdealSuccessiveQuotient (maximalIdeal R) n)).toNat

private def successiveQuotientInclusion {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) :
    IdealSuccessiveQuotient I n →ₗ[R] R ⧸ (I ^ (n + 1) : Submodule R R) :=
  Submodule.mapQ _ _ ((I ^ n : Ideal R) : Submodule R R).subtype le_rfl

private lemma successiveQuotientInclusion_injective {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) : Function.Injective (successiveQuotientInclusion I n) := by
  rw [← LinearMap.ker_eq_bot]
  simp [successiveQuotientInclusion, Submodule.ker_mapQ]

private lemma successiveQuotient_exact {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) :
    Function.Exact (successiveQuotientInclusion I n)
      (Submodule.factor (Ideal.pow_le_pow_right n.le_succ)) := by
  rw [LinearMap.exact_iff]
  simp [successiveQuotientInclusion, Submodule.range_mapQ, Submodule.ker_mapQ]

lemma length_quotient_pow_succ_eq_add (R : Type*) [CommRing R]
    (I : Ideal R) (n : ℕ) :
    Module.length R (R ⧸ I ^ (n + 1)) =
      Module.length R (IdealSuccessiveQuotient I n) + Module.length R (R ⧸ I ^ n) := by
  simpa [add_comm] using Module.length_eq_add_of_exact
    (successiveQuotientInclusion I n)
    (Submodule.factor (Ideal.pow_le_pow_right n.le_succ))
    (successiveQuotientInclusion_injective I n)
    (Submodule.factor_surjective (Ideal.pow_le_pow_right n.le_succ))
    (successiveQuotient_exact I n)

private lemma maximalIdeal_mem_minimalPrimes_pow_succ
    (R : Type*) [CommRing R] [IsLocalRing R] (n : ℕ) :
    maximalIdeal R ∈ (maximalIdeal R ^ (n + 1)).minimalPrimes := by
  let m : Ideal R := maximalIdeal R
  change m ∈ (m ^ (n + 1)).minimalPrimes
  let _ : m.IsPrime := by
    dsimp [m]
    infer_instance
  rw [← (m ^ (n + 1)).radical_minimalPrimes,
    m.radical_pow (Nat.succ_ne_zero n), Ideal.IsPrime.radical,
    Ideal.minimalPrimes_eq_subsingleton_self]
  · exact Set.mem_singleton m
  · infer_instance

private lemma length_quotient_maximalIdeal_pow_succ_ne_top
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (n : ℕ) :
    Module.length R (R ⧸ maximalIdeal R ^ (n + 1)) ≠ ⊤ := by
  let Q := R ⧸ maximalIdeal R ^ (n + 1)
  let _ : IsArtinianRing Q :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _
      (maximalIdeal_mem_minimalPrimes_pow_succ R n)
  rw [Module.length_eq_of_surjective (S := R) (R := Q) (M := Q)
    Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

lemma maximalIdealHilbertSamuelFunction_succ_sub
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (n : ℕ) :
    maximalIdealHilbertSamuelFunction R (n + 1) -
        maximalIdealHilbertSamuelFunction R n =
      maximalIdealGradedLength R (n + 1) := by
  have hlength := length_quotient_pow_succ_eq_add R (maximalIdeal R) (n + 1)
  have htotal :
      Module.length R (R ⧸ maximalIdeal R ^ ((n + 1) + 1)) ≠ ⊤ :=
    length_quotient_maximalIdeal_pow_succ_ne_top R (n + 1)
  have hprevious : Module.length R (R ⧸ maximalIdeal R ^ (n + 1)) ≠ ⊤ :=
    length_quotient_maximalIdeal_pow_succ_ne_top R n
  have hgraded :
      Module.length R (IdealSuccessiveQuotient (maximalIdeal R) (n + 1)) ≠ ⊤ := by
    intro htop
    apply htotal
    rw [hlength, htop, top_add]
  have hnat := congrArg ENat.toNat hlength
  rw [ENat.toNat_add hgraded hprevious] at hnat
  dsimp [maximalIdealHilbertSamuelFunction, maximalIdealGradedLength]
  omega

/-- A positive Hilbert--Samuel degree drops by one on the associated graded pieces. -/
lemma maximalIdealGradedLength_hasDegree_of_hilbertSamuel_hasDegree_succ
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (d : ℕ)
    (hdegree : NumericalPolynomial.HasDegree
      (maximalIdealHilbertSamuelFunction R) (d + 1)) :
    NumericalPolynomial.HasDegree (maximalIdealGradedLength R) d := by
  apply NumericalPolynomial.HasDegree.of_comp_succ
  simpa only [maximalIdealHilbertSamuelFunction_succ_sub, Nat.add_sub_cancel] using
    hdegree.forwardDifference (by omega)

/-- In positive dimension, the maximal-ideal graded lengths have degree one less
than the cumulative Hilbert--Samuel function. -/
public theorem maximalIdealGradedLength_hasDegree_of_dimension_succ
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (d : ℕ)
    (hd : ringKrullDim R = d + 1) :
    NumericalPolynomial.HasDegree (maximalIdealGradedLength R) d :=
  maximalIdealGradedLength_hasDegree_of_hilbertSamuel_hasDegree_succ R d
    (maximalIdealHilbertSamuel_hasDegree R (d + 1) hd)

/-- In Krull dimension zero, the maximal-ideal graded lengths eventually vanish. -/
public theorem maximalIdealGradedLength_eventuallyEq_zero_of_dimension_zero
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hd : ringKrullDim R = 0) :
    maximalIdealGradedLength R =ᶠ[atTop] 0 := by
  let _ : Ring.KrullDimLE 0 R :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hd
  have hnil : IsNilpotent (maximalIdeal R) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal R).mp
      IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  obtain ⟨N, hN⟩ := hnil
  filter_upwards [eventually_ge_atTop N] with n hn
  have hpow : maximalIdeal R ^ n = ⊥ := by
    apply le_antisymm
    · exact (Ideal.pow_le_pow_right hn).trans_eq hN
    · exact bot_le
  simp [maximalIdealGradedLength, IdealSuccessiveQuotient, hpow]

end


end HilbertSamuel
