module

public import Theory.CommutativeAlgebra.AssociatedGraded
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The maximal-ideal Hilbert--Samuel degree

This module proves Stacks Project, Proposition 10.60.9 (tag 00KQ): for a
Noetherian local ring `R`, the eventual polynomial computing
`length_R (R / m ^ (n + 1))` has degree exactly `ringKrullDim R`.

The upper bound chooses a parameter ideal with `d` generators and compares its
Hilbert--Samuel polynomial with the maximal-ideal polynomial. For the lower
bound, a saturated prime chain is read from the maximal ideal downward. At each
strict prime inclusion, multiplication by a nonzero element in the quotient
domain and the filtered short-exact degree theorem force a strict degree drop.
No reducedness, domain, Cohen--Macaulay, or finite-type hypothesis is used.
-/

namespace HilbertSamuel

open IsLocalRing
open scoped Pointwise

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

private lemma maximalIdeal_isIdealOfDefinition (T : Type*) [CommRing T] [IsLocalRing T] :
    (maximalIdeal T).IsIdealOfDefinition := by
  exact (inferInstance : (maximalIdeal T).IsPrime).radical

private noncomputable def maximalIdealPolynomial (T : Type*) [CommRing T]
    [IsNoetherianRing T] [IsLocalRing T] : Polynomial ℚ :=
  (idealPolynomial_exists (maximalIdeal T) (maximalIdeal_isIdealOfDefinition T)).choose

private lemma maximalIdealPolynomial_isPolynomial (T : Type*) [CommRing T]
    [IsNoetherianRing T] [IsLocalRing T] :
    IsPolynomial (maximalIdeal T) T (maximalIdealPolynomial T) :=
  (idealPolynomial_exists (maximalIdeal T) (maximalIdeal_isIdealOfDefinition T)).choose_spec

private lemma maximalIdealPolynomial_ne_zero (T : Type*) [CommRing T]
    [IsNoetherianRing T] [IsLocalRing T] : maximalIdealPolynomial T ≠ 0 := by
  intro hzero
  have hsub : Subsingleton T :=
    ((maximalIdealPolynomial_isPolynomial T).eq_zero_iff_subsingleton
      (maximalIdeal_isIdealOfDefinition T)).mp hzero
  exact not_subsingleton T hsub

private lemma quotient_length_le_of_surjective (f : R →+* S)
    (hf : Function.Surjective f) (n : ℕ) :
    Module.length S (S ⧸ maximalIdeal S ^ n) ≤
      Module.length R (R ⧸ maximalIdeal R ^ n) := by
  let _ : Algebra R S := f.toAlgebra
  have hmap : (maximalIdeal R ^ n).map f = maximalIdeal S ^ n := by
    rw [Ideal.map_pow, map_maximalIdeal_of_surjective f hf]
  have hle : maximalIdeal R ^ n ≤ (maximalIdeal S ^ n).comap f :=
    Ideal.map_le_iff_le_comap.mp hmap.le
  let fA : R →ₐ[R] S :=
    { f with commutes' := fun r => rfl }
  let q := Ideal.quotientMapₐ (maximalIdeal S ^ n) fA hle
  have hq : Function.Surjective q :=
    Ideal.quotientMap_surjective (H := hle) hf
  have hlength := Module.length_le_of_surjective q.toLinearMap hq
  rw [← Module.length_eq_of_surjective (R := S) (S := R)
    (M := S ⧸ maximalIdeal S ^ n) hf]
  exact hlength

private lemma hilbertFunction_le_of_surjective [IsNoetherianRing R]
    [IsNoetherianRing S] (f : R →+* S) (hf : Function.Surjective f) (n : ℕ) :
    hilbertFunction (maximalIdeal S) S n ≤
      hilbertFunction (maximalIdeal R) R n := by
  have hlength := quotient_length_le_of_surjective f hf n
  have htopR : (maximalIdeal R ^ n • (⊤ : Submodule R R)) =
      (maximalIdeal R ^ n : Submodule R R) := by
    ext x
    simp
  have htopS : (maximalIdeal S ^ n • (⊤ : Submodule S S)) =
      (maximalIdeal S ^ n : Submodule S S) := by
    ext x
    simp
  have hfinite : Module.length R (R ⧸ maximalIdeal R ^ n) ≠ ⊤ := by
    rw [← htopR]
    exact length_quotient_pow_ne_top (M := R)
      (maximalIdeal_isIdealOfDefinition R) n
  have hnat := ENat.toNat_le_toNat hlength hfinite
  simp only [hilbertFunction]
  rw [htopR, htopS]
  exact_mod_cast hnat

private lemma hilbertFunction_eq_restrictScalars_of_surjective
    {M : Type*} [AddCommGroup M] [Module S M]
    (f : R →+* S) (hf : Function.Surjective f) (n : ℕ) :
    let _ : Module R M := Module.compHom M f
    hilbertFunction (maximalIdeal R) M n =
      hilbertFunction (maximalIdeal S) M n := by
  let _ : Algebra R S := f.toAlgebra
  let _ : Module R M := Module.compHom M f
  let _ : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hmap : (maximalIdeal R ^ n).map f = maximalIdeal S ^ n := by
    rw [Ideal.map_pow, map_maximalIdeal_of_surjective f hf]
  have halg : algebraMap R S = f := rfl
  have hsub : maximalIdeal R ^ n • (⊤ : Submodule R M) =
      (maximalIdeal S ^ n • (⊤ : Submodule S M)).restrictScalars R := by
    calc
      maximalIdeal R ^ n • (⊤ : Submodule R M) =
          maximalIdeal R ^ n • (⊤ : Submodule S M).restrictScalars R := by
            rw [Submodule.restrictScalars_top]
      _ = ((maximalIdeal R ^ n).map (algebraMap R S) •
          (⊤ : Submodule S M)).restrictScalars R :=
        (Ideal.smul_restrictScalars (maximalIdeal R ^ n)
          (⊤ : Submodule S M)).symm
      _ = (maximalIdeal S ^ n • (⊤ : Submodule S M)).restrictScalars R := by
        rw [halg, hmap]
  let e₁ := Submodule.quotEquivOfEq
    (maximalIdeal R ^ n • (⊤ : Submodule R M))
    ((maximalIdeal S ^ n • (⊤ : Submodule S M)).restrictScalars R) hsub
  let e₂ := Submodule.Quotient.restrictScalarsEquiv R
    (maximalIdeal S ^ n • (⊤ : Submodule S M))
  have hlength₁ := (e₁.trans e₂).length_eq
  have hlength₂ := Module.length_eq_of_surjective (R := S) (S := R)
    (M := M ⧸ maximalIdeal S ^ n • (⊤ : Submodule S M)) hf
  simp only [hilbertFunction]
  rw [hlength₁, hlength₂]

private lemma isPolynomial_restrictScalars_of_surjective
    {M : Type*} [AddCommGroup M] [Module S M]
    (f : R →+* S) (hf : Function.Surjective f) {P : Polynomial ℚ}
    (hP : IsPolynomial (maximalIdeal S) M P) :
    let _ : Module R M := Module.compHom M f
    IsPolynomial (maximalIdeal R) M P := by
  let _ : Algebra R S := f.toAlgebra
  let _ : Module R M := Module.compHom M f
  filter_upwards [hP] with n hn
  rw [hn, hilbertFunction_eq_restrictScalars_of_surjective f hf n]

private lemma not_isFiniteLength_self_of_nonzero_mem_maximalIdeal
    [IsDomain R] {x : R} (hx0 : x ≠ 0) (hxm : x ∈ maximalIdeal R) :
    ¬ IsFiniteLength R R := by
  intro hfinite
  let _ : IsArtinianRing R :=
    (isArtinianRing_iff_isFiniteLength (R := R)).mpr hfinite
  have hfield : IsField R :=
    IsArtinianRing.isField_of_isReduced_of_isLocalRing R
  have hm : maximalIdeal R = ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
  exact hx0 (by simpa [hm] using hxm)

private theorem maximalIdealPolynomial_quotient_span_degree_lt
    [IsNoetherianRing R] [IsDomain R] {x : R}
    [IsLocalRing (R ⧸ Ideal.span {x})]
    (hx0 : x ≠ 0) (hxm : x ∈ maximalIdeal R) :
    (maximalIdealPolynomial (R ⧸ Ideal.span {x})).degree <
      (maximalIdealPolynomial R).degree := by
  let J : Ideal R := Ideal.span {x}
  let T := R ⧸ J
  let q : R →+* T := Ideal.Quotient.mk J
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  let _ : Algebra R T := q.toAlgebra
  let _ : Module R T := Module.compHom T q
  have hQT : IsPolynomial (maximalIdeal T) T (maximalIdealPolynomial T) :=
    maximalIdealPolynomial_isPolynomial T
  have hQR : IsPolynomial (maximalIdeal R) T (maximalIdealPolynomial T) :=
    isPolynomial_restrictScalars_of_surjective q hq hQT
  have hspan : x • (⊤ : Submodule R R) = (J : Submodule R R) := by
    calc
      x • (⊤ : Submodule R R) =
          (Ideal.span {x} : Ideal R) • (⊤ : Submodule R R) :=
        (Submodule.ideal_span_singleton_smul x (⊤ : Submodule R R)).symm
      _ = (J : Submodule R R) := by simp [J]
  have hQ : IsPolynomial (maximalIdeal R)
      (R ⧸ x • (⊤ : Submodule R R)) (maximalIdealPolynomial T) := by
    rw [hspan]
    exact hQR
  have hxregular : IsSMulRegular R x :=
    ((isRegular_iff_ne_zero').mpr hx0).isSMulRegular
  exact quotient_degree_lt_of_isSMulRegular (maximalIdeal R)
    (maximalIdeal_isIdealOfDefinition R) x hxregular
    (maximalIdealPolynomial_isPolynomial R) hQ
    (not_isFiniteLength_self_of_nonzero_mem_maximalIdeal hx0 hxm)

private theorem maximalIdealPolynomial_degree_le_of_surjective
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) (hf : Function.Surjective f) :
    (maximalIdealPolynomial S).degree ≤ (maximalIdealPolynomial R).degree := by
  have hbound : ∀ᶠ n : ℕ in Filter.atTop,
      |(maximalIdealPolynomial S).eval (n : ℚ)| ≤
        (maximalIdealPolynomial R).eval (n : ℚ) := by
    filter_upwards [maximalIdealPolynomial_isPolynomial S,
      maximalIdealPolynomial_isPolynomial R] with n hS hR
    rw [hS, hR, abs_of_nonneg]
    · exact_mod_cast hilbertFunction_le_of_surjective f hf n
    · simp [hilbertFunction]
  exact NumericalPolynomial.degree_le_of_eventually_abs_eval_le
    (maximalIdealPolynomial_ne_zero R) hbound

private theorem maximalIdealPolynomial_degree_lt_of_prime_lt
    [IsNoetherianRing R] {p q : Ideal R} (hp : p.IsPrime) (hpq : p < q)
    (hq : q.IsPrime) [IsLocalRing (R ⧸ p)] [IsLocalRing (R ⧸ q)] :
    (maximalIdealPolynomial (R ⧸ q)).degree <
      (maximalIdealPolynomial (R ⧸ p)).degree := by
  let S := R ⧸ p
  let T := R ⧸ q
  let πp : R →+* S := Ideal.Quotient.mk p
  let g : S →+* T := Ideal.Quotient.factor hpq.le
  let _ : IsDomain S :=
    (Ideal.Quotient.isDomain_iff_prime p).mpr hp
  obtain ⟨x, hxp, hxq⟩ := SetLike.exists_of_lt hpq
  let xbar : S := πp x
  have hxbar0 : xbar ≠ 0 := by
    change Ideal.Quotient.mk p x ≠ 0
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hxq
  let _ : q.IsPrime := hq
  have hxqm : x ∈ maximalIdeal R :=
    IsLocalRing.le_maximalIdeal_of_isPrime q hxp
  have hxbarm : xbar ∈ maximalIdeal S := by
    rw [← map_maximalIdeal_of_surjective πp Ideal.Quotient.mk_surjective]
    exact Ideal.mem_map_of_mem πp hxqm
  have hspanle : Ideal.span {xbar} ≤ maximalIdeal S := by
    rw [Ideal.span_le]
    simpa using hxbarm
  have hspanne : Ideal.span {xbar} ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal S).ne_top hspanle
  let U := S ⧸ Ideal.span {xbar}
  let πx : S →+* U := Ideal.Quotient.mk (Ideal.span {xbar})
  let _ : Nontrivial U := Ideal.Quotient.nontrivial_iff.mpr hspanne
  let _ : IsLocalRing U := IsLocalRing.of_surjective' πx Ideal.Quotient.mk_surjective
  have hstrict : (maximalIdealPolynomial U).degree <
      (maximalIdealPolynomial S).degree :=
    maximalIdealPolynomial_quotient_span_degree_lt hxbar0 hxbarm
  have hxg : g xbar = 0 := by
    change Ideal.Quotient.factor hpq.le (Ideal.Quotient.mk p x) = 0
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hxp
  have hxker : xbar ∈ RingHom.ker g := RingHom.mem_ker.mpr hxg
  have hspanKer : Ideal.span {xbar} ≤ RingHom.ker g :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxker)
  have hkill : ∀ a : S, a ∈ Ideal.span {xbar} → g a = 0 :=
    fun a ha => RingHom.mem_ker.mp (hspanKer ha)
  let uToT : U →+* T := Ideal.Quotient.lift (Ideal.span {xbar}) g hkill
  have huToT : Function.Surjective uToT :=
    Ideal.Quotient.lift_surjective_of_surjective
      (I := Ideal.span {xbar}) (f := g) hkill
      (Ideal.Quotient.factor_surjective hpq.le)
  exact (maximalIdealPolynomial_degree_le_of_surjective uToT huToT).trans_lt hstrict

private noncomputable def primeQuotientNatDegree [IsNoetherianRing R]
    (p : PrimeSpectrum R) : ℕ := by
  let _ : Nontrivial (R ⧸ p.asIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr p.isPrime.ne_top
  let _ : IsLocalRing (R ⧸ p.asIdeal) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p.asIdeal)
      Ideal.Quotient.mk_surjective
  exact (maximalIdealPolynomial (R ⧸ p.asIdeal)).natDegree

private theorem primeQuotientNatDegree_strictAnti [IsNoetherianRing R] :
    StrictAnti (primeQuotientNatDegree (R := R)) := by
  intro p q hpq
  unfold primeQuotientNatDegree
  let _ : Nontrivial (R ⧸ p.asIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr p.isPrime.ne_top
  let _ : Nontrivial (R ⧸ q.asIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr q.isPrime.ne_top
  let _ : IsLocalRing (R ⧸ p.asIdeal) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p.asIdeal)
      Ideal.Quotient.mk_surjective
  let _ : IsLocalRing (R ⧸ q.asIdeal) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk q.asIdeal)
      Ideal.Quotient.mk_surjective
  have hdegree := maximalIdealPolynomial_degree_lt_of_prime_lt
    p.isPrime hpq q.isPrime
  rw [Polynomial.degree_eq_natDegree
    (maximalIdealPolynomial_ne_zero (R ⧸ q.asIdeal)),
    Polynomial.degree_eq_natDegree
      (maximalIdealPolynomial_ne_zero (R ⧸ p.asIdeal))] at hdegree
  exact_mod_cast hdegree

private theorem primeChain_length_le_maximalIdealPolynomial_natDegree
    [IsNoetherianRing R] (l : LTSeries (PrimeSpectrum R)) :
    l.length ≤ (maximalIdealPolynomial R).natDegree := by
  let d : Fin (l.length + 1) → ℕ :=
    fun i => primeQuotientNatDegree (R := R) (l i)
  have hd : StrictAnti d := by
    intro i j hij
    exact primeQuotientNatDegree_strictAnti (l.strictMono hij)
  have hdrev : StrictMono (fun i : Fin (l.length + 1) => d i.rev) := by
    intro i j hij
    exact hd (by simpa using hij)
  let dl : LTSeries ℕ := LTSeries.mk l.length
    (fun i => d i.rev) hdrev
  have hgap := dl.head_add_length_le_nat
  have hchain : l.length ≤ d 0 := by
    have : d (Fin.last l.length) + l.length ≤ d 0 := by
      dsimp [dl, LTSeries.mk, RelSeries.head, RelSeries.last] at hgap
      simpa using hgap
    omega
  let p := l.head
  let πp : R →+* R ⧸ p.asIdeal := Ideal.Quotient.mk p.asIdeal
  let _ : Nontrivial (R ⧸ p.asIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr p.isPrime.ne_top
  let _ : IsLocalRing (R ⧸ p.asIdeal) :=
    IsLocalRing.of_surjective' πp Ideal.Quotient.mk_surjective
  have hdegree := maximalIdealPolynomial_degree_le_of_surjective
    πp Ideal.Quotient.mk_surjective
  rw [Polynomial.degree_eq_natDegree
      (maximalIdealPolynomial_ne_zero (R ⧸ p.asIdeal)),
    Polynomial.degree_eq_natDegree (maximalIdealPolynomial_ne_zero R)] at hdegree
  have hnat : primeQuotientNatDegree (R := R) p ≤
      (maximalIdealPolynomial R).natDegree := by
    unfold primeQuotientNatDegree
    exact_mod_cast hdegree
  exact hchain.trans (by simpa [d, p, RelSeries.head] using hnat)

private lemma isIdealOfDefinition_of_maximalIdeal_mem_minimalPrimes
    {I : Ideal R} (hI : maximalIdeal R ∈ I.minimalPrimes) :
    I.IsIdealOfDefinition := by
  let m : Ideal R := maximalIdeal R
  have hminimalPrimes : I.minimalPrimes = {m} := by
    ext p
    constructor
    · intro hp
      let _ : p.IsPrime := hp.isPrime
      have hpm : p ≤ m := IsLocalRing.le_maximalIdeal_of_isPrime p
      have hmp : m ≤ p := hI.2 hp.1 hpm
      simpa using le_antisymm hpm hmp
    · rintro rfl
      exact hI
  change I.radical = m
  rw [← Ideal.sInf_minimalPrimes, hminimalPrimes, sInf_singleton]

private lemma hilbertFunction_mono_of_ideal_le [IsNoetherianRing R]
    {I J : Ideal R} (hI : I.IsIdealOfDefinition) (hIJ : I ≤ J) (n : ℕ) :
    hilbertFunction J R n ≤ hilbertFunction I R n := by
  have hpow : (I ^ n : Submodule R R) ≤ (J ^ n : Submodule R R) :=
    pow_le_pow_left' hIJ n
  let q : (R ⧸ (I ^ n : Submodule R R)) →ₗ[R]
      (R ⧸ (J ^ n : Submodule R R)) :=
    Submodule.mapQ _ _ LinearMap.id (by simpa using hpow)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk x, by simp [q]⟩
  have hlength := Module.length_le_of_surjective q hq
  have hfinite : Module.length R (R ⧸ I ^ n • (⊤ : Submodule R R)) ≠ ⊤ :=
    length_quotient_pow_ne_top (M := R) hI n
  have htopI : I ^ n • (⊤ : Submodule R R) = (I ^ n : Submodule R R) := by
    ext x
    simp
  have htopJ : J ^ n • (⊤ : Submodule R R) = (J ^ n : Submodule R R) := by
    ext x
    simp
  rw [htopI] at hfinite
  have hnat := ENat.toNat_le_toNat hlength hfinite
  simp only [hilbertFunction]
  rw [htopJ, htopI]
  exact_mod_cast hnat

private theorem maximalIdealPolynomial_natDegree_le_ringKrullDim
    [IsNoetherianRing R] (d : ℕ) (hd : ringKrullDim R = d) :
    (maximalIdealPolynomial R).natDegree ≤ d := by
  let m : Ideal R := maximalIdeal R
  let _ : m.IsPrime := by dsimp [m]; infer_instance
  obtain ⟨s, hminimal, hcard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing m
  let I : Ideal R := Ideal.span (s : Set R)
  have hI : I.IsIdealOfDefinition := by
    apply isIdealOfDefinition_of_maximalIdeal_mem_minimalPrimes
    simpa [I, m] using hminimal
  obtain ⟨P, hP, hPdegree⟩ := idealPolynomial_exists_of_span I hI s rfl
  have hP0 : P ≠ 0 := by
    intro hzero
    exact not_subsingleton R ((hP.eq_zero_iff_subsingleton hI).mp hzero)
  have hbound : ∀ᶠ n : ℕ in Filter.atTop,
      |(maximalIdealPolynomial R).eval (n : ℚ)| ≤ P.eval (n : ℚ) := by
    filter_upwards [maximalIdealPolynomial_isPolynomial R, hP] with n hm hIeval
    rw [hm, hIeval, abs_of_nonneg]
    · exact_mod_cast hilbertFunction_mono_of_ideal_le hI hI.le_maximalIdeal n
    · simp [hilbertFunction]
  have hdegree : (maximalIdealPolynomial R).degree ≤ P.degree :=
    NumericalPolynomial.degree_le_of_eventually_abs_eval_le hP0 hbound
  rw [Polynomial.degree_eq_natDegree (maximalIdealPolynomial_ne_zero R),
    Polynomial.degree_eq_natDegree hP0] at hdegree
  have hnat : (maximalIdealPolynomial R).natDegree ≤ P.natDegree := by
    exact_mod_cast hdegree
  have hheight : s.card = d := by
    have hcard' := congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) hcard
    have hmheight : (m.height : WithBot ℕ∞) = ringKrullDim R := by
      simp [m]
    have hheight' : ((s.card : ℕ∞) : WithBot ℕ∞) =
        ((d : ℕ∞) : WithBot ℕ∞) := hcard'.trans (hmheight.trans hd)
    exact_mod_cast hheight'
  exact hnat.trans (hPdegree.trans_eq hheight)

private theorem ringKrullDim_le_maximalIdealPolynomial_natDegree
    [IsNoetherianRing R] (d : ℕ) (hd : ringKrullDim R = d) :
    d ≤ (maximalIdealPolynomial R).natDegree := by
  let m : Ideal R := maximalIdeal R
  let _ : m.IsPrime := by dsimp [m]; infer_instance
  obtain ⟨l, hlast, hlength⟩ := m.exists_ltSeries_length_eq_height
  have hlength' := congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) hlength
  have hmheight : (m.height : WithBot ℕ∞) = ringKrullDim R := by
    simp [m]
  have hlengthNat : l.length = d := by
    have hcoe : (((l.length : ℕ) : ℕ∞) : WithBot ℕ∞) =
        (((d : ℕ) : ℕ∞) : WithBot ℕ∞) := hlength'.trans (hmheight.trans hd)
    exact_mod_cast hcoe
  rw [← hlengthNat]
  exact primeChain_length_le_maximalIdealPolynomial_natDegree l

private theorem maximalIdealPolynomial_natDegree_eq_ringKrullDim
    [IsNoetherianRing R] (d : ℕ) (hd : ringKrullDim R = d) :
    (maximalIdealPolynomial R).natDegree = d :=
  le_antisymm
    (maximalIdealPolynomial_natDegree_le_ringKrullDim d hd)
    (ringKrullDim_le_maximalIdealPolynomial_natDegree d hd)

/-- The cumulative Hilbert--Samuel function of the maximal ideal. -/
@[expose] public def maximalIdealHilbertSamuelFunction
    (T : Type*) [CommRing T] [IsLocalRing T]
    (n : ℕ) : ℤ :=
  (Module.length T (T ⧸ maximalIdeal T ^ (n + 1))).toNat

/-- Stacks Project, Proposition 10.60.9 (tag 00KQ), in maximal-ideal form. -/
public theorem maximalIdealHilbertSamuel_hasDegree (T : Type*) [CommRing T]
    [IsNoetherianRing T] [IsLocalRing T] (d : ℕ)
    (hd : ringKrullDim T = d) :
    NumericalPolynomial.HasDegree (maximalIdealHilbertSamuelFunction T) d := by
  let P := maximalIdealPolynomial T
  refine ⟨P.taylor 1, (Polynomial.taylor_eq_zero 1 P).not.mpr
    (maximalIdealPolynomial_ne_zero T), ?_, ?_⟩
  · rw [Polynomial.natDegree_taylor]
    exact maximalIdealPolynomial_natDegree_eq_ringKrullDim d hd
  · rw [NumericalPolynomial.EventuallyRepresents, Filter.eventually_atTop]
    have hP := maximalIdealPolynomial_isPolynomial T
    rw [IsPolynomial, NumericalPolynomial.EventuallyRepresents,
      Filter.eventually_atTop] at hP
    obtain ⟨N, hN⟩ := hP
    refine ⟨N, fun n hn => ?_⟩
    have hfunction : hilbertFunction (maximalIdeal T) T (n + 1) =
        maximalIdealHilbertSamuelFunction T n := by
      have hsub : maximalIdeal T ^ (n + 1) • (⊤ : Submodule T T) =
          (maximalIdeal T ^ (n + 1) : Submodule T T) := by
        ext x
        simp
      dsimp [hilbertFunction, maximalIdealHilbertSamuelFunction]
      exact congrArg (fun q : ℕ∞ => (q.toNat : ℤ))
        (Submodule.quotEquivOfEq _ _ hsub).length_eq
    rw [Polynomial.taylor_eval,
      show (n : ℚ) + 1 = ((n + 1 : ℕ) : ℚ) by norm_num,
      hN (n + 1) (hn.trans (Nat.le_add_right n 1)), hfunction]

end

end HilbertSamuel
