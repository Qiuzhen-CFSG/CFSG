module

public import Theory.CommutativeAlgebra.GradedHilbert
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Regular.Category

/-!
# Hilbert--Samuel degrees under filtered short exact sequences

For a finite module over a commutative Noetherian local ring, this module defines the cumulative
Hilbert--Samuel function for an ideal of definition and studies any rational polynomial that
eventually represents it.  The principal result is the degree estimate from Stacks Project,
Lemma 10.59.10 (tag 00KC): in a short exact sequence, the failure of polynomial additivity caused
by the induced filtrations has degree strictly below the polynomial of an infinite-length
submodule.  It implies that the middle degree is the maximum of the outer degrees and that
quotienting by an injectively acting element strictly lowers degree, in the form needed by the
prime-chain induction of tag 00KQ.

The proof identifies the pointwise error with the negative length of the kernel after reducing
modulo `I ^ n`.  Artin--Rees bounds this kernel by a fixed finite difference of the submodule's
Hilbert--Samuel function.  Taylor translation turns that bound into a polynomial of smaller
degree.  Separate stabilization and Nakayama arguments identify the zero and finite-length cases.
The implementation uses the numerical-polynomial interface from `GradedHilbert`, Mathlib's adic
filtration and Artin--Rees theorems, and the module-length exact-sequence API.
-/

open Filter
open Pointwise
open scoped Polynomial

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

@[expose] public section

namespace NumericalPolynomial

noncomputable section

lemma EventuallyRepresents.unique {f : ℕ → ℤ} {P Q : ℚ[X]}
    (hP : EventuallyRepresents P f) (hQ : EventuallyRepresents Q f) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  rw [EventuallyRepresents] at hP hQ
  have h := hP.and hQ
  rw [eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  refine (Set.infinite_range_of_injective (f := fun n : ℕ ↦ ((n + N : ℕ) : ℚ)) ?_).mono ?_
  · exact Nat.cast_injective.comp fun _ _ h ↦ Nat.add_right_cancel h
  · rintro _ ⟨n, rfl⟩
    exact (hN (n + N) (Nat.le_add_left N n)).1.trans
      (hN (n + N) (Nat.le_add_left N n)).2.symm

lemma leadingCoeff_nonneg_of_eventually_eval_nonneg {P : ℚ[X]}
    (hP : ∀ᶠ n : ℕ in atTop, 0 ≤ P.eval (n : ℚ)) : 0 ≤ P.leadingCoeff := by
  by_contra! hlead
  by_cases hdegree : 0 < P.degree
  · have hneg : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) < 0 :=
      ((P.tendsto_atBot_of_leadingCoeff_nonpos hdegree hlead.le).comp
        (tendsto_natCast_atTop_atTop (R := ℚ))).eventually (eventually_lt_atBot 0)
    obtain ⟨n, hn, hneg⟩ := (hP.and hneg).exists
    exact (not_lt_of_ge hn) hneg
  · have hconst := Polynomial.eq_C_of_degree_le_zero (p := P) (not_lt.mp hdegree)
    obtain ⟨n, hn⟩ := hP.exists
    rw [hconst, Polynomial.eval_C] at hn
    have hlc : P.leadingCoeff = P.coeff 0 := by rw [hconst]; simp
    rw [hlc] at hlead
    exact (not_lt_of_ge hn) hlead

lemma leadingCoeff_pos_of_eventually_eval_nonneg {P : ℚ[X]} (hP0 : P ≠ 0)
    (hP : ∀ᶠ n : ℕ in atTop, 0 ≤ P.eval (n : ℚ)) : 0 < P.leadingCoeff :=
  (leadingCoeff_nonneg_of_eventually_eval_nonneg hP).lt_of_ne'
    (Polynomial.leadingCoeff_ne_zero.mpr hP0)

lemma degree_le_of_eventually_abs_eval_le {P Q : ℚ[X]} (hQ : Q ≠ 0)
    (h : ∀ᶠ n : ℕ in atTop, |P.eval (n : ℚ)| ≤ Q.eval (n : ℚ)) : P.degree ≤ Q.degree := by
  by_contra! hdegree
  have hratio := Polynomial.abs_div_tendsto_atTop_atTop_of_degree_gt P Q hdegree hQ
  have hgt : ∀ᶠ n : ℕ in atTop, 1 < |P.eval (n : ℚ) / Q.eval (n : ℚ)| :=
    (hratio.comp (tendsto_natCast_atTop_atTop (R := ℚ))).eventually_gt_atTop 1
  have hQeval : ∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) ≠ 0 :=
    ((tendsto_natCast_atTop_atTop (R := ℚ)).eventually
      (Polynomial.eventually_atTop_not_isRoot Q hQ)).mono fun _ hn ↦ by
        simpa [Polynomial.IsRoot] using hn
  obtain ⟨n, hn, hgt, hQeval⟩ := (h.and (hgt.and hQeval)).exists
  rw [abs_div] at hgt
  have hQabs : 0 < |Q.eval (n : ℚ)| := abs_pos.mpr hQeval
  rw [lt_div_iff₀ hQabs] at hgt
  exact (not_lt_of_ge (hn.trans (le_abs_self _))) (by simpa using hgt)

end

end NumericalPolynomial

namespace Ideal

/-- An ideal whose radical is the maximal ideal of a local ring. -/
def IsIdealOfDefinition {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R) : Prop :=
  I.radical = IsLocalRing.maximalIdeal R

lemma IsIdealOfDefinition.le_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    {I : Ideal R} (hI : I.IsIdealOfDefinition) : I ≤ IsLocalRing.maximalIdeal R := by
  rw [← hI]
  exact I.le_radical

end Ideal

namespace HilbertSamuel

noncomputable section

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The cumulative Hilbert--Samuel function of an adic filtration. -/
def hilbertFunction (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) : ℤ :=
  (Module.length R (M ⧸ I ^ n • (⊤ : Submodule R M))).toNat

/-- A polynomial which eventually computes an adic Hilbert--Samuel function. -/
def IsPolynomial (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
    (P : ℚ[X]) : Prop :=
  NumericalPolynomial.EventuallyRepresents P (hilbertFunction I M)

private lemma maximalIdeal_mem_minimalPrimes_pow {I : Ideal R}
    (hI : I.IsIdealOfDefinition) {n : ℕ} (hn : n ≠ 0) :
    IsLocalRing.maximalIdeal R ∈ (I ^ n).minimalPrimes := by
  let m : Ideal R := IsLocalRing.maximalIdeal R
  change m ∈ (I ^ n).minimalPrimes
  let _ : m.IsPrime := by
    dsimp [m]
    infer_instance
  rw [← (I ^ n).radical_minimalPrimes, I.radical_pow hn, hI,
    Ideal.minimalPrimes_eq_subsingleton_self]
  exact Set.mem_singleton m

lemma length_quotient_pow_ne_top {I : Ideal R} (hI : I.IsIdealOfDefinition) (n : ℕ) :
    Module.length R (M ⧸ I ^ n • (⊤ : Submodule R M)) ≠ ⊤ := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  let Q := R ⧸ I ^ n
  let V := M ⧸ I ^ n • (⊤ : Submodule R M)
  letI : Module Q V := by
    dsimp [Q, V]
    infer_instance
  letI : IsArtinianRing Q :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _
           (maximalIdeal_mem_minimalPrimes_pow hI hn)
  letI : Module.Finite Q V := Module.Finite.of_restrictScalars_finite R Q V
  letI : IsArtinian Q V := inferInstance
  letI : IsNoetherian Q V := inferInstance
  rw [Module.length_eq_of_surjective (S := R) (R := Q) (M := V)
    Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

lemma IsPolynomial.eventually_eval_nonneg {I : Ideal R} {P : ℚ[X]}
    (hP : IsPolynomial I M P) : ∀ᶠ n : ℕ in atTop, 0 ≤ P.eval (n : ℚ) := by
  filter_upwards [hP] with n hn
  rw [hn]
  simp [hilbertFunction]

lemma IsPolynomial.leadingCoeff_nonneg {I : Ideal R} {P : ℚ[X]}
    (hP : IsPolynomial I M P) : 0 ≤ P.leadingCoeff :=
  NumericalPolynomial.leadingCoeff_nonneg_of_eventually_eval_nonneg hP.eventually_eval_nonneg

lemma IsPolynomial.leadingCoeff_pos {I : Ideal R} {P : ℚ[X]}
    (hP : IsPolynomial I M P) (hP0 : P ≠ 0) : 0 < P.leadingCoeff :=
  NumericalPolynomial.leadingCoeff_pos_of_eventually_eval_nonneg hP0 hP.eventually_eval_nonneg

lemma IsPolynomial.eq_zero_iff_subsingleton {I : Ideal R} (hI : I.IsIdealOfDefinition)
    {P : ℚ[X]} (hP : IsPolynomial I M P) : P = 0 ↔ Subsingleton M := by
  constructor
  · intro hP0
    rw [hP0, IsPolynomial, NumericalPolynomial.EventuallyRepresents, eventually_atTop] at hP
    obtain ⟨N, hN⟩ := hP
    let n := N + 1
    have hn : n ≠ 0 := by simp [n]
    have hnN : N ≤ n := Nat.le_add_right N 1
    have hvalue : hilbertFunction I M n = 0 := by
      have := hN n hnN
      simpa [hilbertFunction] using this.symm
    have hvalueNat :
        (Module.length R (M ⧸ I ^ n • (⊤ : Submodule R M))).toNat = 0 := by
      dsimp [hilbertFunction] at hvalue
      exact_mod_cast hvalue
    have hlength : Module.length R (M ⧸ I ^ n • (⊤ : Submodule R M)) = 0 := by
      rcases ENat.toNat_eq_zero.mp hvalueNat with h | h
      · exact h
      · exact (length_quotient_pow_ne_top (M := M) hI n h).elim
    have hquot : Subsingleton (M ⧸ I ^ n • (⊤ : Submodule R M)) :=
      Module.length_eq_zero_iff.mp hlength
    have hfiltration : I ^ n • (⊤ : Submodule R M) = ⊤ := by
      apply top_unique
      intro x _
      exact (Submodule.Quotient.mk_eq_zero _).mp (hquot.elim _ _)
    have hpow_jac : I ^ n ≤ (⊥ : Ideal R).jacobson := by
      rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
      exact (Ideal.pow_le_self hn).trans hI.le_maximalIdeal
    have htopbot : (⊤ : Submodule R M) = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (I ^ n) ⊤ Module.Finite.fg_top
        hfiltration.ge hpow_jac
    exact ⟨fun x y ↦ sub_eq_zero.mp <| by
        have hxy : x - y ∈ (⊤ : Submodule R M) := Submodule.mem_top
        rw [htopbot] at hxy
        exact hxy⟩
  · intro hM
    letI : Subsingleton M := hM
    apply NumericalPolynomial.EventuallyRepresents.unique hP
    simp [NumericalPolynomial.EventuallyRepresents, hilbertFunction]

lemma IsPolynomial.ne_zero_of_not_isFiniteLength {I : Ideal R} (hI : I.IsIdealOfDefinition)
    {P : ℚ[X]} (hP : IsPolynomial I M P) (hM : ¬ IsFiniteLength R M) : P ≠ 0 := by
  intro hP0
  letI : Subsingleton M := (hP.eq_zero_iff_subsingleton hI).mp hP0
  exact hM IsFiniteLength.of_subsingleton

private lemma eventually_pow_smul_top_eq_bot {I : Ideal R} (hI : I.IsIdealOfDefinition)
    (hM : IsFiniteLength R M) :
    ∀ᶠ n : ℕ in atTop, I ^ n • (⊤ : Submodule R M) = ⊥ := by
  letI : IsArtinian R M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).2
  let F : ℕ →o (Submodule R M)ᵒᵈ :=
    ⟨fun n ↦ I ^ n • (⊤ : Submodule R M), fun _ _ h ↦
      Submodule.smul_mono_left (Ideal.pow_le_pow_right h)⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes F
  have hstable (m : ℕ) (hm : n ≤ m) :
      I ^ n • (⊤ : Submodule R M) = I ^ m • (⊤ : Submodule R M) := by
    exact hn m hm
  have hIne : I ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hI.le_maximalIdeal
  have hnbot : I ^ n • (⊤ : Submodule R M) = ⊥ := by
    rw [← I.iInf_pow_smul_eq_bot_of_isLocalRing (M := M) hIne]
    apply le_antisymm
    · rw [le_iInf_iff]
      intro m
      by_cases hm : n ≤ m
      · exact (hstable m hm).le
      · exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_of_not_ge hm))
    · exact iInf_le _ n
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [← hstable m hm, hnbot]

lemma IsPolynomial.eq_C_of_isFiniteLength {I : Ideal R} (hI : I.IsIdealOfDefinition)
    {P : ℚ[X]} (hP : IsPolynomial I M P) (hM : IsFiniteLength R M) :
    P = Polynomial.C ((Module.length R M).toNat : ℚ) := by
  apply NumericalPolynomial.EventuallyRepresents.unique hP
  filter_upwards [eventually_pow_smul_top_eq_bot hI hM] with n hn
  simp only [Polynomial.eval_C, hilbertFunction]
  exact_mod_cast (congrArg ENat.toNat
    (Submodule.quotEquivOfEqBot (I ^ n • (⊤ : Submodule R M)) hn).length_eq).symm

lemma IsPolynomial.degree_le_zero_of_isFiniteLength {I : Ideal R}
    (hI : I.IsIdealOfDefinition) {P : ℚ[X]} (hP : IsPolynomial I M P)
    (hM : IsFiniteLength R M) : P.degree ≤ 0 := by
  rw [hP.eq_C_of_isFiniteLength hI hM]
  exact Polynomial.degree_C_le

section ExactSequence

variable {M' M'' : Type*}
variable [AddCommGroup M'] [Module R M'] [Module.Finite R M']
variable [AddCommGroup M''] [Module R M''] [Module.Finite R M'']

private def quotientMap (I : Ideal R) (n : ℕ) (f : M' →ₗ[R] M) :
    (M' ⧸ I ^ n • (⊤ : Submodule R M')) →ₗ[R]
      (M ⧸ I ^ n • (⊤ : Submodule R M)) :=
  Submodule.mapQ _ _ f <| by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'', Submodule.map_top]
    exact smul_mono_right _ le_top

private lemma quotientMap_surjective (I : Ideal R) (n : ℕ) (f : M' →ₗ[R] M)
    (hf : Function.Surjective f) : Function.Surjective (quotientMap I n f) := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

private lemma quotientMap_exact (I : Ideal R) (n : ℕ)
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (quotientMap I n f) (quotientMap I n g) := by
  apply (Function.Exact.exact_mapQ_iff hfg _ _).2
  rw [LinearMap.range_eq_top.mpr hg, top_inf_eq, Submodule.map_smul'',
    Submodule.map_top, LinearMap.range_eq_top.mpr hg]

private lemma length_eq_ker_add_range (f : M' →ₗ[R] M) :
    Module.length R M' = Module.length R (LinearMap.ker f) + Module.length R (LinearMap.range f) := by
  let fr : M' →ₗ[R] LinearMap.range f := f.rangeRestrict
  have hker : LinearMap.ker fr = LinearMap.ker f := LinearMap.ker_rangeRestrict f
  have hexact : Function.Exact (LinearMap.ker f).subtype fr := by
    rw [LinearMap.exact_iff, Submodule.range_subtype, hker]
  simpa using Module.length_eq_add_of_exact (LinearMap.ker f).subtype fr
    (Submodule.subtype_injective _) (LinearMap.range_eq_top.mp f.range_rangeRestrict) hexact

private lemma length_eq_range_add_of_exact (I : Ideal R) (n : ℕ)
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Module.length R (M ⧸ I ^ n • (⊤ : Submodule R M)) =
      Module.length R (LinearMap.range (quotientMap I n f)) +
        Module.length R (M'' ⧸ I ^ n • (⊤ : Submodule R M'')) := by
  let fn := quotientMap I n f
  let gn := quotientMap I n g
  have hexact := quotientMap_exact I n f g hfg hg
  have hexact' : Function.Exact (LinearMap.range fn).subtype gn := by
    rw [LinearMap.exact_iff, Submodule.range_subtype, hexact.linearMap_ker_eq]
  exact Module.length_eq_add_of_exact _ _ (Submodule.subtype_injective _)
    (quotientMap_surjective I n g hg) hexact'

private lemma error_eq_neg_ker_length (I : Ideal R) (hI : I.IsIdealOfDefinition)
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hfg : Function.Exact f g) (hg : Function.Surjective g) (n : ℕ) :
    hilbertFunction I M n - hilbertFunction I M'' n - hilbertFunction I M' n =
      -(Module.length R (LinearMap.ker (quotientMap I n f))).toNat := by
  have hM := length_quotient_pow_ne_top (M := M) hI n
  have hM' := length_quotient_pow_ne_top (M := M') hI n
  have hM'' := length_quotient_pow_ne_top (M := M'') hI n
  have hrange : Module.length R (LinearMap.range (quotientMap I n f)) ≠ ⊤ := by
    exact ne_top_of_le_ne_top hM (Module.length_le_of_injective _ (Submodule.subtype_injective _))
  have hker : Module.length R (LinearMap.ker (quotientMap I n f)) ≠ ⊤ := by
    exact ne_top_of_le_ne_top hM'
      (Module.length_le_of_injective _ (Submodule.subtype_injective _))
  have hmiddle := length_eq_range_add_of_exact I n f g hfg hg
  have hleft := length_eq_ker_add_range (quotientMap I n f)
  have hmiddleNat := congrArg ENat.toNat hmiddle
  have hleftNat := congrArg ENat.toNat hleft
  rw [ENat.toNat_add hrange hM''] at hmiddleNat
  rw [ENat.toNat_add hker hrange] at hleftNat
  dsimp [hilbertFunction] at hmiddleNat hleftNat ⊢
  omega

private def transitionMap (I : Ideal R) {m n : ℕ} (h : m ≤ n) :
    (M' ⧸ I ^ n • (⊤ : Submodule R M')) →ₗ[R]
      (M' ⧸ I ^ m • (⊤ : Submodule R M')) :=
  Submodule.factor <| Submodule.smul_le.mpr fun _r hr _x hx ↦
    Submodule.smul_mem_smul (Ideal.pow_le_pow_right h hr) hx

private lemma transitionMap_surjective (I : Ideal R) {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (transitionMap (M' := M') I h) := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  exact ⟨Submodule.Quotient.mk y, rfl⟩

private lemma transitionMap_kernel_length (I : Ideal R) (hI : I.IsIdealOfDefinition)
    {m n : ℕ} (h : m ≤ n) :
    ((Module.length R (LinearMap.ker (transitionMap (M' := M') I h))).toNat : ℤ) =
      hilbertFunction I M' n - hilbertFunction I M' m := by
  let t := transitionMap (M' := M') I h
  have hexact : Function.Exact (LinearMap.ker t).subtype t :=
    LinearMap.exact_subtype_ker_map t
  have hlength := Module.length_eq_add_of_exact (LinearMap.ker t).subtype t
    (Submodule.subtype_injective _) (transitionMap_surjective (M' := M') I h) hexact
  have hn := length_quotient_pow_ne_top (M := M') hI n
  have hm := length_quotient_pow_ne_top (M := M') hI m
  have hker : Module.length R (LinearMap.ker t) ≠ ⊤ :=
    ne_top_of_le_ne_top hn
      (Module.length_le_of_injective _ (Submodule.subtype_injective _))
  have hlengthNat := congrArg ENat.toNat hlength
  rw [ENat.toNat_add hker hm] at hlengthNat
  dsimp [t, hilbertFunction] at hlengthNat ⊢
  omega

private lemma eventually_kernel_length_le_difference (I : Ideal R)
    (hI : I.IsIdealOfDefinition) (f : M' →ₗ[R] M) (hf : Function.Injective f) :
    ∃ c : ℕ, ∀ᶠ n : ℕ in atTop,
      ((Module.length R (LinearMap.ker (quotientMap I n f))).toNat : ℤ) ≤
        hilbertFunction I M' n - hilbertFunction I M' (n - c) := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range f)
  refine ⟨c, (eventually_ge_atTop c).mono fun n hn ↦ ?_⟩
  let t := transitionMap (M' := M') I (Nat.sub_le n c)
  have hcomap : Submodule.comap f (I ^ n • (⊤ : Submodule R M)) ≤
      I ^ (n - c) • (⊤ : Submodule R M') := by
    intro x hx
    have hxinf : f x ∈ I ^ n • (⊤ : Submodule R M) ⊓ LinearMap.range f :=
      ⟨hx, LinearMap.mem_range_self f x⟩
    rw [hc n hn] at hxinf
    have hxrange : f x ∈ I ^ (n - c) • LinearMap.range f :=
      (Submodule.smul_le.mpr fun r hr (y : M)
          (hy : y ∈ I ^ c • (⊤ : Submodule R M) ⊓ LinearMap.range f) ↦
        Submodule.smul_mem_smul hr hy.2) hxinf
    have hmap : Submodule.map f (I ^ (n - c) • (⊤ : Submodule R M')) =
        I ^ (n - c) • LinearMap.range f := by
      rw [Submodule.map_smul'', Submodule.map_top]
    rw [← hmap] at hxrange
    obtain ⟨y, hy, hfy⟩ := hxrange
    rw [hf hfy] at hy
    exact hy
  have hkerle : LinearMap.ker (quotientMap I n f) ≤ LinearMap.ker t := by
    dsimp only [t]
    rw [quotientMap, Submodule.ker_mapQ, transitionMap, Submodule.ker_mapQ]
    exact Submodule.map_mono hcomap
  have hlengthle :
      Module.length R (LinearMap.ker (quotientMap I n f)) ≤
        Module.length R (LinearMap.ker t) :=
    Module.length_le_of_injective (Submodule.inclusion hkerle)
      (Submodule.inclusion_injective hkerle)
  have ht_ne : Module.length R (LinearMap.ker t) ≠ ⊤ := by
    exact ne_top_of_le_ne_top (length_quotient_pow_ne_top (M := M') hI n)
      (Module.length_le_of_injective _ (Submodule.subtype_injective _))
  rw [← transitionMap_kernel_length (M' := M') I hI (Nat.sub_le n c)]
  exact_mod_cast ENat.toNat_le_toNat hlengthle ht_ne

private lemma eventually_abs_eval_error_le_difference (I : Ideal R)
    (hI : I.IsIdealOfDefinition) (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    {P' P P'' : ℚ[X]} (hP' : IsPolynomial I M' P') (hP : IsPolynomial I M P)
    (hP'' : IsPolynomial I M'' P'') :
    ∃ c : ℕ, ∀ᶠ n : ℕ in atTop,
      |(P - P'' - P').eval (n : ℚ)| ≤
        (P' - P'.taylor (-(c : ℚ))).eval (n : ℚ) := by
  obtain ⟨c, hkernel⟩ := eventually_kernel_length_le_difference I hI f hf
  refine ⟨c, ?_⟩
  have hP'shift := (tendsto_sub_atTop_nat c).eventually hP'
  filter_upwards [hP, hP'', hP', hP'shift, hkernel, eventually_ge_atTop c] with
      n hn hn'' hn' hn'shift hkernel hnc
  have hncast : (n : ℚ) + -(c : ℚ) = ((n - c : ℕ) : ℚ) := by
    rw [Nat.cast_sub hnc]
    ring
  have herrorQ :
      (hilbertFunction I M n : ℚ) - hilbertFunction I M'' n - hilbertFunction I M' n =
        -((Module.length R (LinearMap.ker (quotientMap I n f))).toNat : ℚ) := by
    exact_mod_cast error_eq_neg_ker_length I hI f g hfg hg n
  rw [Polynomial.eval_sub, Polynomial.eval_sub, hn, hn'', hn',
    herrorQ, abs_neg, abs_of_nonneg,
    Polynomial.eval_sub, Polynomial.taylor_eval, hncast, hn', hn'shift]
  · exact_mod_cast hkernel
  · positivity

/-- The filtered short-exact Hilbert--Samuel error has smaller degree than the
submodule polynomial when that module does not have finite length. -/
theorem filteredShortExact_error_degree_lt (I : Ideal R) (hI : I.IsIdealOfDefinition)
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'') (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    {P' P P'' : ℚ[X]} (hP' : IsPolynomial I M' P') (hP : IsPolynomial I M P)
    (hP'' : IsPolynomial I M'' P'') (hM' : ¬ IsFiniteLength R M') :
    (P - P'' - P').degree < P'.degree := by
  have hP'0 := hP'.ne_zero_of_not_isFiniteLength hI hM'
  obtain ⟨c, hbound⟩ :=
    eventually_abs_eval_error_le_difference I hI f g hf hfg hg hP' hP hP''
  let D := P' - P'.taylor (-(c : ℚ))
  have hDdegree : D.degree < P'.degree := by
    exact Polynomial.degree_sub_lt_left (Polynomial.degree_taylor P' (-(c : ℚ))).symm hP'0
      (Polynomial.leadingCoeff_taylor (-(c : ℚ)) P').symm
  by_cases hD0 : D = 0
  · have hEeval : ∀ᶠ n : ℕ in atTop, (P - P'' - P').eval (n : ℚ) = 0 := by
      filter_upwards [hbound] with n hn
      rw [show P' - P'.taylor (-(c : ℚ)) = D from rfl, hD0] at hn
      simp only [Polynomial.eval_zero] at hn
      exact abs_eq_zero.mp (le_antisymm hn (abs_nonneg _))
    have hEzero : P - P'' - P' = 0 :=
      NumericalPolynomial.EventuallyRepresents.unique hEeval (by
        simp [NumericalPolynomial.EventuallyRepresents])
    rw [hEzero, Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr (Polynomial.degree_ne_bot.mpr hP'0)
  · exact (NumericalPolynomial.degree_le_of_eventually_abs_eval_le hD0 hbound).trans_lt
      hDdegree

private lemma filteredShortExact_error_eq_zero_of_isFiniteLength
    (I : Ideal R) (hI : I.IsIdealOfDefinition)
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'') (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    {P' P P'' : ℚ[X]} (hP' : IsPolynomial I M' P') (hP : IsPolynomial I M P)
    (hP'' : IsPolynomial I M'' P'') (hM' : IsFiniteLength R M') :
    P - P'' - P' = 0 := by
  obtain ⟨c, hbound⟩ :=
    eventually_abs_eval_error_le_difference I hI f g hf hfg hg hP' hP hP''
  have hD0 : P' - P'.taylor (-(c : ℚ)) = 0 := by
    rw [hP'.eq_C_of_isFiniteLength hI hM']
    rw [Polynomial.taylor_C]
    ring
  have hEeval : ∀ᶠ n : ℕ in atTop, (P - P'' - P').eval (n : ℚ) = 0 := by
    filter_upwards [hbound] with n hn
    rw [hD0, Polynomial.eval_zero] at hn
    exact abs_eq_zero.mp (le_antisymm hn (abs_nonneg _))
  exact NumericalPolynomial.EventuallyRepresents.unique hEeval (by
    simp [NumericalPolynomial.EventuallyRepresents])

private lemma degree_add_eq_max_of_isPolynomial
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N]
    {I : Ideal R} {P Q : ℚ[X]} (hP : IsPolynomial I M P) (hQ : IsPolynomial I N Q) :
    (P + Q).degree = max P.degree Q.degree := by
  by_cases hP0 : P = 0
  · simp [hP0]
  by_cases hQ0 : Q = 0
  · simp [hQ0]
  exact Polynomial.degree_add_eq_of_leadingCoeff_add_ne_zero
    (ne_of_gt (add_pos (hP.leadingCoeff_pos hP0) (hQ.leadingCoeff_pos hQ0)))

/-- In a short exact sequence, the Hilbert--Samuel degree of the middle module
is the maximum of the two outer degrees, including zero and finite-length cases. -/
theorem filteredShortExact_degree_eq_max (I : Ideal R) (hI : I.IsIdealOfDefinition)
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'') (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    {P' P P'' : ℚ[X]} (hP' : IsPolynomial I M' P') (hP : IsPolynomial I M P)
    (hP'' : IsPolynomial I M'' P'') :
    P.degree = max P'.degree P''.degree := by
  have hsum : (P' + P'').degree = max P'.degree P''.degree :=
    degree_add_eq_max_of_isPolynomial hP' hP''
  by_cases hM' : IsFiniteLength R M'
  · have herror :=
      filteredShortExact_error_eq_zero_of_isFiniteLength I hI f g hf hfg hg hP' hP hP'' hM'
    have hpolynomial : P = P' + P'' := by linear_combination herror
    rw [hpolynomial, hsum]
  · have herror :=
      filteredShortExact_error_degree_lt I hI f g hf hfg hg hP' hP hP'' hM'
    have herror' : (P - P'' - P').degree < (P' + P'').degree := by
      rw [hsum]
      exact herror.trans_le (le_max_left _ _)
    have hpolynomial : P = (P' + P'') + (P - P'' - P') := by ring
    rw [hpolynomial, Polynomial.degree_add_eq_left_of_degree_lt herror', hsum]

/-- Multiplication by a regular element lowers Hilbert--Samuel degree after
passing to its cokernel. This is the form used in the prime-chain induction of
Stacks Project, tag 00KQ. -/
theorem quotient_degree_lt_of_isSMulRegular (I : Ideal R) (hI : I.IsIdealOfDefinition)
    (x : R) (hx : IsSMulRegular M x) {P Q : ℚ[X]}
    (hP : IsPolynomial I M P)
    (hQ : IsPolynomial I (M ⧸ x • (⊤ : Submodule R M)) Q)
    (hM : ¬ IsFiniteLength R M) : Q.degree < P.degree := by
  have hx' : Function.Injective (LinearMap.lsmul R M x) := by
    rw [LinearMap.lsmul_eq_distribSMultoLinearMap]
    exact hx
  have hdegree := filteredShortExact_error_degree_lt I hI
    (LinearMap.lsmul R M x) (x • (⊤ : Submodule R M)).mkQ hx'
    (LinearMap.exact_lsmul_mkQ_smul_top M x) (Submodule.mkQ_surjective _)
    hP hP hQ hM
  have herror : P - Q - P = -Q := by ring
  rw [herror, Polynomial.degree_neg] at hdegree
  exact hdegree

end ExactSequence

end


end HilbertSamuel
