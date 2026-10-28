module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Regular.Free
public import Mathlib.RingTheory.Smooth.Locus
public import Theory.AlgebraicGroup.CoordinateRing.CharZeroLocalSmooth

/-!
# Free Kahler differentials imply smoothness in characteristic zero

For a finite-type algebra over a characteristic-zero field, this module proves
that a free module of Kahler differentials forces smoothness.  This is the
generic commutative-algebra input used later for finite-type commutative Hopf
algebras; no Hopf structure is used here.

The local argument follows [Stacks Project, Lemma 10.140.7 (tag 00TX)].  At a
nonfield local ring, cotangent injectivity supplies an element `f` whose
differential admits a linear functional taking value one.  The corresponding
derivation and Krull intersection show that `f` is a nonzerodivisor.  The
conormal sequence for the quotient by `f` then splits one free summand from
the base-changed differential module, so induction applies to the quotient.
The principal quotient dimension formula lifts regularity back to the original
local ring.  Finally the localized differential basis and the
characteristic-zero regular-local criterion globalize the result through the
smooth locus, as in [Stacks Project, Lemma 33.25.1 (tag 04QN)].
-/

open IsLocalRing
open scoped TensorProduct

universe u v

namespace Theory.AlgebraicGroup

private theorem exists_linearMap_eq_one_of_one_tmul_ne_zero
    (R : Type v) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (x : M)
    (hx : (1 ⊗ₜ[R] x : ResidueField R ⊗[R] M) ≠ 0) :
    ∃ l : M →ₗ[R] R, l x = 1 := by
  let b := Module.finBasis R M
  have hi : ∃ i, residue R (b.repr x i) ≠ 0 := by
    by_contra! h
    apply hx
    apply (b.baseChange (ResidueField R)).repr.injective
    ext i
    rw [Module.Basis.baseChange_repr_tmul]
    simp [Algebra.smul_def, h]
  obtain ⟨i, hi⟩ := hi
  have hu : IsUnit (b.repr x i) := (residue_ne_zero_iff_isUnit _).mp hi
  let a : Rˣ := hu.unit
  let l : M →ₗ[R] R :=
    a⁻¹ • (Finsupp.lapply i).comp b.repr.toLinearMap
  refine ⟨l, ?_⟩
  change (↑(a⁻¹) : R) * b.repr x i = 1
  rw [← hu.unit_spec]
  exact Units.inv_mul _

private theorem isSMulRegular_of_derivation_eq_one
    (k : Type u) (R : Type v) [Field k] [CharZero k]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra k R]
    (D : Derivation k R R) (f : R) (hf : D f = 1) :
    IsSMulRegular R f := by
  by_cases hfu : IsUnit f
  · exact hfu.isSMulRegular R
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  intro a hfa
  have hpow : ∀ n : ℕ, a ∈ Ideal.span {f} ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n hn =>
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hn ⊢
      obtain ⟨b, rfl⟩ := hn
      have hzero : f ^ (n + 1) * b = 0 := by
        simpa [smul_eq_mul, pow_succ', mul_assoc] using hfa
      have hder := congrArg D hzero
      rw [map_zero, Derivation.leibniz] at hder
      have hder' :
          f ^ (n + 1) * D b + (n + 1 : R) * (f ^ n * b) = 0 := by
        simpa [Derivation.leibniz_pow, hf, smul_eq_mul, mul_comm, mul_left_comm,
          mul_assoc] using hder
      have hnunit : IsUnit (algebraMap k R (n + 1 : k)) :=
        (isUnit_iff_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero n)).map
          (algebraMap k R)
      let c : Rˣ := hnunit.unit
      have hc : (c : R) * (f ^ n * b) = -(f ^ (n + 1) * D b) := by
        rw [eq_neg_iff_add_eq_zero]
        simpa [c, IsUnit.unit_spec, add_comm, mul_comm, mul_left_comm, mul_assoc]
          using hder'
      refine ⟨-((c⁻¹ : Rˣ) : R) * D b, ?_⟩
      calc
        f ^ n * b = ((c⁻¹ : Rˣ) : R) * (c : R) * (f ^ n * b) := by simp
        _ = ((c⁻¹ : Rˣ) : R) * ((c : R) * (f ^ n * b)) := by ring
        _ = ((c⁻¹ : Rˣ) : R) * (-(f ^ (n + 1) * D b)) := by rw [hc]
        _ = f ^ (n + 1) * (-((c⁻¹ : Rˣ) : R) * D b) := by ring
  have ha : a ∈ ⨅ n : ℕ, Ideal.span {f} ^ n := by
    rw [Ideal.mem_iInf]
    exact hpow
  have hproper : Ideal.span {f} ≠ ⊤ := by
    simpa [Ideal.span_singleton_eq_top] using hfu
  have hi := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {f}) hproper
  have : a ∈ (⊥ : Ideal R) := hi ▸ ha
  simpa using this

set_option linter.style.haveILetI false in
private theorem spanFinrank_maximalIdeal_le_of_surjective_principal_kernel
    (R : Type v) {S : Type v} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (q : R →+* S) (hq_surj : Function.Surjective q) (f : R)
    (hf : f ∈ maximalIdeal R) (hker : RingHom.ker q = Ideal.span {f}) :
    (maximalIdeal R).spanFinrank ≤ (maximalIdeal S).spanFinrank + 1 := by
  letI : IsLocalHom q := IsLocalHom.of_surjective q hq_surj
  have hGfg : Submodule.FG (maximalIdeal S) := by
    obtain ⟨G, hG⟩ := (maximalIdeal S).fg_of_isNoetherianRing
    rw [← Ideal.submodule_span_eq] at hG
    exact Submodule.fg_def.mpr ⟨G, G.finite_toSet, hG⟩
  obtain ⟨G : Finset S, hGcard, hGspanSubmodule⟩ :=
    hGfg.exists_span_finset_card_eq_spanFinrank
  have hGspan : Ideal.span (G : Set S) = maximalIdeal S := by
    rw [← Ideal.submodule_span_eq]
    exact hGspanSubmodule
  have hGfinite : (G : Set S).Finite := G.finite_toSet
  let t : Set R := Function.surjInv hq_surj '' G
  have htfinite : t.Finite := hGfinite.image _
  have hqt : q '' t = (G : Set S) := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      rw [Function.surjInv_eq hq_surj z]
      exact hz
    · intro hx
      refine ⟨Function.surjInv hq_surj x, ⟨x, hx, rfl⟩, ?_⟩
      exact Function.surjInv_eq hq_surj x
  let J : Ideal R := Ideal.span t
  have hmapJ : J.map q = maximalIdeal S := by
    change (Ideal.span t).map q = maximalIdeal S
    rw [Ideal.map_span, hqt, hGspan]
  have htmax : t ⊆ maximalIdeal R := by
    rintro y ⟨z, hz, rfl⟩
    rw [← IsLocalRing.maximalIdeal_comap q]
    change q (Function.surjInv hq_surj z) ∈ maximalIdeal S
    rw [Function.surjInv_eq hq_surj z]
    rw [← hGspan]
    exact Ideal.subset_span hz
  have hspan : Ideal.span (insert f t) = maximalIdeal R := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro x (rfl | hx)
      · exact hf
      · exact htmax hx
    · intro x hx
      have hqx : q x ∈ J.map q := by
        rw [hmapJ]
        apply IsLocalRing.map_maximalIdeal_le q
        exact Ideal.mem_map_of_mem q hx
      rw [Ideal.mem_map_iff_of_surjective q hq_surj] at hqx
      obtain ⟨y, hyJ, hy⟩ := hqx
      have hxyI : x - y ∈ Ideal.span {f} := by
        rw [← hker, RingHom.mem_ker, map_sub, hy, sub_self]
      rw [← sub_add_cancel x y]
      apply Ideal.add_mem
      · exact (show Ideal.span {f} ≤ Ideal.span (insert f t) by
          exact Ideal.span_mono
            (Set.singleton_subset_iff.mpr (Set.mem_insert f t))) hxyI
      · exact (show J ≤ Ideal.span (insert f t) by
          change Ideal.span t ≤ Ideal.span (insert f t)
          exact Ideal.span_mono (Set.subset_insert f t)) hyJ
  rw [← hspan, ← Ideal.submodule_span_eq]
  refine (Submodule.spanFinrank_span_le_ncard_of_finite
    (htfinite.insert f)).trans ?_
  calc
    (insert f t).ncard ≤ t.ncard + 1 := Set.ncard_insert_le f t
    _ ≤ (G : Set S).ncard + 1 :=
      Nat.add_le_add_right (Set.ncard_image_le hGfinite) 1
    _ = G.card + 1 := by simp
    _ = (maximalIdeal S).spanFinrank + 1 := by rw [hGcard]

set_option linter.style.haveILetI false in
private theorem local_regular_of_free_kaehler_aux
    (k : Type u) (R : Type v) [Field k] [CharZero k]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra k R]
    [Algebra.EssFiniteType k R] [Module.Free R Ω[R⁄k]]
    (n : ℕ)
    (ih : ∀ (k' : Type u) (R' : Type v) [Field k'] [CharZero k']
      [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [Algebra k' R']
      [Algebra.EssFiniteType k' R'] [Module.Free R' Ω[R'⁄k']],
      Module.finrank R' Ω[R'⁄k'] < n → IsRegularLocalRing R')
    (hn : Module.finrank R Ω[R⁄k] = n) : IsRegularLocalRing R := by
  by_cases hfield : IsField R
  · let _ := hfield.toField
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [maximalIdeal_eq_bot, Submodule.spanFinrank_bot]
    simp
  have hcot_nontrivial : Nontrivial (CotangentSpace R) :=
    not_subsingleton_iff_nontrivial.mp <| by
      rwa [subsingleton_cotangentSpace_iff]
  let K := ResidueField R
  letI : Algebra.EssFiniteType k K := Algebra.EssFiniteType.comp k R K
  let fCot : CotangentSpace R →ₗ[R] K ⊗[R] Ω[R⁄k] :=
    (KaehlerDifferential.kerCotangentToTensor k R K).comp
      (Ideal.Cotangent.equivOfEq (maximalIdeal R)
        (RingHom.ker (algebraMap R K))
        (by rw [ResidueField.algebraMap_eq, ker_residue])).toLinearMap
  have hfCot_inj : Function.Injective fCot :=
    (charZero_local_cotangentToKaehler_injective k R).comp
      (Ideal.Cotangent.equivOfEq (maximalIdeal R)
        (RingHom.ker (algebraMap R K))
        (by rw [ResidueField.algebraMap_eq, ker_residue])).injective
  obtain ⟨x, hx⟩ := exists_ne (0 : CotangentSpace R)
  obtain ⟨f, rfl⟩ := (maximalIdeal R).toCotangent_surjective x
  have hdf :
      (1 ⊗ₜ[R] KaehlerDifferential.D k R f.1 : K ⊗[R] Ω[R⁄k]) ≠ 0 := by
    simpa [fCot] using fun h ↦ hx (hfCot_inj h)
  obtain ⟨l, hl⟩ := exists_linearMap_eq_one_of_one_tmul_ne_zero R Ω[R⁄k]
    (KaehlerDifferential.D k R f.1) hdf
  let D : Derivation k R R := (KaehlerDifferential.linearMapEquivDerivation k R) l
  have hDf : D f.1 = 1 := by simpa [D] using hl
  have hfreg : IsSMulRegular R f.1 :=
    isSMulRegular_of_derivation_eq_one k R D f.1 hDf
  have hf_nonunit : ¬ IsUnit f.1 :=
    (IsLocalRing.mem_maximalIdeal f.1).mp f.2
  let I : Ideal R := Ideal.span {f.1}
  have hI_ne : I ≠ ⊤ := by
    intro h
    exact hf_nonunit (Ideal.span_singleton_eq_top.mp
      (show Ideal.span {f.1} = ⊤ by simpa [I] using h))
  let S := R ⧸ I
  letI : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hI_ne
  letI : IsNoetherianRing S := inferInstance
  letI : IsLocalRing S := IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective
  letI : Algebra.EssFiniteType k S := inferInstance
  let N := S ⊗[R] Ω[R⁄k]
  let g : N →ₗ[S] Ω[S⁄k] := KaehlerDifferential.mapBaseChange k R S
  have hexact : Function.Exact
      (KaehlerDifferential.kerCotangentToTensor k R S) g := by
    intro y
    simpa [g] using
      (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k R S
        Ideal.Quotient.mk_surjective y)
  have hg_surj : Function.Surjective g :=
    KaehlerDifferential.mapBaseChange_surjective k R S
      Ideal.Quotient.mk_surjective
  letI : Module.Free S N := inferInstance
  letI : Module.Finite S N := inferInstance
  let v : N := 1 ⊗ₜ[R] KaehlerDifferential.D k R f.1
  let lS : N →ₗ[S] S :=
    (TensorProduct.isBaseChange R Ω[R⁄k] S).lift
      ((Algebra.linearMap R S).comp l)
  have hlS : lS v = 1 := by
    change ((TensorProduct.isBaseChange R Ω[R⁄k] S).lift
      ((Algebra.linearMap R S).comp l))
        ((TensorProduct.mk R S Ω[R⁄k]) 1
          (KaehlerDifferential.D k R f.1)) = 1
    rw [IsBaseChange.lift_eq]
    simpa using congrArg (algebraMap R S) hl
  have hgv : g v = 0 := by
    change KaehlerDifferential.mapBaseChange k R S
      (1 ⊗ₜ[R] KaehlerDifferential.D k R f.1) = 0
    rw [KaehlerDifferential.mapBaseChange_tmul, one_smul,
      KaehlerDifferential.map_D]
    change KaehlerDifferential.D k S (algebraMap R S f.1) = 0
    rw [show algebraMap R S f.1 = 0 by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_singleton f.1))]
    exact map_zero _
  have hker_g (x : N) (hx : g x = 0) : ∃ a : S, x = a • v := by
    obtain ⟨z, hz⟩ := (hexact x).mp hx
    obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective _ z
    have hyI : y.1 ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp y.2
    change y.1 ∈ Ideal.span {f.1} at hyI
    rw [Ideal.mem_span_singleton] at hyI
    obtain ⟨a, ha⟩ := hyI
    have hfa : f.1 * a ∈ RingHom.ker (algebraMap R S) := by
      rw [RingHom.mem_ker, map_mul]
      rw [show algebraMap R S f.1 = 0 by
        exact Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span (Set.mem_singleton f.1))]
      exact zero_mul _
    have hy_eq : y = ⟨f.1 * a, hfa⟩ := Subtype.ext ha
    rw [hy_eq] at hz
    refine ⟨algebraMap R S a, ?_⟩
    rw [← hz]
    simp only [KaehlerDifferential.kerCotangentToTensor_toCotangent,
      Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one]
    rw [show algebraMap R S f.1 = 0 by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_singleton f.1))]
    simpa [v, Algebra.smul_def] using
      (TensorProduct.smul_tmul' (R := R) (R' := R) a (1 : S)
        (KaehlerDifferential.D k R f.1)).symm
  let p : N →ₗ[S] lS.ker :=
    LinearMap.codRestrict lS.ker (LinearMap.id -
      (LinearMap.toSpanSingleton S N v).comp lS) (fun x ↦ by
        simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
          LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, map_sub,
          map_smul, hlS, smul_eq_mul, mul_one, sub_self])
  have hp_subtype (x : N) : (p x : N) = x - lS x • v := rfl
  have hp_retract : p.comp lS.ker.subtype = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (p (x : N) : N) = x
    simp [hp_subtype]
  letI : Module.Finite S lS.ker := inferInstance
  letI : Module.Projective S lS.ker :=
    Module.Projective.of_split lS.ker.subtype p hp_retract
  letI : Module.Flat S lS.ker := Module.Flat.of_projective
  letI : Module.Free S lS.ker :=
    @Module.free_of_flat_of_isLocalRing S lS.ker _ _ _ _
      inferInstance inferInstance
  let decomp : N →ₗ[S] S × lS.ker := lS.prod p
  have hdecomp_bij : Function.Bijective decomp := by
    constructor
    · intro x y hxy
      have h₁ := congrArg Prod.fst hxy
      have h₂ := congrArg (fun z : S × lS.ker ↦ (z.2 : N)) hxy
      change lS x = lS y at h₁
      change (p x : N) = (p y : N) at h₂
      rw [hp_subtype, hp_subtype, h₁] at h₂
      exact sub_left_injective h₂
    · rintro ⟨a, x⟩
      refine ⟨a • v + x.1, ?_⟩
      apply Prod.ext
      · simp [decomp, hlS]
      · apply Subtype.ext
        simp [decomp, hp_subtype, hlS]
  let eN : N ≃ₗ[S] S × lS.ker :=
    LinearEquiv.ofBijective decomp hdecomp_bij
  let gKer : lS.ker →ₗ[S] Ω[S⁄k] := g.domRestrict lS.ker
  have hgKer_bij : Function.Bijective gKer := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      have hgsub : g (x.1 - y.1) = 0 := by
        simpa [gKer] using sub_eq_zero.mpr hxy
      obtain ⟨a, ha⟩ := hker_g (x.1 - y.1) hgsub
      have hla : a = 0 := by
        have h := congrArg lS ha
        exact (by simpa [x.2, y.2, hlS] using h : 0 = a).symm
      exact sub_eq_zero.mp (by simpa [hla] using ha)
    · intro y
      obtain ⟨x, hx⟩ := hg_surj y
      refine ⟨p x, ?_⟩
      simpa [gKer, hp_subtype, hgv] using hx
  let eKer : lS.ker ≃ₗ[S] Ω[S⁄k] :=
    LinearEquiv.ofBijective gKer hgKer_bij
  letI : Module.Finite S Ω[S⁄k] := Module.Finite.equiv eKer
  letI : Module.Free S Ω[S⁄k] := Module.Free.of_equiv eKer
  have hltN : Module.finrank S Ω[S⁄k] < Module.finrank S N := by
    rw [← eKer.finrank_eq, eN.finrank_eq, Module.finrank_prod,
      Module.finrank_self]
    omega
  have hlt : Module.finrank S Ω[S⁄k] < n := by
    rwa [Module.finrank_baseChange, hn] at hltN
  have hregS : IsRegularLocalRing S := ih k S hlt
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc
    (↑(maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤
        ↑((maximalIdeal S).spanFinrank + 1) := by
      exact_mod_cast
        spanFinrank_maximalIdeal_le_of_surjective_principal_kernel
          R (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective f.1 f.2
          (by simp [I])
    _ = (↑(maximalIdeal S).spanFinrank : WithBot ℕ∞) + 1 := by simp
    _ = ringKrullDim S + 1 := by rw [hregS.spanFinrank_maximalIdeal]
    _ = ringKrullDim R :=
      ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hfreg f.2

private theorem local_regular_of_free_kaehler_rank (n : ℕ) :
    ∀ (k : Type u) (R : Type v) [Field k] [CharZero k]
      [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra k R]
      [Algebra.EssFiniteType k R] [Module.Free R Ω[R⁄k]],
      Module.finrank R Ω[R⁄k] = n → IsRegularLocalRing R := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro k R _ _ _ _ _ _ _ _ hn
      exact local_regular_of_free_kaehler_aux k R n
        (fun k' R' _ _ _ _ _ _ _ _ hlt ↦ ih _ hlt k' R' rfl) hn

private theorem local_regular_of_free_kaehler
    (k : Type u) (R : Type v) [Field k] [CharZero k]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra k R]
    [Algebra.EssFiniteType k R] [Module.Free R Ω[R⁄k]] :
    IsRegularLocalRing R :=
  local_regular_of_free_kaehler_rank (Module.finrank R Ω[R⁄k]) k R rfl

set_option linter.style.haveILetI false in
/-- A finite-type algebra over a characteristic-zero field is smooth when its
module of Kahler differentials is free.  This is Stacks Project tag 00TX,
globalized through tag 04QN. -/
public theorem finiteType_charZero_smooth_of_kaehlerDifferential_free
    (k : Type u) (A : Type v) [Field k] [CharZero k]
    [CommRing A] [Nontrivial A] [Algebra k A]
    [Algebra.FiniteType k A] [Module.Free A Ω[A⁄k]] :
    Algebra.Smooth k A := by
  letI : Algebra.FinitePresentation k A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  refine ⟨?_, inferInstance⟩
  rw [← Algebra.smoothLocus_eq_univ_iff]
  apply Set.eq_univ_of_forall
  intro q
  apply finiteType_charZero_isSmoothAt_of_regularLocal k A q.asIdeal
  let R := Localization.AtPrime q.asIdeal
  letI : Algebra.EssFiniteType k R := inferInstance
  letI : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing k R
  let e : LocalizedModule q.asIdeal.primeCompl Ω[A⁄k] ≃ₗ[R] Ω[R⁄k] := by
    have eLoc := IsLocalizedModule.iso q.asIdeal.primeCompl
      (KaehlerDifferential.map k k A R)
    exact eLoc.extendScalarsOfIsLocalization q.asIdeal.primeCompl R
  let b := Module.Free.chooseBasis A Ω[A⁄k]
  let bLoc := b.ofIsLocalizedModule R q.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap q.asIdeal.primeCompl Ω[A⁄k])
  letI : Module.Free R (LocalizedModule q.asIdeal.primeCompl Ω[A⁄k]) :=
    Module.Free.of_basis bLoc
  letI : Module.Free R Ω[R⁄k] := Module.Free.of_equiv e
  exact local_regular_of_free_kaehler k R

end Theory.AlgebraicGroup
