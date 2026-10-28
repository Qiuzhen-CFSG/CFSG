module

public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.ZariskisMainTheorem
public import Theory.AlgebraicGroup.Dimension.Finite
public import Theory.AlgebraicGroup.Dimension.Isomorphism
public import Theory.AlgebraicGroup.Dimension.Strict
public import Theory.AlgebraicGroup.Morphism.ClosedImage

universe u

/-!
Fibers, finite-fiber dominance, and the kernel-image dimension formula for
algebraic-group morphisms.

For a morphism between irreducible affine varieties of equal dimension, finite
rational-point fibers force the pullback on polynomial functions to be
injective.  The proof compares maximal-ideal heights after factoring out the
pullback kernel; the zero-dimensional fiber bounds the relative height.  This
gives the dominance criterion used for the Lang morphism.  The remainder of
the module proves the kernel-image dimension formula for algebraic-group
morphisms (Proposition 1.1.6(e)).
-/

open scoped nonZeroDivisors
open Cardinal Topology
namespace Theory.AlgebraicGroup

section

lemma mvPolynomial_ker_eval_eq_span_X_sub_C
    {R : Type u} [CommRing R] {ι : Type u} (c : ι → R) :
    RingHom.ker (MvPolynomial.eval c) =
      Ideal.span (Set.range fun i : ι => MvPolynomial.X i - MvPolynomial.C (c i)) := by
  let I : Ideal (MvPolynomial ι R) :=
    Ideal.span (Set.range fun i : ι => MvPolynomial.X i - MvPolynomial.C (c i))
  apply le_antisymm
  · intro p hp
    rw [RingHom.mem_ker] at hp
    have hhom : Ideal.Quotient.mk I =
        (algebraMap R (MvPolynomial ι R ⧸ I)).comp (MvPolynomial.eval c) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simpa [RingHom.comp_apply] using Ideal.Quotient.mk_algebraMap R I r
      · intro i
        apply Ideal.Quotient.eq.mpr
        rw [MvPolynomial.eval_X]
        change MvPolynomial.X i - MvPolynomial.C (c i) ∈ I
        exact Ideal.subset_span ⟨i, rfl⟩
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [hhom, RingHom.comp_apply, hp, map_zero]
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp

lemma mvPolynomial_ker_eval₂Hom_le_map_ker_sup_span
    {R S : Type u} [CommRing R] [CommRing S]
    {ι : Type u} (β : R →+* S) (r : ι → R) :
    RingHom.ker (MvPolynomial.eval₂Hom β (fun i => β (r i))) ≤
      Ideal.map (MvPolynomial.C : R →+* MvPolynomial ι R) (RingHom.ker β) ⊔
        Ideal.span (Set.range fun i : ι =>
          MvPolynomial.X i - MvPolynomial.C (r i)) := by
  intro p hp
  let ev : MvPolynomial ι R →+* R := MvPolynomial.eval r
  have hcomp : MvPolynomial.eval₂Hom β (fun i => β (r i)) = β.comp ev := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ev]
    · intro i
      simp [ev]
  have hβ : ev p ∈ RingHom.ker β := by
    rw [RingHom.mem_ker] at hp ⊢
    rw [hcomp, RingHom.comp_apply] at hp
    exact hp
  have hdiff : p - MvPolynomial.C (ev p) ∈
      Ideal.span (Set.range fun i : ι =>
        MvPolynomial.X i - MvPolynomial.C (r i)) := by
    rw [← mvPolynomial_ker_eval_eq_span_X_sub_C r, RingHom.mem_ker]
    simp [ev]
  rw [show p = (p - MvPolynomial.C (ev p)) + MvPolynomial.C (ev p) by ring]
  apply Ideal.add_mem
  · exact (show Ideal.span (Set.range fun i : ι =>
        MvPolynomial.X i - MvPolynomial.C (r i)) ≤ _ from le_sup_right) hdiff
  · exact (show Ideal.map (MvPolynomial.C : R →+* MvPolynomial ι R)
        (RingHom.ker β) ≤ _ from le_sup_left)
      (Ideal.mem_map_of_mem (MvPolynomial.C : R →+* MvPolynomial ι R) hβ)

lemma under_adjoin_eq_of_under_eq_of_sub_mem
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type u} {x : ι → A} (hx : AlgebraicIndependent R x)
    {P Q : Ideal A} [P.IsPrime] [Q.IsPrime] (hQP : Q ≤ P)
    (hunder : Q.under R = P.under R) (r : ι → R)
    (hxr : ∀ i, x i - algebraMap R A (r i) ∈ Q) :
    let C := Algebra.adjoin R (Set.range x)
    Q.under C = P.under C := by
  dsimp only
  let C := Algebra.adjoin R (Set.range x)
  let e : MvPolynomial ι R ≃ₐ[R] C := hx.aevalEquiv
  apply le_antisymm
  · exact Ideal.comap_mono hQP
  · intro c hcP
    let p : MvPolynomial ι R := e.symm c
    have hep : e p = c := e.apply_symm_apply c
    let β : R →+* A ⧸ P :=
      (Ideal.Quotient.mk P).comp (algebraMap R A)
    let ev : MvPolynomial ι R →+* A ⧸ P :=
      MvPolynomial.eval₂Hom β (fun i => β (r i))
    have heval (p : MvPolynomial ι R) :
        algebraMap C A (e p) = MvPolynomial.aeval x p := by
      change algebraMap (Algebra.adjoin R (Set.range x)) A
        (hx.aevalEquiv p) = MvPolynomial.aeval x p
      exact hx.algebraMap_aevalEquiv p
    have heval' (p : MvPolynomial ι R) :
        algebraMap C A (e.toRingEquiv.toRingHom p) =
          MvPolynomial.aeval x p := by
      exact heval p
    have hhom : ev = (Ideal.Quotient.mk P).comp
        ((algebraMap C A).comp e.toRingHom) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp only [ev, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
        rw [heval']
        simp [β]
      · intro i
        simp only [ev, MvPolynomial.eval₂Hom_X', RingHom.comp_apply]
        rw [heval']
        rw [MvPolynomial.aeval_X]
        change Ideal.Quotient.mk P (algebraMap R A (r i)) =
          Ideal.Quotient.mk P (x i)
        apply Ideal.Quotient.eq.mpr
        simpa only [neg_sub] using P.neg_mem (hQP (hxr i))
    have hpker : p ∈ RingHom.ker ev := by
      rw [RingHom.mem_ker, hhom, RingHom.comp_apply, RingHom.comp_apply]
      change Ideal.Quotient.mk P (algebraMap C A (e p)) = 0
      rw [hep]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hcP
    have hp := mvPolynomial_ker_eval₂Hom_le_map_ker_sup_span β r hpker
    have hconst : Ideal.map e.toRingHom
        (Ideal.map (MvPolynomial.C : R →+* MvPolynomial ι R)
          (RingHom.ker β)) ≤ Q.under C := by
      apply Ideal.map_le_iff_le_comap.mpr
      apply Ideal.map_le_iff_le_comap.mpr
      intro a ha
      change algebraMap C A (e (MvPolynomial.C a)) ∈ Q
      rw [heval]
      have haP : a ∈ P.under R := by
        change algebraMap R A a ∈ P
        change Ideal.Quotient.mk P (algebraMap R A a) = 0 at ha
        exact Ideal.Quotient.eq_zero_iff_mem.mp ha
      have haQ : a ∈ Q.under R := by
        rw [hunder]
        exact haP
      simpa using haQ
    have hvars : Ideal.map e.toRingHom
        (Ideal.span (Set.range fun i : ι =>
          MvPolynomial.X i - MvPolynomial.C (r i))) ≤ Q.under C := by
      apply Ideal.map_le_iff_le_comap.mpr
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      change algebraMap C A
        (e (MvPolynomial.X i - MvPolynomial.C (r i))) ∈ Q
      rw [heval]
      simpa using hxr i
    have hemap : Ideal.map e.toRingHom
        (Ideal.map (MvPolynomial.C : R →+* MvPolynomial ι R)
            (RingHom.ker β) ⊔
          Ideal.span (Set.range fun i : ι =>
            MvPolynomial.X i - MvPolynomial.C (r i))) ≤ Q.under C := by
      rw [Ideal.map_sup]
      exact sup_le hconst hvars
    have : e p ∈ Q.under C := hemap (Ideal.mem_map_of_mem e.toRingHom hp)
    rwa [hep] at this

lemma exists_finite_isTranscendenceBasis_subset
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsDomain A] [FaithfulSMul R A] [Algebra.FiniteType R A] :
    ∃ t : Set A, t.Finite ∧ IsTranscendenceBasis R ((↑) : t → A) := by
  have hfg : (⊤ : Subalgebra R A).FG := Algebra.FiniteType.out
  rcases Subalgebra.fg_def.mp hfg with ⟨s, hsfin, hs⟩
  let : Algebra.IsAlgebraic (Algebra.adjoin R s) A := by
    constructor
    intro a
    let a' : Algebra.adjoin R s := ⟨a, by rw [hs]; trivial⟩
    have ha : algebraMap (Algebra.adjoin R s) A a' = a := rfl
    rw [← ha]
    exact isAlgebraic_algebraMap a'
  obtain ⟨t, hts, htb⟩ := exists_isTranscendenceBasis_subset (R := R) (A := A) s
  exact ⟨t, hsfin.subset hts, htb⟩

lemma height_le_of_minimalPrimes_quotient_height_le
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {p : Ideal R} [p.IsPrime] {n : ℕ∞}
    (h : ∀ q ∈ minimalPrimes R, q ≤ p →
      (p.map (Ideal.Quotient.mk q)).height ≤ n) :
    p.height ≤ n := by
  rw [show p.height = Order.height (⟨p, inferInstance⟩ : PrimeSpectrum R) from
    PrimeSpectrum.height_eq_orderHeight (⟨p, inferInstance⟩ : PrimeSpectrum R)]
  apply Order.height_le
  intro l hl
  have hlastideal : l.last.asIdeal = p := congrArg PrimeSpectrum.asIdeal hl
  have hhead : l.head.asIdeal ≤ p := by
    rw [← hlastideal]
    exact l.head_le_last
  obtain ⟨q, hqmin0, hqhead⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R))
      (J := l.head.asIdeal) bot_le
  have hqmin : q ∈ minimalPrimes R := by simpa using hqmin0
  let π : R →+* R ⧸ q := Ideal.Quotient.mk q
  have hqle (i : Fin (l.length + 1)) : q ≤ (l i).asIdeal :=
    hqhead.trans (l.head_le i)
  let f : Fin (l.length + 1) → PrimeSpectrum (R ⧸ q) := fun i =>
    ⟨(l i).asIdeal.map π,
      Ideal.isPrime_map_quotientMk_of_isPrime (hqle i)⟩
  have hf : StrictMono f := by
    intro i j hij
    have hij' : (l i).asIdeal < (l j).asIdeal := l.strictMono hij
    apply lt_of_le_of_ne (Ideal.map_mono hij'.le)
    intro heq
    have hcomap := congrArg (Ideal.comap π) heq
    have hker : Ideal.comap π ⊥ = q := by
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    rw [Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective,
      Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective,
      hker, sup_eq_left.mpr (hqle i),
      sup_eq_left.mpr (hqle j)] at hcomap
    exact hij'.ne hcomap
  let l' : LTSeries (PrimeSpectrum (R ⧸ q)) := LTSeries.mk l.length f hf
  have hlast : l'.last.asIdeal = p.map π := by
    change l.last.asIdeal.map π = p.map π
    rw [hlastideal]
  have hlen : (l.length : ℕ∞) ≤ (p.map π).height := by
    rw [← hlast, PrimeSpectrum.height_eq_orderHeight]
    exact Order.length_le_height_last
  exact hlen.trans (h q hqmin (hqhead.trans hhead))

lemma quasiFiniteAt_of_fg_and_awayMap_bijective
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (S' : Subalgebra R S) (hS' : S'.toSubmodule.FG) (r : S')
    {p : Ideal S} [p.IsPrime] (hrp : r.1 ∉ p)
    (H : Function.Bijective (Localization.awayMap S'.val.toRingHom r)) :
    Algebra.QuasiFiniteAt R p := by
  have : Module.Finite R S' := ⟨(Submodule.fg_top _).mpr hS'⟩
  have : Algebra.QuasiFinite R (Localization.Away r) :=
    .trans R S' _
  have : Algebra.QuasiFinite R (Localization.Away r.1) :=
    .of_surjective_algHom (Localization.awayMapₐ S'.val r) H.2
  let f : Localization.Away r.1 →ₐ[S] Localization.AtPrime p :=
    IsLocalization.Away.liftAlgHom r.1 (f := Algebra.ofId _ _) <|
      IsLocalization.map_units (M := p.primeCompl)
        (Localization.AtPrime p) ⟨r, hrp⟩
  refine .of_forall_exists_mul_mem_range (f.restrictScalars R) fun x ↦ ?_
  obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
  exact ⟨algebraMap _ _ s,
    by simpa using IsLocalization.map_units _ ⟨s, hs⟩,
    algebraMap _ _ x, by simp⟩

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
lemma mvPolynomial_maximal_height (n : ℕ)
    (m : Ideal (MvPolynomial (Fin n) k)) [m.IsMaximal] :
    m.height = n := by
  induction n with
  | zero =>
      let e := MvPolynomial.isEmptyRingEquiv k (Fin 0)
      have hm : (m.map e).IsMaximal := inferInstance
      have hbot : m.map e = (⊥ : Ideal k) :=
        (Ideal.bot_isMaximal.eq_of_le hm.ne_top bot_le).symm
      rw [← e.height_map m, hbot, Ideal.height_bot]
      rfl
  | succ n ih =>
      let e := MvPolynomial.finSuccEquiv k n
      let M : Ideal (Polynomial (MvPolynomial (Fin n) k)) := m.map e
      have hM : M.IsMaximal := inferInstance
      let p : Ideal (MvPolynomial (Fin n) k) := M.comap Polynomial.C
      have hp : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing M
      have hover : M.LiesOver p := ⟨rfl⟩
      rw [← e.height_map m]
      change M.height = ↑(n + 1)
      rw [Polynomial.height_eq_height_add_one p M, ih p]
      simp

omit [IsAlgClosed k] in
public lemma domain_maximal_height_eq_trdeg
    (A : Type u) [CommRing A] [Algebra k A] [IsDomain A]
    [Algebra.FiniteType k A]
    (m : Ideal A) [m.IsMaximal] :
    m.height = Cardinal.toNat (Algebra.trdeg k A) := by
  obtain ⟨n, g, hg, hgint⟩ := exists_integral_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin n) k
  let : Algebra P A := g.toRingHom.toAlgebra
  have : FaithfulSMul P A :=
    (faithfulSMul_iff_algebraMap_injective (R := P) (A := A)).mpr hg
  have : Algebra.IsIntegral P A := ⟨hgint⟩
  let p : Ideal P := m.comap (algebraMap P A)
  have hp : p.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
  have hover : m.LiesOver p := ⟨rfl⟩
  have hmin : m ∈ (p.map (algebraMap P A)).minimalPrimes :=
    Ideal.IsIntegral.mem_minimalPrimes_map_under m
  have hqmin : m.map (Ideal.Quotient.mk (p.map (algebraMap P A))) ∈
      minimalPrimes (A ⧸ p.map (algebraMap P A)) := by
    rw [@Ideal.minimalPrimes_eq_comap A _
      (p.map (algebraMap P A))] at hmin
    rcases hmin with ⟨q, hq, hqm⟩
    have heq : q = m.map
        (Ideal.Quotient.mk (p.map (algebraMap P A))) := by
      apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
      rw [hqm, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
      symm
      apply sup_eq_left.mpr
      have hI : p.map (algebraMap P A) ≤ m :=
        Ideal.map_le_iff_le_comap.mpr le_rfl
      change RingHom.ker
          (Ideal.Quotient.mk (p.map (algebraMap P A))) ≤ m
      rwa [Ideal.mk_ker]
    simpa [heq] using hq
  have hheight : m.height = p.height := by
    let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
    let : IsIntegrallyClosed P := by
      dsimp [P]
      infer_instance
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p m,
      Ideal.height_eq_zero_iff.mpr hqmin, add_zero]
  have hpheight : p.height = n := mvPolynomial_maximal_height n p
  rw [hheight, hpheight]
  have htr : Algebra.trdeg k A = n := by
    have hP : Algebra.trdeg k P = n := by simp [P]
    have hrel : Algebra.trdeg P A = 0 :=
      trdeg_eq_zero (R := P) (A := A)
    have htower := trdeg_add_eq (R := k) (S := P) (A := A)
    rw [hrel, add_zero, hP] at htower
    exact htower.symm
  rw [htr]
  simp

def polynomialFunctionIdealZeroSet (V : Variety k)
    (I : Ideal (Variety.PolynomialFunction V)) : Set (Variety.Point V) :=
  {x | ∀ f ∈ I, f x = 0}

omit [IsAlgClosed k] in
lemma polynomialFunctionIdealZeroSet_isZariskiClosed (V : Variety k)
    (I : Ideal (Variety.PolynomialFunction V)) :
    IsZariskiClosed V (polynomialFunctionIdealZeroSet V I) := by
  let e := evaluationRingHom (V := V)
  refine ⟨I.comap e, ?_⟩
  ext x
  constructor
  · intro hx p hp
    exact hx (e p) hp
  · intro hx f hf
    obtain ⟨p, rfl⟩ := evaluationRingHom_surjective V f
    exact hx p hf

lemma vanishingIdeal_polynomialFunctionIdealZeroSet_of_isPrime
    (V : Variety k) (I : Ideal (Variety.PolynomialFunction V)) [I.IsPrime] :
    vanishingIdeal (polynomialFunctionIdealZeroSet V I) =
      I.comap (evaluationRingHom (V := V)) := by
  let A := Variety.PolynomialFunction V
  let : Algebra.FiniteType k (Variety.PolynomialFunction V) :=
    polynomialFunction_finiteType V
  let : IsJacobsonRing (Variety.PolynomialFunction V) :=
    isJacobsonRing_of_finiteType (A := k)
  apply le_antisymm
  · intro p hp
    change evaluationRingHom (V := V) p ∈ I
    have hjac : evaluationRingHom (V := V) p ∈ I.jacobson := by
      rw [Ideal.jacobson, Ideal.mem_sInf]
      intro m hm
      rcases hm with ⟨hIm, hmmax⟩
      obtain ⟨x, hx⟩ := V.exists_pointPrime_eq_of_isMaximal m hmmax
      have hxzero : x ∈ polynomialFunctionIdealZeroSet V I := by
        intro f hf
        have hfm : f ∈ m := hIm hf
        have hmx : m = (V.pointPrime x).asIdeal :=
          (congrArg PrimeSpectrum.asIdeal hx).symm
        rw [hmx] at hfm
        simpa [Variety.pointPrime] using hfm
      have hpzero := hp x hxzero
      have hpmem : evaluationRingHom (V := V) p ∈
          (V.pointPrime x).asIdeal := by
        change evalPolynomial x.val p = 0
        exact hpzero
      rw [congrArg PrimeSpectrum.asIdeal hx] at hpmem
      exact hpmem
    have hrad : evaluationRingHom (V := V) p ∈ I.radical := by
      rw [Ideal.radical_eq_jacobson]
      exact hjac
    rw [show I.radical = I from (inferInstance : I.IsPrime).radical] at hrad
    exact hrad
  · intro p hp x hx
    exact hx (evaluationRingHom (V := V) p) hp

noncomputable def polynomialFunctionIdealQuotientAlgEquiv
    (V : Variety k) (I : Ideal (Variety.PolynomialFunction V)) :
    (MvPolynomial V.Coordinates k ⧸
        I.comap (evaluationRingHom (V := V))) ≃ₐ[k]
      Variety.PolynomialFunction V ⧸ I := by
  let e : MvPolynomial V.Coordinates k →ₐ[k]
      Variety.PolynomialFunction V :=
    { toRingHom := evaluationRingHom (V := V)
      commutes' := by
        intro r
        apply Variety.PolynomialFunction.ext
        intro x
        change evalPolynomial x.val (MvPolynomial.C r) =
          (algebraMap k (Variety.PolynomialFunction V) r) x
        rw [polynomialFunction_algebraMap_apply]
        simp [evalPolynomial] }
  let f : MvPolynomial V.Coordinates k →ₐ[k]
      Variety.PolynomialFunction V ⧸ I :=
    (Ideal.Quotient.mkₐ k I).comp e
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨p, rfl⟩ := evaluationRingHom_surjective V a
    exact ⟨p, rfl⟩
  have hker : I.comap (evaluationRingHom (V := V)) = RingHom.ker f := by
    ext p
    change evaluationRingHom (V := V) p ∈ I ↔
      Ideal.Quotient.mk I (evaluationRingHom (V := V) p) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.symm
  exact (Ideal.quotientEquivAlgOfEq k hker).trans
    (Ideal.quotientKerAlgEquivOfSurjective hf)

def polynomialFunctionVanishingIdeal (V : Variety k)
    (S : Set (Variety.Point V)) : Ideal (Variety.PolynomialFunction V) where
  carrier := {f | ∀ x ∈ S, f x = 0}
  zero_mem' := by
    intro x hx
    change (0 : k) = 0
    rfl
  add_mem' := by
    intro f g hf hg x hx
    change f x + g x = 0
    rw [hf x hx, hg x hx, add_zero]
  smul_mem' := by
    intro f g hg x hx
    change f x * g x = 0
    rw [hg x hx, mul_zero]

omit [IsAlgClosed k] in
lemma mem_polynomialFunctionVanishingIdeal_iff (V : Variety k)
    (S : Set (Variety.Point V)) (f : Variety.PolynomialFunction V) :
    f ∈ polynomialFunctionVanishingIdeal V S ↔ ∀ x ∈ S, f x = 0 := Iff.rfl

omit [IsAlgClosed k] in
lemma polynomialFunctionVanishingIdeal_comap_evaluationRingHom
    (V : Variety k) (S : Set (Variety.Point V)) :
    (polynomialFunctionVanishingIdeal V S).comap
        (evaluationRingHom (V := V)) = vanishingIdeal S := by
  rfl

omit [IsAlgClosed k] in
lemma polynomialFunctionIdealZeroSet_vanishingIdeal
    (V : Variety k) {S : Set (Variety.Point V)} (hS : IsZariskiClosed V S) :
    polynomialFunctionIdealZeroSet V
      (polynomialFunctionVanishingIdeal V S) = S := by
  ext x
  constructor
  · intro hx
    have hxzero : x ∈ {x : Variety.Point V |
        ∀ p ∈ vanishingIdeal S, evalPolynomial x.val p = 0} := by
      intro p hp
      apply hx (evaluationRingHom (V := V) p)
      exact hp
    exact zeroLocus_vanishingIdeal hS ▸ hxzero
  · intro hx f hf
    exact hf x hx

omit [IsAlgClosed k] in
lemma polynomialFunctionVanishingIdeal_isPrime_of_isIrreducible
    (V : Variety k) {S : Set (Variety.Point V)}
    (hS : IsZariskiClosed V S) (hSi : IsIrreducible S) :
    (polynomialFunctionVanishingIdeal V S).IsPrime := by
  let e := evaluationRingHom (V := V)
  let P := polynomialFunctionVanishingIdeal V S
  have hcomap : P.comap e = vanishingIdeal S :=
    polynomialFunctionVanishingIdeal_comap_evaluationRingHom V S
  have hprime : (P.comap e).IsPrime := by
    rw [hcomap]
    exact isPrime_vanishingIdeal_of_isIrreducible_set hS hSi
  let : (P.comap e).IsPrime := hprime
  have hker : RingHom.ker e ≤ P.comap e := by
    intro p hp
    change e p ∈ P
    rw [RingHom.mem_ker] at hp
    rw [hp]
    exact P.zero_mem
  have hmap : (P.comap e).map e = P :=
    Ideal.map_comap_of_surjective e (evaluationRingHom_surjective V) P
  change P.IsPrime
  rw [← hmap]
  exact Ideal.map_isPrime_of_surjective (evaluationRingHom_surjective V) hker

lemma polynomialFunctionVanishingIdeal_idealZeroSet_of_isPrime
    (V : Variety k) (I : Ideal (Variety.PolynomialFunction V)) [I.IsPrime] :
    polynomialFunctionVanishingIdeal V
      (polynomialFunctionIdealZeroSet V I) = I := by
  let Z := polynomialFunctionIdealZeroSet V I
  let hZ := polynomialFunctionIdealZeroSet_isZariskiClosed V I
  apply Ideal.comap_injective_of_surjective
    (evaluationRingHom (V := V)) (evaluationRingHom_surjective V)
  rw [polynomialFunctionVanishingIdeal_comap_evaluationRingHom,
    vanishingIdeal_polynomialFunctionIdealZeroSet_of_isPrime]

lemma polynomialFunctionIdealZeroSet_isIrreducible_of_isPrime
    (V : Variety k) (I : Ideal (Variety.PolynomialFunction V)) [I.IsPrime] :
    IsIrreducible (polynomialFunctionIdealZeroSet V I) := by
  let Z := polynomialFunctionIdealZeroSet V I
  let hZ := polynomialFunctionIdealZeroSet_isZariskiClosed V I
  apply isIrreducible_zeroLocus_of_isPrime V hZ
  rw [vanishingIdeal_polynomialFunctionIdealZeroSet_of_isPrime]
  infer_instance

lemma polynomialFunctionIdealZeroSet_maximal_irreducible_of_minimalPrime
    (V : Variety k) (J q : Ideal (Variety.PolynomialFunction V))
    (hq : q ∈ J.minimalPrimes) :
    IsIrreducible (polynomialFunctionIdealZeroSet V q) ∧
      polynomialFunctionIdealZeroSet V q ⊆
        polynomialFunctionIdealZeroSet V J ∧
      ∀ T : Set (Variety.Point V), IsIrreducible T →
        polynomialFunctionIdealZeroSet V q ⊆ T →
        T ⊆ polynomialFunctionIdealZeroSet V J →
        T = polynomialFunctionIdealZeroSet V q := by
  let : q.IsPrime := hq.isPrime
  have hqi := polynomialFunctionIdealZeroSet_isIrreducible_of_isPrime V q
  refine ⟨hqi, ?_, ?_⟩
  · intro x hx f hf
    exact hx f (hq.le hf)
  · intro T hTi hqT hTJ
    let C := closure T
    have hCz : IsZariskiClosed V C :=
      Variety.isClosed_iff_isZariskiClosed.mp isClosed_closure
    have hCi : IsIrreducible C := hTi.closure
    have hCJ : C ⊆ polynomialFunctionIdealZeroSet V J := by
      apply IsClosed.closure_subset_iff
        (Variety.isClosed_iff_isZariskiClosed.mpr
          (polynomialFunctionIdealZeroSet_isZariskiClosed V J)) |>.mpr
      exact hTJ
    let p := polynomialFunctionVanishingIdeal V C
    have hpprime : p.IsPrime :=
      polynomialFunctionVanishingIdeal_isPrime_of_isIrreducible V hCz hCi
    have hJp : J ≤ p := by
      intro f hf x hx
      exact hCJ hx f hf
    have hpq : p ≤ q := by
      intro f hf
      rw [← polynomialFunctionVanishingIdeal_idealZeroSet_of_isPrime V q]
      intro x hx
      exact hf x (subset_closure (hqT hx))
    have hpqeq : p = q :=
      Minimal.eq_of_le (show J.IsMinimalPrime q from hq) ⟨hpprime, hJp⟩ hpq
    have hCeq : C = polynomialFunctionIdealZeroSet V q := by
      rw [← hpqeq, polynomialFunctionIdealZeroSet_vanishingIdeal V hCz]
    apply Set.Subset.antisymm
    · exact fun x hx => hCeq ▸ subset_closure hx
    · exact hqT

lemma dimension_closedSubvariety_polynomialFunctionIdealZeroSet_of_isPrime
    (V : Variety k) (I : Ideal (Variety.PolynomialFunction V)) [I.IsPrime] :
    let hZ := polynomialFunctionIdealZeroSet_isZariskiClosed V I
    Variety.dimension (Variety.closedSubvariety hZ) =
      Algebra.trdeg k (Variety.PolynomialFunction V ⧸ I) := by
  dsimp only
  let Z := polynomialFunctionIdealZeroSet V I
  let hZ := polynomialFunctionIdealZeroSet_isZariskiClosed V I
  let W := Variety.closedSubvariety hZ
  have hZi : IsIrreducible Z :=
    polynomialFunctionIdealZeroSet_isIrreducible_of_isPrime V I
  let : Nonempty (Variety.Point W) := by
    rcases hZi.1 with ⟨x, hx⟩
    exact ⟨(Variety.closedSubvarietyPointEquiv hZ).symm ⟨x, hx⟩⟩
  have hprimeW : (vanishingIdeal
      (Set.univ : Set (Variety.Point W))).IsPrime := by
    rw [vanishingIdeal_closedSubvariety hZ,
      vanishingIdeal_polynomialFunctionIdealZeroSet_of_isPrime]
    infer_instance
  have hWirr : IsIrreducible (Set.univ : Set (Variety.Point W)) :=
    isIrreducible_univ_of_prime_vanishingIdeal W hprimeW
  rw [dimension_eq_fractionRing_of_isIrreducible W hWirr,
    trdeg_fractionRing_eq]
  change Algebra.trdeg k (MvPolynomial V.Coordinates k ⧸
      vanishingIdeal (Set.univ : Set (Variety.Point W))) =
    Algebra.trdeg k (Variety.PolynomialFunction V ⧸ I)
  rw [vanishingIdeal_closedSubvariety hZ,
    vanishingIdeal_polynomialFunctionIdealZeroSet_of_isPrime]
  exact (polynomialFunctionIdealQuotientAlgEquiv V I).trdeg_eq

omit [IsAlgClosed k] in
lemma mem_polynomialFunctionIdealZeroSet_iff_le_pointPrime
    (V : Variety k) (I : Ideal (Variety.PolynomialFunction V))
    (x : Variety.Point V) :
    x ∈ polynomialFunctionIdealZeroSet V I ↔ I ≤ (V.pointPrime x).asIdeal := by
  rfl

noncomputable def morphismFiberIdeal {V W : Variety k} (f : Variety.Morphism V W)
    (y : Variety.Point W) : Ideal (Variety.PolynomialFunction V) :=
  (W.pointPrime y).asIdeal.map f.pullbackRingHom

omit [IsAlgClosed k] in
lemma polynomialFunctionIdealZeroSet_morphismFiberIdeal
    {V W : Variety k} (f : Variety.Morphism V W) (y : Variety.Point W) :
    polynomialFunctionIdealZeroSet V (morphismFiberIdeal f y) =
      {x | f.toFun x = y} := by
  ext x
  rw [mem_polynomialFunctionIdealZeroSet_iff_le_pointPrime,
    morphismFiberIdeal, Ideal.map_le_iff_le_comap]
  have himage := f.pointPrime_image x
  change (W.pointPrime y).asIdeal ≤ (W.pointPrime (f.toFun x)).asIdeal ↔ _
  constructor
  · intro hle
    have heq : W.pointPrime y = W.pointPrime (f.toFun x) := by
      apply PrimeSpectrum.ext
      exact (W.pointPrime_isMaximal y).eq_of_le
        (W.pointPrime (f.toFun x)).isPrime.ne_top hle
    exact W.pointPrime_injective heq |>.symm
  · intro hxy
    rw [hxy]

omit [IsAlgClosed k] in
lemma dimension_eq_of_inverseMorphisms_of_isIrreducible
    {V W : Variety k} (f : Variety.Morphism V W) (g : Variety.Morphism W V)
    (hgf : ∀ x, g.toFun (f.toFun x) = x)
    (hfg : ∀ y, f.toFun (g.toFun y) = y)
    (hVi : IsIrreducible (Set.univ : Set (Variety.Point V)))
    (hWi : IsIrreducible (Set.univ : Set (Variety.Point W))) :
    Variety.dimension V = Variety.dimension W := by
  rw [dimension_eq_fractionRing_of_isIrreducible V hVi,
    dimension_eq_fractionRing_of_isIrreducible W hWi]
  let : IsDomain (coordinateRing V) :=
    isDomain_coordinateRing_of_isIrreducible V hVi
  let : IsDomain (coordinateRing W) :=
    isDomain_coordinateRing_of_isIrreducible W hWi
  let e : coordinateRing W ≃ₐ[k] coordinateRing V :=
    coordinateRingAlgEquivOfInverseMorphisms f g hgf hfg
  let eFrac : FractionRing (coordinateRing W) ≃ₐ[k]
      FractionRing (coordinateRing V) :=
    IsFractionRing.algEquivOfAlgEquiv e
  exact eFrac.trdeg_eq.symm

omit [IsAlgClosed k] in
lemma dimension_closedSubvariety_eq_of_set_eq
    {V : Variety k} {S T : Set (Variety.Point V)}
    (hS : IsZariskiClosed V S) (hT : IsZariskiClosed V T) (hST : S = T) :
    Variety.dimension (Variety.closedSubvariety hS) =
      Variety.dimension (Variety.closedSubvariety hT) := by
  subst T
  rfl

omit [IsAlgClosed k] in
lemma dimension_eq_trdeg_polynomialFunction_of_isIrreducible
    (V : Variety k) (hVi : IsIrreducible
      (Set.univ : Set (Variety.Point V))) :
    Variety.dimension V = Algebra.trdeg k (Variety.PolynomialFunction V) := by
  let : IsDomain (coordinateRing V) :=
    isDomain_coordinateRing_of_isIrreducible V hVi
  let : IsDomain (Variety.PolynomialFunction V) :=
    (coordinateRingAlgEquivPolynomialFunction V).toRingEquiv.isDomain_iff.mp
      inferInstance
  rw [dimension_eq_fractionRing_of_isIrreducible V hVi,
    trdeg_fractionRing_eq]
  exact (coordinateRingAlgEquivPolynomialFunction V).trdeg_eq

omit [IsAlgClosed k] in
private lemma Variety.Morphism.denseRange_of_pullback_injective
    {V W : Variety k} (f : Variety.Morphism V W)
    (hf : Function.Injective f.pullbackAlgHom) :
    Dense (Set.range f.toFun) := by
  rw [dense_iff_closure_eq]
  by_contra hne
  have hproper : closure (Set.range f.toFun) ⊂
      (Set.univ : Set (Variety.Point W)) :=
    ⟨Set.subset_univ _, fun h => hne (Set.eq_univ_of_univ_subset h)⟩
  have hideal : vanishingIdeal (Set.univ : Set (Variety.Point W)) <
      vanishingIdeal (closure (Set.range f.toFun)) :=
    vanishingIdeal_strict_antitone
      (Variety.isClosed_iff_isZariskiClosed.mp isClosed_univ)
      (Variety.isClosed_iff_isZariskiClosed.mp isClosed_closure)
      hproper
  obtain ⟨p, hpclosure, hpuniv⟩ := SetLike.exists_of_lt hideal
  let q := Variety.PolynomialFunction.ofPolynomial W p
  have hpullzero : f.pullbackAlgHom q = 0 := by
    apply Variety.PolynomialFunction.ext
    intro x
    change evalPolynomial (f.toFun x).val p = 0
    exact hpclosure (f.toFun x) (subset_closure ⟨x, rfl⟩)
  have hqzero : q = 0 := hf hpullzero
  apply hpuniv
  intro x _
  exact congrArg (fun r : Variety.PolynomialFunction W => r x) hqzero

set_option maxHeartbeats 800000 in
/-- A finite-fiber morphism between irreducible affine varieties of equal
dimension has dense range.  This is the affine finite-fiber dimension
criterion used in Steinberg's proof of Lang's theorem. -/
public theorem Variety.Morphism.denseRange_of_finite_fibers_of_dimension_eq
    {V W : Variety k} (f : Variety.Morphism V W)
    (hVi : IsIrreducible (Set.univ : Set (Variety.Point V)))
    (hWi : IsIrreducible (Set.univ : Set (Variety.Point W)))
    (hdim : Variety.dimension V = Variety.dimension W)
    (hfiber : ∀ y : Variety.Point W,
      Set.Finite {x : Variety.Point V | f.toFun x = y}) :
    Dense (Set.range f.toFun) := by
  classical
  let A := Variety.PolynomialFunction V
  let B := Variety.PolynomialFunction W
  let : Algebra k A := polynomialFunctionAlgebra V
  let : Algebra k B := polynomialFunctionAlgebra W
  let : IsDomain (coordinateRing V) :=
    isDomain_coordinateRing_of_isIrreducible V hVi
  let : IsDomain A :=
    (coordinateRingAlgEquivPolynomialFunction V).toRingEquiv.isDomain_iff.mp
      inferInstance
  let : IsDomain (coordinateRing W) :=
    isDomain_coordinateRing_of_isIrreducible W hWi
  let : IsDomain B :=
    (coordinateRingAlgEquivPolynomialFunction W).toRingEquiv.isDomain_iff.mp
      inferInstance
  let : Algebra.FiniteType k A := polynomialFunction_finiteType V
  let : Algebra.FiniteType k B := polynomialFunction_finiteType W
  let φ : B →ₐ[k] A := f.pullbackAlgHom
  let P : Ideal B := RingHom.ker φ
  have hPprime : P.IsPrime := RingHom.ker_isPrime (f := φ.toRingHom)
  let : P.IsPrime := hPprime
  let B₀ := B ⧸ P
  let πP : B →ₐ[k] B₀ := Ideal.Quotient.mkₐ k P
  let φ₀ : B₀ →ₐ[k] A := Ideal.kerLiftAlg φ
  let : Algebra B₀ A := φ₀.toRingHom.toAlgebra
  have hφ₀inj : Function.Injective φ₀ := Ideal.kerLiftAlg_injective φ
  let : FaithfulSMul B₀ A :=
    (faithfulSMul_iff_algebraMap_injective B₀ A).mpr hφ₀inj
  let : IsScalarTower k B₀ A := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap k A r =
      Ideal.kerLiftAlg φ (Ideal.Quotient.mk P (algebraMap k B r))
    rw [Ideal.kerLiftAlg_mk φ]
    exact (φ.commutes r).symm
  let : Algebra.FiniteType k B₀ :=
    Algebra.FiniteType.of_surjective πP Ideal.Quotient.mk_surjective
  let : Algebra.FiniteType B₀ A :=
    Algebra.FiniteType.of_restrictScalars_finiteType k B₀ A
  obtain ⟨g, _⟩ := hVi.1
  let M : Ideal A := (V.pointPrime g).asIdeal
  let NY : Ideal B := (W.pointPrime (f.toFun g)).asIdeal
  have hP_le_NY : P ≤ NY := by
    change RingHom.ker f.pullbackAlgHom ≤
      (W.pointPrime (f.toFun g)).asIdeal
    rw [f.pointPrime_image g]
    intro b hb
    change f.pullbackRingHom b = 0 at hb
    change f.pullbackRingHom b ∈ (V.pointPrime g).asIdeal
    rw [hb]
    exact (V.pointPrime g).asIdeal.zero_mem
  let N : Ideal B₀ := NY.map πP
  have hMmax : M.IsMaximal := V.pointPrime_isMaximal g
  have hNYmax : NY.IsMaximal := W.pointPrime_isMaximal (f.toFun g)
  have hNmax : N.IsMaximal := by
    dsimp only [N]
    apply Ideal.IsMaximal.map_of_surjective_of_ker_le
      Ideal.Quotient.mk_surjective
    change RingHom.ker (Ideal.Quotient.mk P) ≤ NY
    rw [Ideal.mk_ker]
    exact hP_le_NY
  let : M.IsMaximal := hMmax
  let : M.IsPrime := hMmax.isPrime
  let : N.IsMaximal := hNmax
  let : N.IsPrime := hNmax.isPrime
  have hφcomp : φ₀.toRingHom.comp πP.toRingHom = φ.toRingHom := by
    apply RingHom.ext
    intro b
    exact Ideal.kerLiftAlg_mk φ b
  have hMN : M.under B₀ = N := by
    apply Ideal.comap_injective_of_surjective πP.toRingHom
      Ideal.Quotient.mk_surjective
    rw [Ideal.comap_comap]
    change M.comap (φ₀.toRingHom.comp πP.toRingHom) =
      (NY.map πP.toRingHom).comap πP.toRingHom
    rw [hφcomp, Ideal.comap_map_of_surjective πP.toRingHom
      Ideal.Quotient.mk_surjective]
    rw [← RingHom.ker_eq_comap_bot,
      show RingHom.ker πP.toRingHom = P from Ideal.mk_ker,
      sup_eq_left.mpr hP_le_NY]
    exact congrArg PrimeSpectrum.asIdeal (f.pointPrime_image g).symm
  have hMNlies : M.LiesOver N := ⟨hMN.symm⟩
  let : M.LiesOver N := hMNlies
  let J : Ideal A := N.map (algebraMap B₀ A)
  have hJfiber : J = morphismFiberIdeal f (f.toFun g) := by
    change (NY.map πP.toRingHom).map φ₀.toRingHom =
      NY.map f.pullbackRingHom
    rw [Ideal.map_map, hφcomp]
    rfl
  have hJM : J ≤ M := by
    rw [hJfiber]
    exact (mem_polynomialFunctionIdealZeroSet_iff_le_pointPrime V
      (morphismFiberIdeal f (f.toFun g)) g).mp <| by
        rw [polynomialFunctionIdealZeroSet_morphismFiberIdeal]
        rfl
  let πJ : A →+* A ⧸ J := Ideal.Quotient.mk J
  let Mbar : Ideal (A ⧸ J) := M.map πJ
  have hcomapBotJ : (⊥ : Ideal (A ⧸ J)).comap πJ = J := by
    change RingHom.ker πJ = J
    exact Ideal.mk_ker
  have hMbarmax : Mbar.IsMaximal := by
    dsimp only [Mbar]
    apply Ideal.IsMaximal.map_of_surjective_of_ker_le
      Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker]
    exact hJM
  let : Mbar.IsMaximal := hMbarmax
  let : Mbar.IsPrime := hMbarmax.isPrime
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let : IsNoetherianRing B₀ := Algebra.FiniteType.isNoetherianRing k B₀
  have hfiberheight : Mbar.height ≤ 0 := by
    apply height_le_of_minimalPrimes_quotient_height_le
    intro qbar hqbar hqbarM
    let : qbar.IsPrime := hqbar.isPrime
    let q0 : Ideal A := qbar.comap πJ
    have hq0prime : q0.IsPrime := Ideal.comap_isPrime πJ qbar
    let : q0.IsPrime := hq0prime
    have hJq0 : J ≤ q0 := by
      change J ≤ qbar.comap πJ
      intro a ha
      change πJ a ∈ qbar
      rw [show πJ a = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact qbar.zero_mem
    have hq0M : q0 ≤ M := by
      have hcomapM : (M.map πJ).comap πJ = M := by
        rw [Ideal.comap_map_of_surjective πJ Ideal.Quotient.mk_surjective,
          hcomapBotJ]
        exact sup_eq_left.mpr hJM
      exact (Ideal.comap_mono (f := πJ) hqbarM).trans_eq hcomapM
    have hZq0finite : Set.Finite (polynomialFunctionIdealZeroSet V q0) := by
      apply (hfiber (f.toFun g)).subset
      intro x hx
      rw [← polynomialFunctionIdealZeroSet_morphismFiberIdeal f (f.toFun g),
        ← hJfiber]
      exact fun a ha => hx a (hJq0 ha)
    let hZq0 := polynomialFunctionIdealZeroSet_isZariskiClosed V q0
    have hdimq0 : Variety.dimension (Variety.closedSubvariety hZq0) = 0 := by
      rw [dimension_zero_iff_finite_points]
      let : Finite {x : Variety.Point V // x ∈
          polynomialFunctionIdealZeroSet V q0} :=
        Set.finite_coe_iff.mpr hZq0finite
      exact Finite.of_injective
        (fun x : Variety.Point (Variety.closedSubvariety hZq0) =>
          Variety.closedSubvarietyPointEquiv hZq0 x)
        (by
          intro x y hxy
          exact (Variety.closedSubvarietyPointEquiv hZq0).injective hxy)
    have htrq0 : Algebra.trdeg k (A ⧸ q0) = 0 := by
      rw [← dimension_closedSubvariety_polynomialFunctionIdealZeroSet_of_isPrime
        V q0]
      exact hdimq0
    have hmapq0 : q0.map πJ = qbar :=
      Ideal.map_comap_of_surjective πJ Ideal.Quotient.mk_surjective qbar
    let e0 : ((A ⧸ J) ⧸ qbar) ≃ₐ[k]
        ((A ⧸ J) ⧸ q0.map (Ideal.Quotient.mkₐ k J)) :=
      Ideal.quotientEquivAlgOfEq k hmapq0.symm
    let e1 : ((A ⧸ J) ⧸ q0.map (Ideal.Quotient.mkₐ k J)) ≃ₐ[k]
        A ⧸ q0 := DoubleQuot.quotQuotEquivQuotOfLEₐ k hJq0
    let e := e0.trans e1
    have hqbarMmax :
        (Mbar.map (Ideal.Quotient.mk qbar)).IsMaximal := by
      apply Ideal.IsMaximal.map_of_surjective_of_ker_le
        Ideal.Quotient.mk_surjective
      rw [Ideal.mk_ker]
      exact hqbarM
    let : (Mbar.map (Ideal.Quotient.mk qbar)).IsMaximal := hqbarMmax
    let : Algebra.FiniteType k (A ⧸ J) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k J)
        Ideal.Quotient.mk_surjective
    let : Algebra.FiniteType k ((A ⧸ J) ⧸ qbar) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k qbar)
        Ideal.Quotient.mk_surjective
    rw [domain_maximal_height_eq_trdeg (k := k) ((A ⧸ J) ⧸ qbar)
      (Mbar.map (Ideal.Quotient.mk qbar)), e.trdeg_eq, htrq0]
    simp
  have hheightMain : M.height ≤ N.height + Mbar.height := by
    have h := Ideal.height_le_height_add_of_liesOver N M
    simpa only [J, Mbar, πJ] using h
  have hheightTotal : M.height ≤ N.height := by
    exact hheightMain.trans (by
      simpa [add_comm] using add_le_add_right hfiberheight N.height)
  have hNat : Cardinal.toNat (Algebra.trdeg k A) ≤
      Cardinal.toNat (Algebra.trdeg k B₀) := by
    have h' : (Cardinal.toNat (Algebra.trdeg k A) : ℕ∞) ≤
        (Cardinal.toNat (Algebra.trdeg k B₀) : ℕ∞) := by
      rw [← domain_maximal_height_eq_trdeg A M,
        ← domain_maximal_height_eq_trdeg B₀ N]
      exact hheightTotal
    exact_mod_cast h'
  have hAfin : Algebra.trdeg k A < ℵ₀ := trdeg_lt_aleph0_of_finiteType
  have hB₀fin : Algebra.trdeg k B₀ < ℵ₀ := trdeg_lt_aleph0_of_finiteType
  have htrle : Algebra.trdeg k A ≤ Algebra.trdeg k B₀ :=
    (Cardinal.toNat_le_iff_le_of_lt_aleph0 hAfin hB₀fin).mp hNat
  have htrAB : Algebra.trdeg k A = Algebra.trdeg k B := by
    rw [← dimension_eq_trdeg_polynomialFunction_of_isIrreducible V hVi,
      ← dimension_eq_trdeg_polynomialFunction_of_isIrreducible W hWi]
    exact hdim
  have hPbot : P = ⊥ := by
    by_contra hP
    have hstrict : Algebra.trdeg k B₀ < Algebra.trdeg k B :=
      trdeg_quotient_lt_of_ne_bot B P hP
    exact (not_lt_of_ge (htrAB ▸ htrle)) hstrict
  apply f.denseRange_of_pullback_injective
  exact (RingHom.injective_iff_ker_eq_bot φ.toRingHom).mpr hPbot

lemma fiber_minimalPrime_dimension_eq_kernel
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) (g : Variety.Point G)
    (q : Ideal (Variety.PolynomialFunction G))
    (hq : q ∈ (morphismFiberIdeal f.toVariety (f.onPoints g)).minimalPrimes)
    (hqg : q ≤ (G.pointPrime g).asIdeal) :
    let hC := polynomialFunctionIdealZeroSet_isZariskiClosed G q
    Variety.dimension (Variety.closedSubvariety hC) =
      Variety.dimension f.kernelClosedSubgroup.carrierVariety := by
  dsimp only
  let J := morphismFiberIdeal f.toVariety (f.onPoints g)
  let F := polynomialFunctionIdealZeroSet G J
  let hF := polynomialFunctionIdealZeroSet_isZariskiClosed G J
  let C := polynomialFunctionIdealZeroSet G q
  let hC := polynomialFunctionIdealZeroSet_isZariskiClosed G q
  let K := f.kernelClosedSubgroup
  let Gf := Variety.closedSubvariety hF
  let Gk := K.carrierVariety
  let eF := Variety.closedSubvarietyPointHomeomorph hF
  let incF : Variety.Point Gf → Variety.Point G := fun x => (eF x).1
  have hF_eq : F = {x | f.onPoints x = f.onPoints g} := by
    simpa [F, J, AlgebraicGroup.Morphism.onPoints] using
      polynomialFunctionIdealZeroSet_morphismFiberIdeal
        f.toVariety (f.onPoints g)
  have hCg : g ∈ C :=
    (mem_polynomialFunctionIdealZeroSet_iff_le_pointPrime G q g).2 hqg
  have hCdata :=
    polynomialFunctionIdealZeroSet_maximal_irreducible_of_minimalPrime G J q hq
  have hCi : IsIrreducible C := hCdata.1
  have hCF : C ⊆ F := hCdata.2.1
  have hCmax := hCdata.2.2
  have hgF : g ∈ F := hCF hCg
  let L0 := AlgebraicGroup.leftMulMorphism G g
  let I0 := AlgebraicGroup.leftMulMorphism G g⁻¹
  have hKtoF : ∀ x, x ∈ (K : Set (Variety.Point G)) → L0.toFun x ∈ F := by
    intro x hx
    rw [hF_eq]
    change f.onPoints (g * x) = f.onPoints g
    change f.onPoints x = 1 at hx
    rw [map_mul, hx, mul_one]
  have hFtoK : ∀ x, x ∈ F → I0.toFun x ∈ (K : Set (Variety.Point G)) := by
    intro x hx
    rw [hF_eq] at hx
    change f.onPoints (g⁻¹ * x) = 1
    rw [map_mul, map_inv, hx]
    simp
  let L := L0.restrictClosedSubvariety K.isZariskiClosed hF hKtoF
  let I := I0.restrictClosedSubvariety hF K.isZariskiClosed hFtoK
  have hIL : ∀ x, I.toFun (L.toFun x) = x := by
    intro x
    apply (Variety.closedSubvarietyPointEquiv K.isZariskiClosed).injective
    apply Subtype.ext
    rw [Variety.Morphism.restrictClosedSubvariety_apply,
      Variety.Morphism.restrictClosedSubvariety_apply]
    simp [L0, I0, AlgebraicGroup.leftMulMorphism_apply]
  have hLI : ∀ x, L.toFun (I.toFun x) = x := by
    intro x
    apply (Variety.closedSubvarietyPointEquiv hF).injective
    apply Subtype.ext
    rw [Variety.Morphism.restrictClosedSubvariety_apply,
      Variety.Morphism.restrictClosedSubvariety_apply]
    simp [L0, I0, AlgebraicGroup.leftMulMorphism_apply]
  let eTrans : Variety.Point Gk ≃ₜ Variety.Point Gf :=
    { toEquiv :=
        { toFun := L.toFun
          invFun := I.toFun
          left_inv := hIL
          right_inv := hLI }
      continuous_toFun := L.continuous
      continuous_invFun := I.continuous }
  let C' : Set (Variety.Point Gf) := incF ⁻¹' C
  have hC'z : IsZariskiClosed Gf C' := by
    rw [← Variety.isClosed_iff_isZariskiClosed]
    exact (Variety.isClosed_iff_isZariskiClosed.mpr hC).preimage
      (continuous_subtype_val.comp eF.continuous)
  have hincC : incF '' C' = C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      let y : Variety.Point Gf := eF.symm ⟨x, hCF hx⟩
      refine ⟨y, ?_, ?_⟩
      · change incF y ∈ C
        simpa [incF, y]
      · simp [incF, y]
  have hC'i : IsIrreducible C' := by
    let u : {x : Variety.Point G // x ∈ C} → Variety.Point Gf := fun x =>
      eF.symm ⟨x.1, hCF x.2⟩
    have hu : Continuous u := eF.symm.continuous.comp
      (continuous_subtype_val.subtype_mk fun x => hCF x.2)
    let : IrreducibleSpace {x : Variety.Point G // x ∈ C} :=
      Subtype.irreducibleSpace hCi
    have himage := (IrreducibleSpace.isIrreducible_univ _).image u hu.continuousOn
    have hurange : u '' Set.univ = C' := by
      ext y
      constructor
      · rintro ⟨x, -, rfl⟩
        change incF (u x) ∈ C
        simp [u, incF]
      · intro hy
        let x : {x : Variety.Point G // x ∈ C} := ⟨incF y, hy⟩
        refine ⟨x, Set.mem_univ _, ?_⟩
        apply eF.injective
        apply Subtype.ext
        simp [u, x, incF]
    rwa [hurange] at himage
  have hC'comp : C' ∈ irreducibleComponents (Variety.Point Gf) := by
    refine ⟨hC'i, ?_⟩

    intro T hTi hC'T
    have hTimagei : IsIrreducible (incF '' T) :=
      hTi.image incF (continuous_subtype_val.comp eF.continuous).continuousOn
    have hCimageT : C ⊆ incF '' T := by
      intro x hx
      let y : Variety.Point Gf := eF.symm ⟨x, hCF hx⟩
      have hyC : y ∈ C' := by
        change incF y ∈ C
        simpa [incF, y]
      exact ⟨y, hC'T hyC, by simp [incF, y]⟩
    have hTimageF : incF '' T ⊆ F := by
      rintro _ ⟨y, -, rfl⟩
      exact (eF y).2
    have hEq : incF '' T = C := hCmax (incF '' T) hTimagei hCimageT hTimageF
    intro y hyT
    change incF y ∈ C
    rw [← hEq]
    exact ⟨y, hyT, rfl⟩
  let gF : Variety.Point Gf := eF.symm ⟨g, hgF⟩
  have hgC' : gF ∈ C' := by
    change incF gF ∈ C
    simpa [gF, incF]
  have heone : eTrans (1 : Variety.Point Gk) = gF := by
    apply eF.injective
    apply Subtype.ext
    change g * (K.inclusion.onPoints 1) = g
    calc
      g * K.inclusion.onPoints 1 = g * 1 :=
        congrArg (fun z : Variety.Point G => g * z) K.inclusion.map_one
      _ = g := mul_one g
  have heK0 : eTrans '' AlgebraicGroup.identityComponent Gk =
      connectedComponent gF := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      have hsub := eTrans.continuous.image_connectedComponent_subset
        (1 : Variety.Point Gk)
      rw [show AlgebraicGroup.identityComponent Gk =
          connectedComponent (1 : Variety.Point Gk) from rfl] at hx
      have := hsub ⟨x, hx, rfl⟩
      rwa [heone] at this
    · intro y hy
      have hsub := eTrans.symm.continuous.image_connectedComponent_subset gF
      have hy' := hsub ⟨y, hy, rfl⟩
      have hpre : eTrans.symm gF = (1 : Variety.Point Gk) := by
        apply eTrans.injective
        rw [eTrans.apply_symm_apply, heone]
      rw [hpre] at hy'
      exact ⟨eTrans.symm y, hy', eTrans.apply_symm_apply y⟩
  have hC'eK0 : C' ⊆ eTrans '' AlgebraicGroup.identityComponent Gk := by
    rw [heK0]
    exact hC'i.isConnected.subset_connectedComponent hgC'
  have heK0i : IsIrreducible
      (eTrans '' AlgebraicGroup.identityComponent Gk) :=
    (AlgebraicGroup.identityComponent_isIrreducible Gk).image
      eTrans eTrans.continuous.continuousOn
  have heK0C' : eTrans '' AlgebraicGroup.identityComponent Gk = C' :=
    Set.Subset.antisymm (hC'comp.2 heK0i hC'eK0) hC'eK0
  let hK0z := AlgebraicGroup.identityComponent_isClosed Gk
  have hL0 : ∀ x, x ∈ AlgebraicGroup.identityComponent Gk →
      L.toFun x ∈ C' := by
    intro x hx
    rw [← heK0C']
    exact ⟨x, hx, rfl⟩
  have hI0 : ∀ x, x ∈ C' →
      I.toFun x ∈ AlgebraicGroup.identityComponent Gk := by
    intro x hx
    have hx' : x ∈ eTrans '' AlgebraicGroup.identityComponent Gk := by
      rwa [heK0C']
    rcases hx' with ⟨y, hy, hxy⟩
    have : I.toFun x = y := by
      rw [← hxy]
      exact hIL y
    rwa [this]
  let L' := L.restrictClosedSubvariety hK0z hC'z hL0
  let I' := I.restrictClosedSubvariety hC'z hK0z hI0
  have hI'L' : ∀ x, I'.toFun (L'.toFun x) = x := by
    intro x
    apply (Variety.closedSubvarietyPointEquiv hK0z).injective
    apply Subtype.ext
    rw [Variety.Morphism.restrictClosedSubvariety_apply,
      Variety.Morphism.restrictClosedSubvariety_apply]
    change I.toFun (L.toFun
      (Variety.closedSubvarietyPointEquiv hK0z x).1) =
        (Variety.closedSubvarietyPointEquiv hK0z x).1
    exact hIL _
  have hL'I' : ∀ x, L'.toFun (I'.toFun x) = x := by
    intro x
    apply (Variety.closedSubvarietyPointEquiv hC'z).injective
    apply Subtype.ext
    rw [Variety.Morphism.restrictClosedSubvariety_apply,
      Variety.Morphism.restrictClosedSubvariety_apply]
    change L.toFun (I.toFun
      (Variety.closedSubvarietyPointEquiv hC'z x).1) =
        (Variety.closedSubvarietyPointEquiv hC'z x).1
    exact hLI _
  let WK0 := Variety.closedSubvariety hK0z
  let WC' := Variety.closedSubvariety hC'z
  let eK0 := Variety.closedSubvarietyPointHomeomorph hK0z
  let : IrreducibleSpace
      {x : Variety.Point Gk // x ∈ AlgebraicGroup.identityComponent Gk} :=
    Subtype.irreducibleSpace (AlgebraicGroup.identityComponent_isIrreducible Gk)
  let : IrreducibleSpace (Variety.Point WK0) :=
    eK0.irreducibleSpace_iff.mpr inferInstance
  have hWK0i : IsIrreducible (Set.univ : Set (Variety.Point WK0)) :=
    IrreducibleSpace.isIrreducible_univ _
  let eC' := Variety.closedSubvarietyPointHomeomorph hC'z
  let : IrreducibleSpace {x : Variety.Point Gf // x ∈ C'} :=
    Subtype.irreducibleSpace hC'i
  let : IrreducibleSpace (Variety.Point WC') :=
    eC'.irreducibleSpace_iff.mpr inferInstance
  have hWC'i : IsIrreducible (Set.univ : Set (Variety.Point WC')) :=
    IrreducibleSpace.isIrreducible_univ _
  have hdimIso : Variety.dimension WK0 = Variety.dimension WC' :=
    dimension_eq_of_inverseMorphisms_of_isIrreducible
      L' I' hI'L' hL'I' hWK0i hWC'i
  have hdimK0 : Variety.dimension WK0 = Variety.dimension Gk := by
    rw [dimension_eq_fractionRing_of_isIrreducible WK0 hWK0i,
      AlgebraicGroup.dimension_eq_identityComponent Gk]
    rfl
  have hdimAmbient : Variety.dimension WC' =
      Variety.dimension (Variety.closedSubvariety hC) := by
    let D := (fun y : Variety.Point Gf =>
      (Variety.closedSubvarietyPointEquiv hF y).1) '' C'
    let hD := closedSubvariety_image_isZariskiClosed hF hC'z
    have h := closedSubvariety_image_dimension_eq_of_isIrreducible hF hC'z hC'i
    have hdimD : Variety.dimension WC' =
        Variety.dimension (Variety.closedSubvariety hD) := by
      simpa [WC', D, hD] using h
    have hincC' : (fun y : Variety.Point Gf =>
        (Variety.closedSubvarietyPointEquiv hF y).1) '' C' = C := by
      change incF '' C' = C
      exact hincC
    exact hdimD.trans
      (dimension_closedSubvariety_eq_of_set_eq hD hC hincC')
  rw [← hdimK0, hdimIso, hdimAmbient]

lemma quasiFiniteAt_bot_adjoin_of_isTranscendenceBasis
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Nontrivial R] [IsDomain A] [FaithfulSMul R A] [Algebra.FiniteType R A]
    {ι : Type u} {x : ι → A} (hx : IsTranscendenceBasis R x) :
    let C := Algebra.adjoin R (Set.range x)
    Algebra.QuasiFiniteAt C (⊥ : Ideal A) := by
  dsimp only
  unfold Algebra.QuasiFiniteAt
  let hTarget : Algebra (Algebra.adjoin R (Set.range x))
      (Localization.AtPrime (⊥ : Ideal A)) := OreLocalization.instAlgebra
  let C := Algebra.adjoin R (Set.range x)
  let L := Localization.AtPrime (⊥ : Ideal A)
  let K := FractionRing C
  let F := FractionRing A
  have hL : IsFractionRing A L := by
    simpa [Ideal.primeCompl_bot] using
      Localization.isLocalization (M := (⊥ : Ideal A).primeCompl)
  let : IsFractionRing A L := hL
  let : Algebra C L := hTarget
  let : Algebra C K := inferInstance
  let : Algebra K F := FractionRing.liftAlgebra C F
  let : IsScalarTower C K F := FractionRing.isScalarTower_liftAlgebra C F
  let : Algebra.IsAlgebraic C A := hx.isAlgebraic
  let : Algebra.IsAlgebraic C F :=
    (IsFractionRing.isAlgebraic_iff' C A F).mp inferInstance
  let : Algebra.IsAlgebraic K F :=
    Algebra.IsAlgebraic.extendScalars
      (FaithfulSMul.algebraMap_injective C K)
  let : Algebra.FiniteType C A :=
    Algebra.FiniteType.of_restrictScalars_finiteType R C A
  let : Algebra.EssFiniteType C F :=
    Algebra.EssFiniteType.comp C A F
  let : Algebra.EssFiniteType K F :=
    Algebra.EssFiniteType.of_comp C K F
  let : Module.Finite K F :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  let : Algebra.QuasiFinite C K := inferInstance
  let : Algebra.QuasiFinite K F := inferInstance
  have hF : Algebra.QuasiFinite C F := Algebra.QuasiFinite.trans C K F
  let eA : F ≃ₐ[A] L :=
    IsLocalization.algEquiv (nonZeroDivisors A) F L
  let f : F →ₐ[C] L :=
    { eA.toRingHom with
      commutes' := fun c => by
        rw [IsScalarTower.algebraMap_apply C A F,
          IsScalarTower.algebraMap_apply C A L]
        exact eA.commutes (algebraMap C A c) }
  let : Algebra.QuasiFinite C F := hF
  change @Algebra.QuasiFinite C L _ _ hTarget
  exact Algebra.QuasiFinite.of_surjective_algHom f eA.surjective

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
lemma connected_surjective_morphism_dimension
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) (hG : Variety.IsConnected G)
    (hf : Function.Surjective f.onPoints) :
    Variety.dimension G =
      Variety.dimension H +
        Variety.dimension f.kernelClosedSubgroup.carrierVariety := by
  let A := Variety.PolynomialFunction G
  let B := Variety.PolynomialFunction H
  have hG0 : AlgebraicGroup.identityComponent G = Set.univ :=
    (identityComponent_eq_univ_iff_isConnected G).mpr hG
  have hH0 : AlgebraicGroup.identityComponent H = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    intro y _
    obtain ⟨x, rfl⟩ := hf y
    exact f.image_identityComponent_subset ⟨x, by rw [hG0]; trivial, rfl⟩
  have hGi : IsIrreducible (Set.univ : Set (Variety.Point G)) := by
    rw [← hG0]
    exact AlgebraicGroup.identityComponent_isIrreducible G
  have hHi : IsIrreducible (Set.univ : Set (Variety.Point H)) := by
    rw [← hH0]
    exact AlgebraicGroup.identityComponent_isIrreducible H
  let : Algebra k A := polynomialFunctionAlgebra G
  let : Algebra k B := polynomialFunctionAlgebra H
  let : IsDomain (coordinateRing G) :=
    isDomain_coordinateRing_of_isIrreducible G hGi
  let : IsDomain A :=
    (coordinateRingAlgEquivPolynomialFunction G).toRingEquiv.isDomain_iff.mp
      inferInstance
  let : IsDomain (coordinateRing H) :=
    isDomain_coordinateRing_of_isIrreducible H hHi
  let : IsDomain B :=
    (coordinateRingAlgEquivPolynomialFunction H).toRingEquiv.isDomain_iff.mp
      inferInstance
  let : FaithfulSMul k B :=
    (faithfulSMul_iff_algebraMap_injective (R := k) (A := B)).mpr
      (algebraMap k B).injective
  let : Algebra B A := f.toVariety.pullbackAlgHom.toRingHom.toAlgebra
  have hpull : Function.Injective (algebraMap B A) := by
    intro a b hab
    apply Variety.PolynomialFunction.ext
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact congrArg (fun c : A => c x) hab
  let : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr hpull
  let : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq fun r =>
    (f.toVariety.pullbackAlgHom.commutes r).symm
  let : Algebra.FiniteType k A := polynomialFunction_finiteType G
  let : Algebra.FiniteType k B := polynomialFunction_finiteType H
  let : Algebra.FiniteType B A :=
    Algebra.FiniteType.of_restrictScalars_finiteType k B A
  obtain ⟨t, htfin, htb⟩ :=
    exists_finite_isTranscendenceBasis_subset (R := B) (A := A)
  let x : t → A := fun i => i.1
  let C := Algebra.adjoin B (Set.range x)
  let hCA : Algebra C A := inferInstance
  let : Algebra C A := hCA
  let : Algebra.FiniteType C A :=
    Algebra.FiniteType.of_restrictScalars_finiteType B C A
  have hqf0 : Algebra.QuasiFiniteAt C (⊥ : Ideal A) :=
    quasiFiniteAt_bot_adjoin_of_isTranscendenceBasis htb
  let : Algebra.QuasiFiniteAt C (⊥ : Ideal A) := hqf0
  have hzm : Algebra.ZariskisMainProperty C (⊥ : Ideal A) :=
    Algebra.ZariskisMainProperty.of_finiteType (R := C) (S := A) (⊥ : Ideal A)
  obtain ⟨S', hS', r, hr0, hrbij⟩ :=
    hzm.exists_fg_and_exists_notMem_and_awayMap_bijective (⊥ : Ideal A)
  let : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have hbotjac : (⊥ : Ideal A).jacobson = ⊥ :=
    IsJacobsonRing.out' (⊥ : Ideal A) Ideal.isRadical_bot
  obtain ⟨M, ⟨hbotM, hMmax⟩, hrM⟩ :=
    (Ideal.eq_jacobson_iff_notMem (I := (⊥ : Ideal A))).mp hbotjac r.1 hr0
  let : M.IsMaximal := hMmax
  let : M.IsPrime := hMmax.isPrime
  have hqfM : Algebra.QuasiFiniteAt C M :=
    quasiFiniteAt_of_fg_and_awayMap_bijective S' hS' r hrM hrbij
  let : Algebra.QuasiFiniteAt C M := hqfM
  obtain ⟨g, hg⟩ := G.exists_pointPrime_eq_of_isMaximal M hMmax
  have hMg : M = (G.pointPrime g).asIdeal :=
    (congrArg PrimeSpectrum.asIdeal hg).symm
  let N := (H.pointPrime (f.onPoints g)).asIdeal
  let J := morphismFiberIdeal f.toVariety (f.onPoints g)
  have hNmax : N.IsMaximal := H.pointPrime_isMaximal (f.onPoints g)
  let : N.IsMaximal := hNmax
  let : N.IsPrime := hNmax.isPrime
  have hJM : J ≤ M := by
    rw [hMg]
    exact (mem_polynomialFunctionIdealZeroSet_iff_le_pointPrime G J g).mp <| by
      rw [polynomialFunctionIdealZeroSet_morphismFiberIdeal]
      rfl
  obtain ⟨q, hq, hqM⟩ := Ideal.exists_minimalPrimes_le hJM
  let : q.IsPrime := hq.isPrime
  let rB : t → B := fun i => algebraMap k B (x i g)
  have hdiffM (i : t) : x i - algebraMap B A (rB i) ∈ M := by
    rw [hMg]
    change x i g - (algebraMap B A (rB i)) g = 0
    rw [← IsScalarTower.algebraMap_apply k B A]
    rw [polynomialFunction_algebraMap_apply]
    simp
  let I : Ideal A :=
    Ideal.span (Set.range fun i : t => x i - algebraMap B A (rB i))
  have hIM : I ≤ M := by
    change Ideal.span (Set.range fun i : t =>
      x i - algebraMap B A (rB i)) ≤ M
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hdiffM i
  obtain ⟨p, hp, hpM⟩ :=
    Ideal.exists_minimalPrimes_le (show q ⊔ I ≤ M from sup_le hqM hIM)
  let : p.IsPrime := hp.isPrime
  have hMN : M.under B = N := by
    change M.comap f.toVariety.pullbackRingHom =
      (H.pointPrime (f.onPoints g)).asIdeal
    rw [hMg]
    exact congrArg PrimeSpectrum.asIdeal (f.toVariety.pointPrime_image g).symm
  have hJq : J ≤ q := hq.le
  have hNp : N ≤ p.under B := by
    change N ≤ p.comap f.toVariety.pullbackRingHom
    rw [← Ideal.map_le_iff_le_comap]
    simpa [J, morphismFiberIdeal, N] using hJq.trans (le_sup_left.trans hp.le)
  have hpunder : p.under B = M.under B := by
    have hMp : M.under B ≤ p.under B := by
      rw [hMN]
      exact hNp
    exact le_antisymm (Ideal.comap_mono hpM) hMp
  have hdiffp (i : t) : x i - algebraMap B A (rB i) ∈ p :=
    (le_sup_right.trans hp.le) (Ideal.subset_span ⟨i, rfl⟩)
  have hpunderC : p.under C = M.under C := by
    simpa [C] using under_adjoin_eq_of_under_eq_of_sub_mem
      htb.1 hpM hpunder rB hdiffp
  have hpEqM : p = M :=
    Algebra.QuasiFiniteAt.eq_of_le_of_under_eq (R := C) hpM hpunderC
  have hMmin : M ∈ (q ⊔ I).minimalPrimes := by
    rw [← hpEqM]
    exact hp
  let π : A →+* A ⧸ q := Ideal.Quotient.mk q
  let s : Set (A ⧸ q) :=
    Set.range fun i : t => π (x i - algebraMap B A (rB i))
  let : Fintype t := htfin.fintype
  have hsfin : s.Finite := Set.finite_range _
  have hMqmin : M.map π ∈ (Ideal.span s).minimalPrimes := by
    have hmap : M.map π ∈ (I.map π).minimalPrimes := by
      rw [Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective I]
      refine ⟨M, ?_, rfl⟩
      rw [Ideal.mk_ker, sup_comm]
      exact hMmin
    have hIs : I.map π = Ideal.span s := by
      change Ideal.map π (Ideal.span (Set.range fun i : t =>
        x i - algebraMap B A (rB i))) = Ideal.span s
      rw [Ideal.map_span]
      congr 1
      ext z
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨_, ⟨i, rfl⟩, rfl⟩
    rwa [hIs] at hmap
  have hMqmax : (M.map π).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective <| by
      rw [Ideal.mk_ker]
      exact hqM
  let : (M.map π).IsMaximal := hMqmax
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hheight : (M.map π).height ≤ s.ncard :=
    Ideal.height_le_card_of_mem_minimalPrimes_span hsfin hMqmin
  have hncard : s.ncard ≤ Fintype.card t := by
    simpa [s] using Set.ncard_image_le
      (f := fun i : t => π (x i - algebraMap B A (rB i)))
      (s := Set.univ)
  have htrNat : Cardinal.toNat (Algebra.trdeg k (A ⧸ q)) ≤ Fintype.card t := by
    have hheight' : (Cardinal.toNat (Algebra.trdeg k (A ⧸ q)) : ℕ∞) ≤
        (Fintype.card t : ℕ∞) := by
      rw [← domain_maximal_height_eq_trdeg (A ⧸ q) (M.map π)]
      exact hheight.trans (by exact_mod_cast hncard)
    exact_mod_cast hheight'
  have htrqfin : Algebra.trdeg k (A ⧸ q) < ℵ₀ :=
    trdeg_lt_aleph0_of_finiteType
  have htfin' : (#t : Cardinal) < ℵ₀ := Cardinal.mk_lt_aleph0
  have htrq : Algebra.trdeg k (A ⧸ q) ≤ Algebra.trdeg B A := by
    rw [← htb.cardinalMk_eq_trdeg]
    exact (Cardinal.toNat_le_iff_le_of_lt_aleph0 htrqfin htfin').mp <| by
      simpa using htrNat
  have hdimq : Variety.dimension f.kernelClosedSubgroup.carrierVariety =
      Algebra.trdeg k (A ⧸ q) := by
    rw [← dimension_closedSubvariety_polynomialFunctionIdealZeroSet_of_isPrime G q]
    have hqg : q ≤ (G.pointPrime g).asIdeal := by
      rw [← hMg]
      exact hqM
    exact (fiber_minimalPrime_dimension_eq_kernel f g q hq hqg).symm
  have hKle : Variety.dimension f.kernelClosedSubgroup.carrierVariety ≤
      Algebra.trdeg B A := by
    rw [hdimq]
    exact htrq
  have hNJ : N.map (algebraMap B A) = J := by
    rfl
  let πJ : A →+* A ⧸ J := Ideal.Quotient.mk J
  let Mbar : Ideal (A ⧸ J) := M.map πJ
  have hcomapBotJ : (⊥ : Ideal (A ⧸ J)).comap πJ = J := by
    change RingHom.ker πJ = J
    dsimp only [πJ]
    exact Ideal.mk_ker
  have hMbarmax : Mbar.IsMaximal := by
    dsimp only [Mbar]
    apply Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker]
    exact hJM
  let : Mbar.IsMaximal := hMbarmax
  let : Mbar.IsPrime := hMbarmax.isPrime
  have hfiberheight : Mbar.height ≤
      (Cardinal.toNat
        (Variety.dimension f.kernelClosedSubgroup.carrierVariety) : ℕ∞) := by
    apply height_le_of_minimalPrimes_quotient_height_le
    intro qbar hqbar hqbarM
    let : qbar.IsPrime := hqbar.isPrime
    let q0 : Ideal A := qbar.comap πJ
    have hq0prime : q0.IsPrime := Ideal.comap_isPrime πJ qbar
    let : q0.IsPrime := hq0prime
    have hJq0 : J ≤ q0 := by
      change J ≤ qbar.comap πJ
      intro a ha
      change πJ a ∈ qbar
      have hzero : πJ a = 0 := by
        dsimp only [πJ]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
      rw [hzero]
      exact qbar.zero_mem
    have hq0min : q0 ∈ J.minimalPrimes := by
      change qbar.comap πJ ∈ J.minimalPrimes
      have hmin : qbar.comap πJ ∈
          ((⊥ : Ideal (A ⧸ J)).comap πJ).minimalPrimes :=
        Ideal.minimalPrimes_comap_of_surjective
        (f := πJ) Ideal.Quotient.mk_surjective hqbar
      exact Eq.mp
        (congrArg (fun I : Ideal A => qbar.comap πJ ∈ I.minimalPrimes)
          hcomapBotJ)
        hmin
    have hq0M : q0 ≤ M := by
      have hcomapM : (M.map πJ).comap πJ = M := by
        rw [Ideal.comap_map_of_surjective πJ Ideal.Quotient.mk_surjective,
          hcomapBotJ]
        exact sup_eq_left.mpr hJM
      exact (Ideal.comap_mono (f := πJ) hqbarM).trans_eq hcomapM
    have hq0g : q0 ≤ (G.pointPrime g).asIdeal := by
      rw [← hMg]
      exact hq0M
    have hdimq0 : Variety.dimension f.kernelClosedSubgroup.carrierVariety =
        Algebra.trdeg k (A ⧸ q0) := by
      rw [← dimension_closedSubvariety_polynomialFunctionIdealZeroSet_of_isPrime G q0]
      exact (fiber_minimalPrime_dimension_eq_kernel f g q0 hq0min hq0g).symm
    have hmapq0 : q0.map πJ = qbar := by
      exact Ideal.map_comap_of_surjective πJ Ideal.Quotient.mk_surjective qbar
    let e0 : ((A ⧸ J) ⧸ qbar) ≃ₐ[k]
        ((A ⧸ J) ⧸ q0.map (Ideal.Quotient.mkₐ k J)) :=
      Ideal.quotientEquivAlgOfEq k hmapq0.symm
    let e1 : ((A ⧸ J) ⧸ q0.map (Ideal.Quotient.mkₐ k J)) ≃ₐ[k]
        A ⧸ q0 := DoubleQuot.quotQuotEquivQuotOfLEₐ k hJq0
    let e := e0.trans e1
    have htrnested : Algebra.trdeg k ((A ⧸ J) ⧸ qbar) =
        Algebra.trdeg k (A ⧸ q0) := e.trdeg_eq
    have hqbarMmax :
        (Mbar.map (Ideal.Quotient.mk qbar)).IsMaximal := by
      apply Ideal.IsMaximal.map_of_surjective_of_ker_le
        Ideal.Quotient.mk_surjective
      rw [Ideal.mk_ker]
      exact hqbarM
    let : (Mbar.map (Ideal.Quotient.mk qbar)).IsMaximal := hqbarMmax
    let : Algebra.FiniteType k (A ⧸ J) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k J)
        Ideal.Quotient.mk_surjective
    let : Algebra.FiniteType k ((A ⧸ J) ⧸ qbar) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k qbar)
        Ideal.Quotient.mk_surjective
    rw [domain_maximal_height_eq_trdeg (k := k) ((A ⧸ J) ⧸ qbar)
      (Mbar.map (Ideal.Quotient.mk qbar)), htrnested, ← hdimq0]
  have hMNlies : M.LiesOver N := ⟨hMN.symm⟩
  let : M.LiesOver N := hMNlies
  have hheightMain : M.height ≤ N.height + Mbar.height := by
    have h := Ideal.height_le_height_add_of_liesOver N M
    rw [hNJ] at h
    simpa only [Mbar, πJ] using h
  have hheightTotal : M.height ≤ N.height +
      (Cardinal.toNat
        (Variety.dimension f.kernelClosedSubgroup.carrierVariety) : ℕ∞) :=
    hheightMain.trans (add_le_add_right hfiberheight N.height)
  have hNatTotal : Cardinal.toNat (Algebra.trdeg k A) ≤
      Cardinal.toNat (Algebra.trdeg k B) +
        Cardinal.toNat
          (Variety.dimension f.kernelClosedSubgroup.carrierVariety) := by
    have h' : (Cardinal.toNat (Algebra.trdeg k A) : ℕ∞) ≤
        (Cardinal.toNat (Algebra.trdeg k B) : ℕ∞) +
          (Cardinal.toNat
            (Variety.dimension f.kernelClosedSubgroup.carrierVariety) : ℕ∞) := by
      rw [← domain_maximal_height_eq_trdeg A M,
        ← domain_maximal_height_eq_trdeg B N]
      exact hheightTotal
    exact_mod_cast h'
  have hAfin : Algebra.trdeg k A < ℵ₀ := trdeg_lt_aleph0_of_finiteType
  have hBfin : Algebra.trdeg k B < ℵ₀ := trdeg_lt_aleph0_of_finiteType
  have hrelfin : Algebra.trdeg B A < ℵ₀ := trdeg_lt_aleph0_of_finiteType
  have hKfin : Variety.dimension f.kernelClosedSubgroup.carrierVariety < ℵ₀ :=
    variety_dimension_lt_aleph0 f.kernelClosedSubgroup.carrierVariety
  have htower : Algebra.trdeg k A =
      Algebra.trdeg k B + Algebra.trdeg B A :=
    (trdeg_add_eq (R := k) (S := B) (A := A)).symm
  have htowerNat : Cardinal.toNat (Algebra.trdeg k A) =
      Cardinal.toNat (Algebra.trdeg k B) +
        Cardinal.toNat (Algebra.trdeg B A) := by
    rw [htower, Cardinal.toNat_add hBfin hrelfin]
  have hrelNat : Cardinal.toNat (Algebra.trdeg B A) ≤
      Cardinal.toNat
        (Variety.dimension f.kernelClosedSubgroup.carrierVariety) := by
    rw [htowerNat] at hNatTotal
    exact Nat.le_of_add_le_add_left hNatTotal
  have hrelle : Algebra.trdeg B A ≤
      Variety.dimension f.kernelClosedSubgroup.carrierVariety :=
    (Cardinal.toNat_le_iff_le_of_lt_aleph0 hrelfin hKfin).mp hrelNat
  have hKrel : Variety.dimension f.kernelClosedSubgroup.carrierVariety =
      Algebra.trdeg B A := le_antisymm hKle hrelle
  rw [dimension_eq_trdeg_polynomialFunction_of_isIrreducible G hGi,
    dimension_eq_trdeg_polynomialFunction_of_isIrreducible H hHi,
    hKrel]
  exact htower

set_option maxHeartbeats 800000 in
/-- Proposition 1.1.6(e): the dimension of an algebraic group is the sum of
its kernel dimension and the dimension of its closed image under a morphism. -/
public lemma morphism_dimension_eq_kernel_add_image
    {k : Type u} [Field k] [IsAlgClosed k]
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) :
    Variety.dimension G =
      Variety.dimension f.kernelClosedSubgroup.carrierVariety +
        Variety.dimension f.imageClosedSubgroup.carrierVariety := by
  let I := f.imageClosedSubgroup
  have hfI_mem (x : Variety.Point G) : f.onPoints x ∈ I.toSubgroup := by
    change f.onPoints x ∈ f.image
    exact ⟨x, rfl⟩
  let fI : AlgebraicGroup.Morphism G I.carrierVariety :=
    AlgebraicGroup.Morphism.codRestrictClosedSubgroup f I hfI_mem
  have hfI_surj : Function.Surjective fI.onPoints := by
    intro y
    have hy : I.inclusion.onPoints y ∈ f.image := (I.pointEquiv y).property
    rcases hy with ⟨x, hx⟩
    refine ⟨x, I.inclusion_injective ?_⟩
    rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
    exact hx
  let G₀ := AlgebraicGroup.identityComponentClosedSubgroup G
  let r : AlgebraicGroup.Morphism G₀.carrierVariety I.carrierVariety :=
    fI.comp G₀.inclusion
  let J := r.imageClosedSubgroup
  let : AlgebraicGroup J.carrierVariety :=
    ClosedSubgroup.carrierAlgebraicGroup J
  have hrJ_mem (x : Variety.Point G₀.carrierVariety) :
      r.onPoints x ∈ J.toSubgroup := by
    change r.onPoints x ∈ r.image
    exact ⟨x, rfl⟩
  let rJ : AlgebraicGroup.Morphism G₀.carrierVariety J.carrierVariety :=
    AlgebraicGroup.Morphism.codRestrictClosedSubgroup r J hrJ_mem
  have hrJ_surj : Function.Surjective rJ.onPoints := by
    intro y
    have hy : J.inclusion.onPoints y ∈ r.image := (J.pointEquiv y).property
    rcases hy with ⟨x, hx⟩
    refine ⟨x, J.inclusion_injective ?_⟩
    rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
    exact hx
  have hG₀conn : Variety.IsConnected G₀.carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph G₀.isZariskiClosed
    have hcarrier : (G₀ : Set (Variety.Point G)) =
        AlgebraicGroup.identityComponent G := by
      ext x
      rfl
    have hconn : _root_.IsConnected (G₀ : Set (Variety.Point G)) := by
      rw [hcarrier]
      exact AlgebraicGroup.identityComponent_isConnected G
    let : ConnectedSpace {x : Variety.Point G // x ∈ (G₀ : Set (Variety.Point G))} :=
      Subtype.connectedSpace hconn
    let : ConnectedSpace (Variety.Point G₀.carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  have hcore := connected_surjective_morphism_dimension rJ hG₀conn hrJ_surj
  have hdimJ : Variety.dimension J.carrierVariety =
      Variety.dimension I.carrierVariety := by
    have hJmap : J.toSubgroup = G₀.toSubgroup.map fI.onPoints := by
      ext y
      constructor
      · intro hy
        change y ∈ r.image at hy
        rcases hy with ⟨x, hx⟩
        refine ⟨G₀.inclusion.onPoints x, (G₀.pointEquiv x).property, ?_⟩
        exact hx
      · rintro ⟨x, hx, rfl⟩
        change fI.onPoints x ∈ r.image
        let x₀ : Variety.Point G₀.carrierVariety := G₀.pointEquiv.symm ⟨x, hx⟩
        refine ⟨x₀, ?_⟩
        change fI.onPoints (G₀.inclusion.onPoints x₀) = fI.onPoints x
        apply congrArg fI.onPoints
        change (G₀.pointEquiv x₀).val = x
        dsimp only [x₀]
        rw [G₀.pointEquiv.apply_symm_apply]
    let : G₀.toSubgroup.Normal := by
      simpa [G₀] using
        AlgebraicGroup.identityComponentClosedSubgroup_isNormal G
    have hJnormal : J.toSubgroup.Normal := by
      rw [hJmap]
      exact Subgroup.Normal.map inferInstance fI.onPoints hfI_surj
    let : J.toSubgroup.Normal := hJnormal
    have hG₀J : G₀.toSubgroup ≤ J.toSubgroup.comap fI.onPoints := by
      rw [hJmap]
      exact Subgroup.le_comap_map (f := fI.onPoints) G₀.toSubgroup
    let q : (Variety.Point G ⧸ G₀.toSubgroup) →*
        (Variety.Point I.carrierVariety ⧸ J.toSubgroup) :=
      QuotientGroup.map G₀.toSubgroup J.toSubgroup fI.onPoints hG₀J
    have hqsurj : Function.Surjective q := by
      apply QuotientGroup.map_surjective_of_surjective
      · intro z
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective J.toSubgroup z
        obtain ⟨x, rfl⟩ := hfI_surj y
        exact ⟨x, rfl⟩
    let : G₀.toSubgroup.FiniteIndex := by
      simpa [G₀, AlgebraicGroup.identityComponentClosedSubgroup_carrier] using
        AlgebraicGroup.identityComponentSubgroup_finiteIndex G
    let : Finite (Variety.Point G ⧸ G₀.toSubgroup) :=
      Subgroup.finite_quotient_of_finiteIndex
    let : Finite (Variety.Point I.carrierVariety ⧸ J.toSubgroup) :=
      Finite.of_surjective q hqsurj
    let : J.toSubgroup.FiniteIndex :=
      J.toSubgroup.finiteIndex_of_finite_quotient
    exact (closedSubgroup_dimension_eq_iff_contains_identityComponent I.carrierVariety J).2
      (identityComponent_subset_of_finiteIndexSubgroup I.carrierVariety J)
  have hdimKernel : Variety.dimension rJ.kernelClosedSubgroup.carrierVariety =
      Variety.dimension f.kernelClosedSubgroup.carrierVariety := by
    let K := f.kernelClosedSubgroup
    let L := rJ.kernelClosedSubgroup
    let : AlgebraicGroup L.carrierVariety :=
      ClosedSubgroup.carrierAlgebraicGroup L
    let KG₀sub : Subgroup (Variety.Point K.carrierVariety) :=
      G₀.toSubgroup.comap K.inclusion.onPoints
    have hKG₀closed : IsZariskiClosed K.carrierVariety
        (KG₀sub : Set (Variety.Point K.carrierVariety)) := by
      change IsZariskiClosed K.carrierVariety
        (K.inclusion.onPoints ⁻¹' (G₀.toSubgroup : Set (Variety.Point G)))
      exact K.inclusion.toVariety.isZariskiClosed_preimage G₀.isZariskiClosed
    let KG₀ : ClosedSubgroup K.carrierVariety :=
      ClosedSubgroup.ofSubgroup KG₀sub hKG₀closed
    let : AlgebraicGroup KG₀.carrierVariety :=
      ClosedSubgroup.carrierAlgebraicGroup KG₀
    have hKidentity : AlgebraicGroup.identityComponent K.carrierVariety ⊆
        (KG₀.toSubgroup : Set (Variety.Point K.carrierVariety)) := by
      intro x hx
      change K.inclusion.onPoints x ∈ G₀.toSubgroup
      change K.inclusion.onPoints x ∈ AlgebraicGroup.identityComponent G
      exact K.inclusion.image_identityComponent_subset ⟨x, hx, rfl⟩
    have hdimKG₀ : Variety.dimension KG₀.carrierVariety =
        Variety.dimension K.carrierVariety :=
      (closedSubgroup_dimension_eq_iff_contains_identityComponent K.carrierVariety KG₀).2 hKidentity
    let aG : AlgebraicGroup.Morphism KG₀.carrierVariety G :=
      K.inclusion.comp KG₀.inclusion
    have haG₀_mem (x : Variety.Point KG₀.carrierVariety) :
        aG.onPoints x ∈ G₀.toSubgroup := by
      have hx := (KG₀.pointEquiv x).property
      change K.inclusion.onPoints (KG₀.inclusion.onPoints x) ∈ G₀.toSubgroup at hx
      exact hx
    let aG₀ : AlgebraicGroup.Morphism KG₀.carrierVariety G₀.carrierVariety :=
      AlgebraicGroup.Morphism.codRestrictClosedSubgroup aG G₀ haG₀_mem
    have haL_mem (x : Variety.Point KG₀.carrierVariety) :
        aG₀.onPoints x ∈ L.toSubgroup := by
      change rJ.onPoints (aG₀.onPoints x) = 1
      apply J.inclusion_injective
      rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
      change r.onPoints (aG₀.onPoints x) = 1
      apply I.inclusion_injective
      change I.inclusion.onPoints
          (fI.onPoints (G₀.inclusion.onPoints (aG₀.onPoints x))) =
        I.inclusion.onPoints 1
      rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
      change f.onPoints (G₀.inclusion.onPoints (aG₀.onPoints x)) = 1
      rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
      have hxK := (K.pointEquiv (KG₀.inclusion.onPoints x)).property
      change f.onPoints (K.inclusion.onPoints (KG₀.inclusion.onPoints x)) = 1 at hxK
      exact hxK
    let a : AlgebraicGroup.Morphism KG₀.carrierVariety L.carrierVariety :=
      AlgebraicGroup.Morphism.codRestrictClosedSubgroup aG₀ L haL_mem
    let bG : AlgebraicGroup.Morphism L.carrierVariety G :=
      G₀.inclusion.comp L.inclusion
    have hbK_mem (y : Variety.Point L.carrierVariety) :
        bG.onPoints y ∈ K.toSubgroup := by
      have hy := (L.pointEquiv y).property
      change rJ.onPoints (L.inclusion.onPoints y) = 1 at hy
      have hyJ := congrArg J.inclusion.onPoints hy
      rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply] at hyJ
      change r.onPoints (L.inclusion.onPoints y) = 1 at hyJ
      have hyI := congrArg I.inclusion.onPoints hyJ
      change I.inclusion.onPoints
          (fI.onPoints (G₀.inclusion.onPoints (L.inclusion.onPoints y))) =
        I.inclusion.onPoints 1 at hyI
      rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply] at hyI
      exact hyI
    let bK : AlgebraicGroup.Morphism L.carrierVariety K.carrierVariety :=
      AlgebraicGroup.Morphism.codRestrictClosedSubgroup bG K hbK_mem
    have hbKG₀_mem (y : Variety.Point L.carrierVariety) :
        bK.onPoints y ∈ KG₀.toSubgroup := by
      change K.inclusion.onPoints (bK.onPoints y) ∈ G₀.toSubgroup
      rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
      exact (G₀.pointEquiv (L.inclusion.onPoints y)).property
    let b : AlgebraicGroup.Morphism L.carrierVariety KG₀.carrierVariety :=
      AlgebraicGroup.Morphism.codRestrictClosedSubgroup bK KG₀ hbKG₀_mem
    let e : AlgebraicGroup.Iso KG₀.carrierVariety L.carrierVariety := by
      refine
        { hom := a
          inv := b
          hom_inv_id := ?_
          inv_hom_id := ?_ }
      · intro x
        apply KG₀.inclusion_injective
        apply K.inclusion_injective
        rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
        rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
        change G₀.inclusion.onPoints (L.inclusion.onPoints (a.onPoints x)) =
          K.inclusion.onPoints (KG₀.inclusion.onPoints x)
        rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
        rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
        rfl
      · intro y
        apply L.inclusion_injective
        apply G₀.inclusion_injective
        rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
        rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
        change K.inclusion.onPoints (KG₀.inclusion.onPoints (b.onPoints y)) =
          G₀.inclusion.onPoints (L.inclusion.onPoints y)
        rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
        rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
        rfl
    calc
      Variety.dimension L.carrierVariety = Variety.dimension KG₀.carrierVariety :=
        (algebraicGroupIso_dimension_eq e).symm
      _ = Variety.dimension K.carrierVariety := hdimKG₀
  rw [AlgebraicGroup.dimension_identityComponentClosedSubgroup G] at hcore
  rw [hdimJ, hdimKernel] at hcore
  simpa [I, add_comm] using hcore

end

end Theory.AlgebraicGroup
