module

public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.GradedAlgebra.FiniteType
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Polynomial.HilbertPoly
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# A graded Hilbert--Serre interface

This module records the numerical-polynomial language needed by the local
Hilbert--Samuel development and proves the Hilbert--Serre series formula for a
standard natural-number graded algebra.  The constructor
`HilbertSeriesCertificate.ofGenerators` presents the algebra as a quotient of
a polynomial ring on a specified finite set of degree-one generators and
performs the Stacks Project induction on those variables; the
`ofStandardGenerators` wrapper chooses such a set when its size is irrelevant. For the last
variable, its kernel and cokernel inherit decomposed gradings over the smaller
polynomial ring; additivity of module length gives the coefficient recurrence,
and multiplication by `1 - X` gives the corresponding power-series identity.
`gradedHilbertSerre` then applies `Polynomial.hilbertPoly` to the certificate.

The finite-difference lemmas prove the exact degree drop: Taylor's first
difference has lower degree, and its top iterated forward difference is
nonzero.  The graded assumptions use Mathlib's `GradedRing`,
`SetLike.GradedSMul`, `DirectSum.Decomposition`, module length, and
`Polynomial.hilbertPoly` APIs, and are arranged so an associated graded ring
over an Artinian degree-zero coefficient ring can instantiate them.
-/

open Filter
open scoped fwdDiff Polynomial PowerSeries

set_option maxHeartbeats 800000

@[expose] public section

namespace NumericalPolynomial

noncomputable section

/-- A rational polynomial agrees eventually with an integer-valued sequence. -/
def EventuallyRepresents (P : ℚ[X]) (f : ℕ → ℤ) : Prop :=
  ∀ᶠ (n : ℕ) in atTop, P.eval (n : ℚ) = (f n : ℚ)

/-- An integer-valued sequence has eventual numerical-polynomial degree `d`. -/
def HasDegree (f : ℕ → ℤ) (d : ℕ) : Prop :=
  ∃ P : ℚ[X], P ≠ 0 ∧ P.natDegree = d ∧ EventuallyRepresents P f

/-- The polynomial realizing the first forward difference of a sequence. -/
def forwardDifference (P : ℚ[X]) : ℚ[X] :=
  P.taylor 1 - P

lemma eval_forwardDifference (P : ℚ[X]) (x : ℚ) :
    (forwardDifference P).eval x = P.eval (x + 1) - P.eval x := by
  simp [forwardDifference, Polynomial.eval_sub, Polynomial.taylor_eval]

lemma eventuallyRepresents_forwardDifference {P : ℚ[X]} {f : ℕ → ℤ}
    (hP : EventuallyRepresents P f) :
    EventuallyRepresents (forwardDifference P) (fun n ↦ f (n + 1) - f n) := by
  rw [EventuallyRepresents, eventually_atTop] at hP ⊢
  obtain ⟨N, hN⟩ := hP
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [eval_forwardDifference, show (n : ℚ) + 1 = ((n + 1 : ℕ) : ℚ) by norm_num,
    hN n hn, hN (n + 1) (hn.trans (Nat.le_add_right n 1))]
  norm_cast

private lemma forwardDifference_eval_eq_fwdDiff (P : ℚ[X]) :
    (forwardDifference P).eval = Δ_[1] P.eval := by
  funext x
  simp [eval_forwardDifference, fwdDiff]

private lemma fwdDiff_iter_natDegree_ne_zero {P : ℚ[X]} (hP : P ≠ 0) :
    Δ_[1]^[P.natDegree] P.eval ≠ 0 := by
  rw [P.fwdDiff_iter_degree_eq_factorial]
  intro hzero
  have hzero_at_zero := congrFun hzero 0
  simp only [Pi.smul_apply, Pi.zero_apply, Pi.natCast_apply, smul_eq_mul] at hzero_at_zero
  exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hP)
    (by exact_mod_cast Nat.factorial_ne_zero P.natDegree)) hzero_at_zero

private lemma forwardDifference_ne_zero {P : ℚ[X]} (hP : P ≠ 0)
    (hpos : 0 < P.natDegree) : forwardDifference P ≠ 0 := by
  intro hzero
  apply fwdDiff_iter_natDegree_ne_zero hP
  rw [← Nat.sub_add_cancel (by omega : 1 ≤ P.natDegree), Function.iterate_succ_apply,
    ← forwardDifference_eval_eq_fwdDiff, hzero]
  have hzero_eval : (0 : ℚ[X]).eval = (0 : ℚ → ℚ) := by
    funext x
    simp
  rw [hzero_eval]
  have hstep : Δ_[1] (0 : ℚ → ℚ) = 0 := by
    funext x
    simp [fwdDiff]
  induction P.natDegree - 1 with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, hstep, ih]

lemma natDegree_forwardDifference {P : ℚ[X]} (hP : P ≠ 0)
    (hpos : 0 < P.natDegree) :
    (forwardDifference P).natDegree = P.natDegree - 1 := by
  have hdegree_lt : (forwardDifference P).degree < P.degree := by
    simpa [forwardDifference, Polynomial.degree_taylor] using
      Polynomial.degree_sub_lt_left (Polynomial.degree_taylor P 1)
        ((Polynomial.taylor_eq_zero 1 P).not.mpr hP) (Polynomial.leadingCoeff_taylor 1 P)
  have hupper : (forwardDifference P).natDegree < P.natDegree := by
    by_cases hdiff : forwardDifference P = 0
    · simp [hdiff, hpos]
    · rw [Polynomial.degree_eq_natDegree hP] at hdegree_lt
      exact (Polynomial.natDegree_lt_iff_degree_lt hdiff).2 hdegree_lt
  apply Nat.le_antisymm (by omega)
  by_contra hlower
  have hsmall : (forwardDifference P).natDegree < P.natDegree - 1 := by omega
  have hzero : Δ_[1]^[P.natDegree - 1] (forwardDifference P).eval = 0 :=
    Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hsmall
  have hzero' : Δ_[1]^[P.natDegree] P.eval = 0 := by
    rw [← Nat.sub_add_cancel (by omega : 1 ≤ P.natDegree), Function.iterate_succ_apply,
      ← forwardDifference_eval_eq_fwdDiff]
    exact hzero
  exact fwdDiff_iter_natDegree_ne_zero hP hzero'

lemma HasDegree.forwardDifference {f : ℕ → ℤ} {d : ℕ} (h : HasDegree f d)
    (hd : 0 < d) :
    HasDegree (fun n ↦ f (n + 1) - f n) (d - 1) := by
  obtain ⟨P, hP, hdegree, hrep⟩ := h
  refine ⟨NumericalPolynomial.forwardDifference P, ?_, ?_,
    eventuallyRepresents_forwardDifference hrep⟩
  · exact forwardDifference_ne_zero hP (hdegree.symm ▸ hd)
  · exact natDegree_forwardDifference hP (hdegree.symm ▸ hd) |>.trans
      (congrArg (fun n ↦ n - 1) hdegree)

end
end NumericalPolynomial

end

namespace GradedHilbert

noncomputable section

open DirectSum

@[expose] public section

/-- A finite Hilbert-series certificate for the graded component lengths.

The coefficient identity is the exact output of the standard Hilbert--Serre
induction.  Keeping it as a certificate lets associated-graded constructions
provide their own presentation while this module supplies the polynomial
conversion and all numerical consequences. -/
structure HilbertSeriesCertificate {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    (𝓜 : ℕ → Submodule R M) where
  numerator : ℚ[X]
  denominator : ℕ
  coeff_eq : ∀ᶠ n : ℕ in atTop,
    (PowerSeries.coeff n)
        ((↑numerator : ℚ⟦X⟧) *
          (PowerSeries.invOneSubPow ℚ denominator : ℚ⟦X⟧)) =
      ((Module.length R (𝓜 n)).toNat : ℚ)

end

public section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (𝓜 : ℕ → Submodule R M) [DirectSum.Decomposition 𝓜]

private def submoduleGrading (p : Submodule R M) (n : ℕ) : Submodule R p :=
  (𝓜 n).comap p.subtype

private def quotientGradingBase (p : Submodule R M) (n : ℕ) : Submodule R (M ⧸ p) :=
  (𝓜 n).map p.mkQ

private theorem submoduleGrading_isInternal (p : Submodule R M)
    (hp : p.IsHomogeneous 𝓜) :
    DirectSum.IsInternal (submoduleGrading 𝓜 p) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [← iSupIndep_map_orderIso_iff p.mapIic]
    apply iSupIndep.of_coe_Iic_comp
    simpa only [Function.comp_apply, Submodule.coe_mapIic_apply] using
      (DirectSum.Decomposition.isInternal 𝓜).submodule_iSupIndep.mono fun n => by
        change (submoduleGrading 𝓜 p n).map p.subtype ≤ 𝓜 n
        rw [Submodule.map_le_iff_le_comap]
        exact le_rfl
  · apply top_unique
    rintro x -
    let y : (i : ℕ) → p := fun i =>
      ⟨decompose 𝓜 (x : M) i, hp i x.property⟩
    have hy (i : ℕ) : y i ∈ submoduleGrading 𝓜 p i :=
      (decompose 𝓜 (x : M) i).property
    have hsum : ∑ i ∈ (decompose 𝓜 (x : M)).support, y i = x := by
      apply Subtype.ext
      simpa [y] using DirectSum.sum_support_decompose 𝓜 (x : M)
    rw [← hsum]
    exact Submodule.sum_mem _ fun i hi =>
      (le_iSup (submoduleGrading 𝓜 p) i) (hy i)

private def quotientComponentMapBase (p : Submodule R M) (n : ℕ) :
    𝓜 n →ₗ[R] quotientGradingBase 𝓜 p n where
  toFun m := ⟨p.mkQ m, ⟨m, m.property, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def quotientDecomposeMap (p : Submodule R M) :
    M →ₗ[R] ⨁ n, quotientGradingBase 𝓜 p n :=
  DFinsupp.mapRange.linearMap (quotientComponentMapBase 𝓜 p) ∘ₗ
    (decomposeLinearEquiv 𝓜).toLinearMap

omit [DirectSum.Decomposition 𝓜] in
private theorem coeLinearMap_comp_mapRange_quotient (p : Submodule R M) :
    (DirectSum.coeLinearMap (quotientGradingBase 𝓜 p)).comp
        (DFinsupp.mapRange.linearMap (quotientComponentMapBase 𝓜 p)) =
      p.mkQ.comp (DirectSum.coeLinearMap 𝓜) := by
  apply DirectSum.linearMap_ext
  intro n
  ext m
  rfl

private theorem quotientDecomposeMap_ker (p : Submodule R M)
    (hp : p.IsHomogeneous 𝓜) :
    p ≤ LinearMap.ker (quotientDecomposeMap 𝓜 p) := by
  intro m hm
  rw [LinearMap.mem_ker]
  ext n
  simp only [quotientDecomposeMap, LinearMap.coe_comp, Function.comp_apply]
  change p.mkQ (decompose 𝓜 m n) = 0
  exact (Submodule.Quotient.mk_eq_zero p).mpr (hp n hm)

private def quotientDecompose (p : Submodule R M) (hp : p.IsHomogeneous 𝓜) :
    (M ⧸ p) →+ ⨁ n, quotientGradingBase 𝓜 p n :=
  (p.liftQ (quotientDecomposeMap 𝓜 p) (quotientDecomposeMap_ker 𝓜 p hp)).toAddMonoidHom

private theorem quotientDecompose_mkQ (p : Submodule R M)
    (hp : p.IsHomogeneous 𝓜) (m : M) :
    quotientDecompose 𝓜 p hp (p.mkQ m) = quotientDecomposeMap 𝓜 p m := by
  rfl

@[instance_reducible] private noncomputable def quotientGradingBase_decomposition
    (p : Submodule R M)
    (hp : p.IsHomogeneous 𝓜) :
    DirectSum.Decomposition (quotientGradingBase 𝓜 p) := by
  classical
  refine DirectSum.Decomposition.ofAddHom (ℳ := quotientGradingBase 𝓜 p)
    (quotientDecompose 𝓜 p hp) ?_ ?_
  · apply AddMonoidHom.ext
    intro q
    obtain ⟨m, rfl⟩ := p.mkQ_surjective q
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
    rw [quotientDecompose_mkQ]
    change ((DirectSum.coeLinearMap (quotientGradingBase 𝓜 p)).comp
      (quotientDecomposeMap 𝓜 p)) m = p.mkQ m
    unfold quotientDecomposeMap
    rw [← LinearMap.comp_assoc, coeLinearMap_comp_mapRange_quotient,
      LinearMap.comp_assoc]
    change p.mkQ ((decomposeLinearEquiv 𝓜).symm
      (decomposeLinearEquiv 𝓜 m)) = p.mkQ m
    rw [LinearEquiv.symm_apply_apply]
  · apply DirectSum.addHom_ext
    intro n q
    ext i
    obtain ⟨m, hm, hmq⟩ := q.property
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply,
      DirectSum.coeAddMonoidHom_of]
    rw [← hmq, quotientDecompose_mkQ]
    simp only [quotientDecomposeMap, LinearMap.coe_comp, Function.comp_apply]
    change p.mkQ (decompose 𝓜 m i) =
      ((DirectSum.of (fun i => quotientGradingBase 𝓜 p i) n q) i : M ⧸ p)
    by_cases hin : i = n
    · subst i
      rw [decompose_of_mem_same 𝓜 hm]
      simp [hmq]
    · rw [decompose_of_mem_ne 𝓜 hm (Ne.symm hin)]
      rw [DirectSum.of_eq_of_ne _ _ _ hin]
      rfl

private def quotientGrading {S : Type*} [CommRing S] [Algebra R S] [Module S M]
    [IsScalarTower R S M] (p : Submodule S M) (n : ℕ) : Submodule R (M ⧸ p) :=
  (quotientGradingBase 𝓜 (p.restrictScalars R) n).map
    (Submodule.Quotient.restrictScalarsEquiv R p).toLinearMap

omit [DirectSum.Decomposition 𝓜] in
private theorem quotientGrading_eq_map_mkQ {S : Type*} [CommRing S] [Algebra R S]
    [Module S M] [IsScalarTower R S M] (p : Submodule S M) (n : ℕ) :
    quotientGrading 𝓜 p n = (𝓜 n).map (p.mkQ.restrictScalars R) := by
  ext q
  constructor
  · rintro ⟨qR, ⟨m, hm, hmq⟩, hq⟩
    refine ⟨m, hm, ?_⟩
    rw [← hq, ← hmq]
    rfl
  · rintro ⟨m, hm, rfl⟩
    refine ⟨(p.restrictScalars R).mkQ m, ?_, rfl⟩
    exact ⟨m, hm, rfl⟩

private def quotientComponentMap {S : Type*} [CommRing S] [Algebra R S] [Module S M]
    [IsScalarTower R S M] (p : Submodule S M) (n : ℕ) :
    𝓜 n →ₗ[R] quotientGrading 𝓜 p n where
  toFun m := ⟨p.mkQ m, by
    rw [quotientGrading_eq_map_mkQ]
    exact ⟨m, m.property, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[instance_reducible] private noncomputable def quotientGrading_decomposition
    {S : Type*} [CommRing S]
    [Algebra R S] [Module S M] [IsScalarTower R S M] (p : Submodule S M)
    (hp : (p.restrictScalars R).IsHomogeneous 𝓜) :
    DirectSum.Decomposition (quotientGrading 𝓜 p) := by
  classical
  let pR := p.restrictScalars R
  let e := Submodule.Quotient.restrictScalarsEquiv R p
  letI : DirectSum.Decomposition (quotientGradingBase 𝓜 pR) :=
    quotientGradingBase_decomposition 𝓜 pR hp
  apply (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_).chooseDecomposition
  · exact (iSupIndep_map_orderIso_iff (Submodule.orderIsoMapComap e)).mpr
      (DirectSum.Decomposition.isInternal (quotientGradingBase 𝓜 pR)).submodule_iSupIndep
  · change (⨆ i, (quotientGradingBase 𝓜 pR i).map e.toLinearMap) = ⊤
    rw [← Submodule.map_iSup,
      (DirectSum.Decomposition.isInternal (quotientGradingBase 𝓜 pR)).submodule_iSup_eq_top,
      Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]

private lemma decompose_smul_succ
    {S : Type*} [CommRing S] [Algebra R S] [Module S M]
    [IsScalarTower R S M] (x : S)
    (hx : ∀ n (m : M), m ∈ 𝓜 n → x • m ∈ 𝓜 (n + 1))
    (m : M) (n : ℕ) :
    (decompose 𝓜 (x • m) (n + 1) : M) =
      x • (decompose 𝓜 m n : M) := by
  induction m using DirectSum.Decomposition.inductionOn 𝓜 with
  | zero => simp
  | homogeneous m =>
      rename_i i
      by_cases h : i = n
      · subst i
        rw [decompose_of_mem_same 𝓜 m.property,
          decompose_of_mem_same 𝓜 (hx n m m.property)]
      · rw [decompose_of_mem_ne 𝓜 m.property h,
          decompose_of_mem_ne 𝓜 (hx i m m.property) (by omega), smul_zero]
  | add a b ha hb =>
      simp only [smul_add, decompose_add]
      change (decompose 𝓜 (x • a) (n + 1) : M) +
          (decompose 𝓜 (x • b) (n + 1) : M) =
        x • ((decompose 𝓜 a n : M) + (decompose 𝓜 b n : M))
      rw [ha, hb, smul_add]

private lemma decompose_smul_zero
    {S : Type*} [CommRing S] [Algebra R S] [Module S M]
    [IsScalarTower R S M] (x : S)
    (hx : ∀ n (m : M), m ∈ 𝓜 n → x • m ∈ 𝓜 (n + 1))
    (m : M) :
    (decompose 𝓜 (x • m) 0 : M) = 0 := by
  induction m using DirectSum.Decomposition.inductionOn 𝓜 with
  | zero => simp
  | homogeneous m =>
      rename_i i
      exact decompose_of_mem_ne 𝓜 (hx i m m.property) (by omega)
  | add a b ha hb =>
      simp only [smul_add, decompose_add]
      change (decompose 𝓜 (x • a) 0 : M) +
          (decompose 𝓜 (x • b) 0 : M) = 0
      rw [ha, hb, add_zero]

private lemma ker_smul_isHomogeneous
    {S : Type*} [CommRing S] [Algebra R S] [Module S M]
    [IsScalarTower R S M] (x : S)
    (hx : ∀ n (m : M), m ∈ 𝓜 n → x • m ∈ 𝓜 (n + 1)) :
    (LinearMap.ker ((LinearMap.lsmul S M x).restrictScalars R)).IsHomogeneous 𝓜 := by
  intro n m hm
  rw [LinearMap.mem_ker] at hm ⊢
  change x • m = 0 at hm
  change x • (decompose 𝓜 m n : M) = 0
  rw [← decompose_smul_succ 𝓜 x hx, hm, decompose_zero]
  rfl

private lemma range_smul_isHomogeneous
    {S : Type*} [CommRing S] [Algebra R S] [Module S M]
    [IsScalarTower R S M] (x : S)
    (hx : ∀ n (m : M), m ∈ 𝓜 n → x • m ∈ 𝓜 (n + 1)) :
    (LinearMap.range ((LinearMap.lsmul S M x).restrictScalars R)).IsHomogeneous 𝓜 := by
  intro n m hm
  obtain ⟨y, rfl⟩ := hm
  change (decompose 𝓜 (x • y) n : M) ∈
    LinearMap.range ((LinearMap.lsmul S M x).restrictScalars R)
  cases n with
  | zero =>
      have hzero := decompose_smul_zero 𝓜 x hx y
      rw [hzero]
      exact ⟨0, by simp⟩
  | succ n =>
      rw [decompose_smul_succ 𝓜 x hx]
      exact ⟨(decompose 𝓜 y n : M), rfl⟩

/-- A polynomial numerator whose Hilbert-series coefficient identity holds in every degree. -/
private structure ExactHilbertSeriesCertificate (d : ℕ) where
  numerator : ℚ[X]
  coeff_eq : ∀ n : ℕ,
    PowerSeries.coeff n
        ((numerator : ℚ⟦X⟧) *
          (PowerSeries.invOneSubPow ℚ d : ℚ⟦X⟧)) =
      ((Module.length R (𝓜 n)).toNat : ℚ)

private noncomputable def exactHilbertSeriesCertificate_zero
    [IsArtinianRing R]
    [Module (MvPolynomial (Fin 0) R) M]
    [IsScalarTower R (MvPolynomial (Fin 0) R) M]
    [Module.Finite (MvPolynomial (Fin 0) R) M] :
    ExactHilbertSeriesCertificate 𝓜 0 := by
  let e := MvPolynomial.isEmptyAlgEquiv R (Fin 0)
  letI : Module.Finite R (MvPolynomial (Fin 0) R) :=
    Module.Finite.equiv e.toLinearEquiv.symm
  letI : Module.Finite R M := Module.Finite.trans (MvPolynomial (Fin 0) R) M
  let hsupport : {n | 𝓜 n ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep
      (DirectSum.Decomposition.isInternal 𝓜).submodule_iSupIndep
  let p : ℚ[X] := ∑ n ∈ hsupport.toFinset,
    Polynomial.monomial n ((Module.length R (𝓜 n)).toNat : ℚ)
  refine ⟨p, fun n => ?_⟩
  simp only [PowerSeries.invOneSubPow_zero, Units.val_one, mul_one,
    Polynomial.coeff_coe]
  by_cases hn : 𝓜 n = ⊥
  · rw [hn, Module.length_bot]
    have hnot : n ∉ hsupport.toFinset := by simp [hn]
    simp [p, Polynomial.coeff_monomial, hnot]
  · have hmem : n ∈ hsupport.toFinset := by simp [hn]
    simp [p, Polynomial.coeff_monomial, hmem]

private lemma quotient_mk_eq_rename_killCompl (d : ℕ)
    (p : MvPolynomial (Fin (d + 1)) R) :
    Ideal.Quotient.mk
        (Ideal.span ({MvPolynomial.X (Fin.last d)} : Set (MvPolynomial (Fin (d + 1)) R))) p =
      Ideal.Quotient.mk
        (Ideal.span ({MvPolynomial.X (Fin.last d)} : Set (MvPolynomial (Fin (d + 1)) R)))
        (MvPolynomial.rename Fin.castSucc
          (MvPolynomial.killCompl (Fin.castSucc_injective d) p)) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      cases i using Fin.lastCases with
      | last =>
          simp [MvPolynomial.killCompl]
      | cast i => simp [hp, MvPolynomial.killCompl]

private theorem quotientRename_surjective (d : ℕ) :
    Function.Surjective
      ((Ideal.Quotient.mkₐ R
          (Ideal.span ({MvPolynomial.X (Fin.last d)} : Set (MvPolynomial (Fin (d + 1)) R)))).comp
        (MvPolynomial.rename Fin.castSucc) :
        MvPolynomial (Fin d) R →ₐ[R]
          MvPolynomial (Fin (d + 1)) R ⧸
            Ideal.span ({MvPolynomial.X (Fin.last d)} : Set (MvPolynomial (Fin (d + 1)) R))) := by
  intro q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨MvPolynomial.killCompl (Fin.castSucc_injective d) p, ?_⟩
  exact (quotient_mk_eq_rename_killCompl d p).symm

private noncomputable def exactHilbertSeriesCertificate_mvPolynomial (d : ℕ)
    [IsArtinianRing R]
    [Module (MvPolynomial (Fin d) R) M]
    [IsScalarTower R (MvPolynomial (Fin d) R) M]
    [Module.Finite (MvPolynomial (Fin d) R) M]
    (hX : ∀ (i : Fin d) n (m : M), m ∈ 𝓜 n →
      (MvPolynomial.X i : MvPolynomial (Fin d) R) • m ∈ 𝓜 (n + 1))
    (hfinite : ∀ n, IsFiniteLength R (𝓜 n)) :
    ExactHilbertSeriesCertificate 𝓜 d := by
  induction d generalizing M with
  | zero => exact exactHilbertSeriesCertificate_zero 𝓜
  | succ d ih =>
      let P := MvPolynomial (Fin (d + 1)) R
      let P₀ := MvPolynomial (Fin d) R
      let x : P := MvPolynomial.X (Fin.last d)
      let T : M →ₗ[P] M := LinearMap.lsmul P M x
      let Kp : Submodule P M := LinearMap.ker T
      let K : Submodule R M := Kp.restrictScalars R
      let Qp : Submodule P M := LinearMap.range T
      let Qr : Submodule R M := Qp.restrictScalars R
      let 𝓚 : ℕ → Submodule R K := submoduleGrading 𝓜 K
      let 𝓠 : ℕ → Submodule R (M ⧸ Qp) := quotientGrading 𝓜 Qp
      have hx : ∀ n (m : M), m ∈ 𝓜 n → x • m ∈ 𝓜 (n + 1) :=
        hX (Fin.last d)
      have hKhom : K.IsHomogeneous 𝓜 := by
        simpa [K, Kp, T, P] using ker_smul_isHomogeneous 𝓜 x hx
      have hQhom : Qr.IsHomogeneous 𝓜 := by
        change (LinearMap.range T).restrictScalars R |>.IsHomogeneous 𝓜
        rw [← LinearMap.range_restrictScalars]
        simpa [T, P] using range_smul_isHomogeneous 𝓜 x hx
      letI : DirectSum.Decomposition 𝓚 :=
        (submoduleGrading_isInternal 𝓜 K hKhom).chooseDecomposition
      letI : DirectSum.Decomposition 𝓠 := quotientGrading_decomposition 𝓜 Qp hQhom
      have hKtor : Module.IsTorsionBy P K x := by
        intro k
        apply Subtype.ext
        exact k.property
      have hQtor : Module.IsTorsionBy P (M ⧸ Qp) x := by
        rw [Module.isTorsionBy_quotient_iff]
        intro m
        exact ⟨m, rfl⟩
      let I : Ideal P := Ideal.span {x}
      let B := P ⧸ I
      let φ : P₀ →ₐ[R] B :=
        (Ideal.Quotient.mkₐ R I).comp (MvPolynomial.rename Fin.castSucc)
      letI : Algebra P₀ B := φ.toRingHom.toAlgebra
      letI : IsScalarTower R P₀ B := IsScalarTower.of_algebraMap_eq fun r => by
        exact (φ.commutes r).symm
      letI : Module B K := hKtor.module
      letI : Module B (M ⧸ Qp) := hQtor.module
      letI : Module P₀ K := Module.compHom K (algebraMap P₀ B)
      letI : Module P₀ (M ⧸ Qp) := Module.compHom (M ⧸ Qp) (algebraMap P₀ B)
      letI : IsScalarTower P₀ B K := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      letI : IsScalarTower P₀ B (M ⧸ Qp) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      letI : IsScalarTower R P₀ K := IsScalarTower.of_algebraMap_smul fun r k => by
        change ((algebraMap P₀ B).comp (algebraMap R P₀)) r • k = r • k
        rw [← IsScalarTower.algebraMap_eq R P₀ B]
        exact IsScalarTower.algebraMap_smul (R := R) (A := B) r k
      letI : IsScalarTower R P₀ (M ⧸ Qp) :=
        IsScalarTower.of_algebraMap_smul fun r q => by
          change ((algebraMap P₀ B).comp (algebraMap R P₀)) r • q = r • q
          rw [← IsScalarTower.algebraMap_eq R P₀ B]
          exact IsScalarTower.algebraMap_smul (R := R) (A := B) r q
      have hφ : Function.Surjective φ := by
        simpa [φ, I, P₀, P] using quotientRename_surjective (R := R) d
      letI : Module.Finite P K :=
        Module.Finite.of_injective Kp.subtype Kp.injective_subtype
      letI : Module.Finite B K := Module.Finite.of_restrictScalars_finite P B K
      letI : Module.Finite B (M ⧸ Qp) :=
        Module.Finite.of_restrictScalars_finite P B (M ⧸ Qp)
      letI : Module.Finite P₀ K := by
        rw [Module.finite_def]
        exact Submodule.FG.restrictScalars_of_surjective Module.Finite.fg_top hφ
      letI : Module.Finite P₀ (M ⧸ Qp) := by
        rw [Module.finite_def]
        exact Submodule.FG.restrictScalars_of_surjective Module.Finite.fg_top hφ
      have hKX : ∀ (i : Fin d) n (m : K), m ∈ 𝓚 n →
          (MvPolynomial.X i : P₀) • m ∈ 𝓚 (n + 1) := by
        intro i n m hm
        have hm' : (m : M) ∈ 𝓜 n := hm
        have h := hX i.castSucc n (m : M) hm'
        change ((algebraMap P₀ B (MvPolynomial.X i)) • m : K) ∈ 𝓚 (n + 1)
        change (((Ideal.Quotient.mk I
          (MvPolynomial.rename Fin.castSucc (MvPolynomial.X i))) • m : K) : M) ∈ 𝓜 (n + 1)
        rw [Module.IsTorsionBy.mk_smul hKtor]
        change (MvPolynomial.rename Fin.castSucc (MvPolynomial.X i) : P) •
          (m : M) ∈ 𝓜 (n + 1)
        simpa using h
      have hQX : ∀ (i : Fin d) n (m : M ⧸ Qp), m ∈ 𝓠 n →
          (MvPolynomial.X i : P₀) • m ∈ 𝓠 (n + 1) := by
        intro i n q hq
        dsimp only [𝓠] at hq ⊢
        rw [quotientGrading_eq_map_mkQ] at hq ⊢
        obtain ⟨m, hm, rfl⟩ := hq
        refine ⟨(MvPolynomial.X i.castSucc : P) • m, hX i.castSucc n m hm, ?_⟩
        change Qp.mkQ ((MvPolynomial.X i.castSucc : P) • m) =
          (algebraMap P₀ B (MvPolynomial.X i)) • Qp.mkQ m
        change Qp.mkQ ((MvPolynomial.X i.castSucc : P) • m) =
          (Ideal.Quotient.mk I
            (MvPolynomial.rename Fin.castSucc (MvPolynomial.X i))) • Qp.mkQ m
        rw [Module.IsTorsionBy.mk_smul hQtor]
        simp [P]
      have hKfinite : ∀ n, IsFiniteLength R (𝓚 n) := by
        intro n
        let f : 𝓚 n →ₗ[R] 𝓜 n :=
          { toFun := fun m => ⟨(m : M), m.property⟩
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        refine (hfinite n).of_injective (f := f) ?_
        intro a b hab
        dsimp only [f] at hab
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : 𝓜 n => (z : M)) hab
      have hQfinite : ∀ n, IsFiniteLength R (𝓠 n) := by
        intro n
        let f := quotientComponentMap 𝓜 Qp n
        refine (hfinite n).of_surjective (f := f) ?_
        intro q
        obtain ⟨qR, hqR, hq⟩ := q.property
        obtain ⟨m, hm, hmq⟩ := hqR
        refine ⟨⟨m, hm⟩, ?_⟩
        apply Subtype.ext
        change Qp.mkQ m = q
        rw [← hq, ← hmq]
        rfl
      have hlengthZero :
          (Module.length R (𝓜 0)).toNat =
            (Module.length R (𝓠 0)).toNat := by
        let π : 𝓜 0 →ₗ[R] 𝓠 0 := quotientComponentMap 𝓜 Qp 0
        have hπsurj : Function.Surjective π := by
          intro q
          obtain ⟨qR, hqR, hq⟩ := q.property
          obtain ⟨m, hm, hmq⟩ := hqR
          refine ⟨⟨m, hm⟩, ?_⟩
          apply Subtype.ext
          change Qp.mkQ m = q
          rw [← hq, ← hmq]
          rfl
        have hπinj : Function.Injective π := by
          intro a b hab
          have hq : Qp.mkQ (a : M) = Qp.mkQ (b : M) :=
            congrArg Subtype.val hab
          have hqzero : Qp.mkQ ((a : M) - (b : M)) = 0 := by
            rw [map_sub, hq, sub_self]
          obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero Qp).mp hqzero
          have hy' : x • y = (a : M) - (b : M) := by
            simpa [Qp, T, x, P] using hy
          have hgrade : (a : M) - (b : M) ∈ 𝓜 0 :=
            Submodule.sub_mem _ a.property b.property
          have hzero : (a : M) - (b : M) = 0 := calc
            (a : M) - (b : M) =
                (decompose 𝓜 ((a : M) - (b : M)) 0 : M) :=
              (decompose_of_mem_same 𝓜 hgrade).symm
            _ = (decompose 𝓜 (x • y) 0 : M) := by rw [hy']
            _ = 0 := decompose_smul_zero 𝓜 x hx y
          exact Subtype.ext (sub_eq_zero.mp hzero)
        let e : 𝓜 0 ≃ₗ[R] 𝓠 0 :=
          LinearEquiv.ofBijective π ⟨hπinj, hπsurj⟩
        exact congrArg ENat.toNat e.length_eq
      have hlengthRec (n : ℕ) :
          (Module.length R (𝓜 (n + 1))).toNat +
              (Module.length R (𝓚 n)).toNat =
            (Module.length R (𝓜 n)).toNat +
              (Module.length R (𝓠 (n + 1))).toNat := by
        let μ : 𝓜 n →ₗ[R] 𝓜 (n + 1) :=
          { toFun := fun m => ⟨x • (m : M), hx n m m.property⟩
            map_add' := fun a b => by ext; simp
            map_smul' := fun r m => by
              ext
              exact (smul_comm r x (m : M)).symm }
        let κ : 𝓚 n →ₗ[R] 𝓜 n :=
          { toFun := fun k => ⟨((k : K) : M), k.property⟩
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        let ρ : μ.range →ₗ[R] 𝓜 (n + 1) := μ.range.subtype
        let π : 𝓜 (n + 1) →ₗ[R] 𝓠 (n + 1) := quotientComponentMap 𝓜 Qp (n + 1)
        have hκ : Function.Injective κ := by
          intro a b hab
          dsimp only [κ] at hab
          exact Subtype.ext (Subtype.ext (congrArg (fun z : 𝓜 n => (z : M)) hab))
        have hρ : Function.Injective ρ := by
          intro a b hab
          dsimp only [ρ] at hab
          exact Subtype.ext hab
        have hμrange : Function.Surjective μ.rangeRestrict := by
          rintro ⟨_, m, rfl⟩
          exact ⟨m, rfl⟩
        have hπ : Function.Surjective π := by
          intro q
          obtain ⟨qR, hqR, hq⟩ := q.property
          obtain ⟨m, hm, hmq⟩ := hqR
          refine ⟨⟨m, hm⟩, ?_⟩
          apply Subtype.ext
          change Qp.mkQ m = q
          rw [← hq, ← hmq]
          rfl
        have hexact₀ : Function.Exact κ μ.rangeRestrict := by
          rw [LinearMap.exact_iff]
          ext m
          constructor
          · intro hm
            rw [LinearMap.mem_ker] at hm
            have hm' : μ m = 0 := congrArg Subtype.val hm
            have hxm : x • (m : M) = 0 := congrArg Subtype.val hm'
            refine ⟨⟨⟨m, ?_⟩, m.property⟩, rfl⟩
            simpa [K, Kp, T, P] using hxm
          · rintro ⟨k, hk⟩
            rw [← hk, LinearMap.mem_ker]
            apply Subtype.ext
            apply Subtype.ext
            exact k.1.property
        have hexact₁ : Function.Exact ρ π := by
          rw [LinearMap.exact_iff]
          ext m
          constructor
          · intro hm
            rw [LinearMap.mem_ker] at hm
            have hmq : Qp.mkQ (m : M) = 0 := congrArg Subtype.val hm
            obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero Qp).mp hmq
            have hy' : x • y = (m : M) := by simpa [Qp, T, x, P] using hy
            have hmgrade : (m : M) ∈ 𝓜 (n + 1) := m.property
            let yn : 𝓜 n := ⟨decompose 𝓜 y n, (decompose 𝓜 y n).property⟩
            refine ⟨⟨μ yn, ⟨yn, rfl⟩⟩, ?_⟩
            apply Subtype.ext
            change x • (decompose 𝓜 y n : M) = (m : M)
            rw [← decompose_smul_succ 𝓜 x hx y n, hy']
            exact decompose_of_mem_same 𝓜 hmgrade
          · rintro ⟨z, hz⟩
            rw [← hz, LinearMap.mem_ker]
            obtain ⟨a, ha⟩ := z.property
            apply Subtype.ext
            change Qp.mkQ (z : M) = 0
            rw [← ha]
            exact (Submodule.Quotient.mk_eq_zero Qp).mpr ⟨a, rfl⟩
        have hlen₀ := Module.length_eq_add_of_exact κ μ.rangeRestrict hκ hμrange hexact₀
        have hlen₁ := Module.length_eq_add_of_exact ρ π hρ hπ hexact₁
        have hIfinite : IsFiniteLength R μ.range := (hfinite (n + 1)).of_injective hρ
        have hlen₀' := congrArg ENat.toNat hlen₀
        have hlen₁' := congrArg ENat.toNat hlen₁
        rw [ENat.toNat_add (Module.length_ne_top_iff.mpr (hKfinite n))
          (Module.length_ne_top_iff.mpr hIfinite)] at hlen₀'
        rw [ENat.toNat_add (Module.length_ne_top_iff.mpr hIfinite)
          (Module.length_ne_top_iff.mpr (hQfinite (n + 1)))] at hlen₁'
        omega
      obtain ⟨pK, hpK⟩ := ih 𝓚 hKX hKfinite
      obtain ⟨pQ, hpQ⟩ := ih 𝓠 hQX hQfinite
      refine ⟨pQ - Polynomial.X * pK, ?_⟩
      let F : ℚ⟦X⟧ :=
        ((pQ - Polynomial.X * pK : ℚ[X]) : ℚ⟦X⟧) *
          (PowerSeries.invOneSubPow ℚ (d + 1) : ℚ⟦X⟧)
      let FK : ℚ⟦X⟧ :=
        (pK : ℚ⟦X⟧) * (PowerSeries.invOneSubPow ℚ d : ℚ⟦X⟧)
      let FQ : ℚ⟦X⟧ :=
        (pQ : ℚ⟦X⟧) * (PowerSeries.invOneSubPow ℚ d : ℚ⟦X⟧)
      have hden :
          (1 - PowerSeries.X) *
              (PowerSeries.invOneSubPow ℚ (d + 1) : ℚ⟦X⟧) =
            (PowerSeries.invOneSubPow ℚ d : ℚ⟦X⟧) := by
        simpa using
          (PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val
            ℚ d 1)
      have hseries :
          (1 - PowerSeries.X) * F =
            FQ - PowerSeries.X * FK := by
        calc
          (1 - PowerSeries.X) * F =
              ((pQ - Polynomial.X * pK : ℚ[X]) : ℚ⟦X⟧) *
                ((1 - PowerSeries.X) *
                  (PowerSeries.invOneSubPow ℚ (d + 1) : ℚ⟦X⟧)) := by
            dsimp only [F]
            ring
          _ = ((pQ - Polynomial.X * pK : ℚ[X]) : ℚ⟦X⟧) *
                (PowerSeries.invOneSubPow ℚ d : ℚ⟦X⟧) := by rw [hden]
          _ = FQ - PowerSeries.X * FK := by
            dsimp only [FK, FQ]
            simp only [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_X]
            ring
      intro n
      change PowerSeries.coeff n F =
        ((Module.length R (𝓜 n)).toNat : ℚ)
      induction n with
      | zero =>
          have hzero := congrArg (PowerSeries.coeff 0) hseries
          simp only [sub_mul, one_mul, map_sub,
            PowerSeries.coeff_zero_X_mul, sub_zero] at hzero
          dsimp only [FQ] at hzero
          rw [hzero, hpQ 0]
          exact_mod_cast hlengthZero.symm
      | succ n hn =>
          have hsucc := congrArg (PowerSeries.coeff (n + 1)) hseries
          simp only [sub_mul, one_mul, map_sub,
            PowerSeries.coeff_succ_X_mul] at hsucc
          dsimp only [FQ, FK] at hsucc
          rw [hpQ (n + 1), hpK n] at hsucc
          have hlengthRecQ :
              ((Module.length R (𝓜 (n + 1))).toNat : ℚ) +
                  ((Module.length R (𝓚 n)).toNat : ℚ) =
                ((Module.length R (𝓜 n)).toNat : ℚ) +
                  ((Module.length R (𝓠 (n + 1))).toNat : ℚ) := by
            exact_mod_cast hlengthRec n
          rw [hn] at hsucc
          linarith

/-- Construct a Hilbert-series certificate from specified standard graded generators.

The proof presents the algebra as a quotient of a polynomial ring whose
variables correspond to the chosen degree-one generators.  It then follows the
Stacks Project Hilbert--Serre induction: multiplication by the last variable
produces graded kernel and cokernel modules over the polynomial ring with one
fewer variable.  Their exact length sequences give the coefficient recurrence,
which is assembled into the numerator identity after multiplying by
`1 - PowerSeries.X`. -/
noncomputable def HilbertSeriesCertificate.ofGenerators
    {A : Type*} [CommRing A] [Algebra R A]
    [Module A M] [IsScalarTower R A M]
    (𝒜 : ℕ → Submodule R A)
    [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 𝓜]
    [Module.Finite A M] [IsArtinianRing R]
    (s : Finset A)
    (hgen : Algebra.adjoin R (s : Set A) = ⊤)
    (hdegree : ∀ a ∈ s, a ∈ 𝒜 1)
    (hfinite : ∀ n, IsFiniteLength R (𝓜 n)) :
    HilbertSeriesCertificate 𝓜 := by
  classical
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let g : Fin (Fintype.card s) → A := fun i => e i
  let P := MvPolynomial (Fin (Fintype.card s)) R
  let f : P →ₐ[R] A := MvPolynomial.aeval g
  have hrange : Set.range g = (s : Set A) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro ha
      let a' : s := ⟨a, ha⟩
      refine ⟨e.symm a', ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply a')
  have hf : Function.Surjective f := by
    rw [← AlgHom.range_eq_top, MvPolynomial.aeval_range, hrange, hgen]
  letI : Algebra P A := f.toRingHom.toAlgebra
  letI : IsScalarTower R P A :=
    IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  letI : Module P M := Module.compHom M (algebraMap P A)
  letI : IsScalarTower P A M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : IsScalarTower R P M :=
    IsScalarTower.of_algebraMap_smul fun r m => by
      change ((algebraMap P A).comp (algebraMap R P)) r • m = r • m
      rw [← IsScalarTower.algebraMap_eq R P A]
      exact IsScalarTower.algebraMap_smul (R := R) (A := A) r m
  letI : Module.Finite P M := by
    rw [Module.finite_def]
    exact Submodule.FG.restrictScalars_of_surjective Module.Finite.fg_top hf
  have hX : ∀ (i : Fin (Fintype.card s)) n (m : M), m ∈ 𝓜 n →
      (MvPolynomial.X i : P) • m ∈ 𝓜 (n + 1) := by
    intro i n m hm
    have hgi : g i ∈ 𝒜 1 := hdegree (g i) (e i).property
    have hsmul := SetLike.GradedSMul.smul_mem hgi hm
    change f (MvPolynomial.X i) • m ∈ 𝓜 (n + 1)
    rw [MvPolynomial.aeval_X]
    simpa [add_comm] using hsmul
  obtain ⟨p, hp⟩ :=
    exactHilbertSeriesCertificate_mvPolynomial (R := R) 𝓜 (Fintype.card s) hX hfinite
  exact
    { numerator := p
      denominator := s.card
      coeff_eq := by
        simpa only [Fintype.card_coe] using Filter.Eventually.of_forall hp }

@[simp]
theorem HilbertSeriesCertificate.denominator_ofGenerators
    {A : Type*} [CommRing A] [Algebra R A]
    [Module A M] [IsScalarTower R A M]
    (𝒜 : ℕ → Submodule R A)
    [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 𝓜]
    [Module.Finite A M] [IsArtinianRing R]
    (s : Finset A)
    (hgen : Algebra.adjoin R (s : Set A) = ⊤)
    (hdegree : ∀ a ∈ s, a ∈ 𝒜 1)
    (hfinite : ∀ n, IsFiniteLength R (𝓜 n)) :
    (HilbertSeriesCertificate.ofGenerators 𝓜 𝒜 s hgen hdegree hfinite).denominator =
      s.card := by
  rw [HilbertSeriesCertificate.ofGenerators]

/-- Construct a Hilbert-series certificate from the existence of standard graded generators.

Use `HilbertSeriesCertificate.ofGenerators` when the cardinality of the chosen
generating set is needed in a subsequent degree estimate. -/
noncomputable def HilbertSeriesCertificate.ofStandardGenerators
    {A : Type*} [CommRing A] [Algebra R A]
    [Module A M] [IsScalarTower R A M]
    (𝒜 : ℕ → Submodule R A)
    [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 𝓜]
    [Module.Finite A M] [IsArtinianRing R]
    (hdegreeOne : ∃ s : Finset A,
      Algebra.adjoin R (s : Set A) = ⊤ ∧ ∀ a ∈ s, a ∈ 𝒜 1)
    (hfinite : ∀ n, IsFiniteLength R (𝓜 n)) :
    HilbertSeriesCertificate 𝓜 := by
  classical
  exact HilbertSeriesCertificate.ofGenerators 𝓜 𝒜 hdegreeOne.choose
    hdegreeOne.choose_spec.1 hdegreeOne.choose_spec.2 hfinite

end

@[expose] public section

/-- Graded Hilbert--Serre polynomiality from a finite Hilbert-series presentation.

The explicit graded hypotheses describe the standard setup: `𝒜` is a natural
number graded algebra generated by degree-one elements over the Artinian ring
`R`, `𝓜` is a decomposed graded module, and every component has finite length.
The certificate supplies the Hilbert-series identity; `hilbertPoly` then turns
it into eventual agreement with a rational polynomial. -/
theorem gradedHilbertSerre
    {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M]
    (𝒜 : ℕ → Submodule R A) (𝓜 : ℕ → Submodule R M)
    [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 𝓜]
    (_hdecomp : DirectSum.Decomposition 𝓜)
    [Module.Finite A M] [IsArtinianRing R]
    (_hdegreeOne : ∃ s : Finset A,
      Algebra.adjoin R (s : Set A) = ⊤ ∧ ∀ a ∈ s, a ∈ 𝒜 1)
    (_hfinite : ∀ n, IsFiniteLength R (𝓜 n))
    (hseries : HilbertSeriesCertificate 𝓜) :
    NumericalPolynomial.EventuallyRepresents
      (hseries.numerator.hilbertPoly hseries.denominator)
      (fun n => (Module.length R (𝓜 n)).toNat : ℕ → ℤ) := by
  rw [NumericalPolynomial.EventuallyRepresents]
  filter_upwards [hseries.coeff_eq,
    (eventually_gt_atTop hseries.numerator.natDegree)] with n hcoeff hn
  calc
    (hseries.numerator.hilbertPoly hseries.denominator).eval (n : ℚ) =
        (PowerSeries.coeff n)
          ((↑hseries.numerator : ℚ⟦X⟧) *
            (PowerSeries.invOneSubPow ℚ hseries.denominator : ℚ⟦X⟧)) :=
      (Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval
        hseries.denominator hn).symm
    _ = ((Module.length R (𝓜 n)).toNat : ℚ) := hcoeff

end

end
end GradedHilbert
