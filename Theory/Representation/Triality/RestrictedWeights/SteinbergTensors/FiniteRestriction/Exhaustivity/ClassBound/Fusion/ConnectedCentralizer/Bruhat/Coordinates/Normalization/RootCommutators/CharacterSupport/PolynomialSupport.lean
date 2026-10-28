module


public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.RootCommutators.CharacterSupport.Contracts

/-!
Mixed polynomial character support for a torus.

The proof first normalizes at a nonzero evaluation and uses the character
algebra of a torus to retain a nonzero monomial witness.  Infinite-field
polynomial evaluation and `killCompl` then force that witness to involve both
Boolean coordinate families.

Source motivation: the regular-function character support underlying GLS3,
1.12.1(b) and 1.12.7(b).
-/

open scoped BigOperators

namespace Theory.AlgebraicGroup

universe u v

variable {k : Type u} [Field k]

private lemma source_of_coeff {M : Type v} [CommMonoid M] {sigma : Type u} [Finite sigma]
    (beta : sigma → M) (z : sigma → k) (Q : MvPolynomial sigma k) (m : M)
    (h : (MvPolynomial.aeval (fun i => MonoidAlgebra.single (beta i) (z i)) Q).coeff m ≠ 0) :
    ∃ d : sigma →₀ ℕ, Q.coeff d ≠ 0 ∧ d.prod (fun i e => beta i ^ e) = m := by
  classical
  have hterm : ∃ d ∈ Q.support,
      (MvPolynomial.aeval (fun i => MonoidAlgebra.single (beta i) (z i))
        (MvPolynomial.monomial d (Q.coeff d))).coeff m ≠ 0 := by
    by_contra hn
    push Not at hn
    apply h
    rw [Q.as_sum]
    rw [map_sum]
    rw [MonoidAlgebra.coeff_sum]
    have coeff_sum_apply (s : Finset (sigma →₀ ℕ))
        (f : (sigma →₀ ℕ) → MonoidAlgebra k M) (m : M) :
        ((∑ d ∈ s, (f d).coeff) m) = ∑ d ∈ s, (f d).coeff m := by
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finsupp.add_apply, ih, Finset.sum_insert ha]
    rw [coeff_sum_apply]
    apply Finset.sum_eq_zero
    intro d hd
    exact hn d hd
  obtain ⟨d, hd, hdm⟩ := hterm
  have hcoeff : Q.coeff d ≠ 0 := Finsupp.mem_support_iff.mp hd
  refine ⟨d, hcoeff, ?_⟩
  rw [MvPolynomial.aeval_monomial] at hdm
  have hsingle :
      d.prod (fun i e => MonoidAlgebra.single (beta i) (z i) ^ e) =
      MonoidAlgebra.single (d.prod (fun i e => beta i ^ e))
        (d.prod (fun i e => z i ^ e)) := by
    rw [Finsupp.prod]
    simp_rw [MonoidAlgebra.single_pow]
    rw [MonoidAlgebra.prod_single]
    rfl
  rw [← Algebra.smul_def, hsingle, MonoidAlgebra.coeff_smul,
    MonoidAlgebra.coeff_single] at hdm
  by_contra hne
  simp [hne] at hdm

private lemma coeff_hits_erase [Infinite k] {sigma : Type u} [Finite sigma] (side : sigma → Bool)
    (e : Bool) (P : MvPolynomial sigma k)
    (herase : ∀ z : sigma → k,
      MvPolynomial.eval (fun i => if side i = e then 0 else z i) P = 0)
    {d : sigma →₀ ℕ} (hd : P.coeff d ≠ 0) :
    ∃ i ∈ d.support, side i = e := by
  classical
  let τ := {i : sigma // side i ≠ e}
  let f : τ → sigma := fun i => i.1
  have hf : Function.Injective f := Subtype.val_injective
  have hvar (w : τ → k) (i : sigma) :
      (MvPolynomial.aeval w : MvPolynomial τ k →ₐ[k] k) (MvPolynomial.killCompl hf (MvPolynomial.X i)) =
        (if h : side i = e then (0 : k) else w ⟨i, h⟩) := by
    by_cases hi : side i = e
    · have hnot : i ∉ Set.range f := by
        rintro ⟨j, rfl⟩
        exact j.2 hi
      have hex : ¬ ∃ y : τ, f y = i := by
        simpa only [Set.mem_range] using hnot
      simp [MvPolynomial.killCompl, hi, hex]
    · have hr : i ∈ Set.range f := ⟨⟨i, hi⟩, rfl⟩
      have hex : ∃ y : τ, f y = i := hr
      let y : Set.range f := ⟨i, hex⟩
      have hy : (Equiv.ofInjective f hf).symm y = ⟨i, hi⟩ := by
        apply (Equiv.symm_apply_eq _).2
        apply Subtype.ext
        rfl
      simp [MvPolynomial.killCompl, hi, hex, y, hy]
  let zfun (w : τ → k) : sigma → k :=
    fun i => if h : side i = e then (0 : k) else w ⟨i, h⟩
  have hfun (w : τ → k) (p : MvPolynomial sigma k) :
      MvPolynomial.aeval w (MvPolynomial.killCompl hf p) =
        MvPolynomial.eval (zfun w) p := by
    have heq : (MvPolynomial.aeval w : MvPolynomial τ k →ₐ[k] k).comp
          (MvPolynomial.killCompl hf) =
        (MvPolynomial.aeval (zfun w) :
          MvPolynomial sigma k →ₐ[k] k) := by
      apply MvPolynomial.algHom_ext
      intro i
      simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X, zfun] using hvar w i
    exact DFunLike.congr_fun heq p
  have hkill : MvPolynomial.killCompl hf P = 0 := by
    apply MvPolynomial.funext
    intro w
    change MvPolynomial.aeval w (MvPolynomial.killCompl hf P) = 0
    rw [hfun]
    have hz : (fun i => if side i = e then (0 : k) else zfun w i) = zfun w := by
      funext i
      by_cases hi : side i = e <;> simp [zfun, hi]
    simpa [hz] using herase (zfun w)
  by_contra hn
  have hno : ∀ i ∈ d.support, side i ≠ e := by
    intro i hi hie
    exact hn ⟨i, hi, hie⟩
  have hsub : (↑d.support : Set sigma) ⊆ Set.range f := by
    intro j hj
    exact ⟨⟨j, by
      intro hj_e
      exact hno j hj hj_e⟩, rfl⟩
  let s : τ →₀ ℕ := d.comapDomain f hf.injOn
  have hmap : s.mapDomain f = d := by
    exact Finsupp.mapDomain_comapDomain f hf d hsub
  have hc : (MvPolynomial.killCompl hf P).coeff s = P.coeff d := by
    rw [MvPolynomial.coeff_killCompl, hmap]
  rw [hkill] at hc
  exact hd hc.symm
private lemma affine_char_with_source
    {T : Variety k} [AlgebraicGroup T] [IsAlgClosed k] (hT : IsTorus T)
    {sigma : Type u} [Finite sigma]
    (beta : sigma → TorusCharacter T) (z : sigma → k)
    (Q : MvPolynomial sigma k) (alpha : TorusCharacter T)
    (hQ : ∀ s : Variety.Point T,
      MvPolynomial.eval (fun i => (beta i).pointCharacter s * z i) Q =
        alpha.pointCharacter s) :
    ∃ d : sigma →₀ ℕ, Q.coeff d ≠ 0 ∧
      alpha = d.prod (fun i e => beta i ^ e) := by
  classical
  let M : Submonoid (TorusCharacter T) :=
    Submonoid.closure (Set.range beta)
  let vars : sigma → MonoidAlgebra k M := fun i =>
    MonoidAlgebra.single
      (show M from ⟨beta i,
        Submonoid.subset_closure (Set.mem_range_self i)⟩) (z i)
  let qM : MonoidAlgebra k M := MvPolynomial.aeval vars Q
  let mapCharacters : MonoidAlgebra k M →ₐ[k]
      MonoidAlgebra k (TorusCharacter T) :=
    MonoidAlgebra.mapDomainAlgHom k k M.subtype
  let eT := torusCharacterAlgebraEquiv T
    hT.isMulCommutative (IsTorus.all_semisimple hT)
  have heTsingle (chi : TorusCharacter T) (c : k) :
      eT (MonoidAlgebra.single chi c) =
        c • chi.scalarPolynomialFunction := by
    change
      ((MonoidAlgebra.lift k (Variety.PolynomialFunction T)
        (TorusCharacter T))
        (TorusCharacter.scalarPolynomialFunctionMonoidHom T))
        (MonoidAlgebra.single chi c) = _
    rw [MonoidAlgebra.lift_single]
    rfl
  let targetVariables : sigma → Variety.PolynomialFunction T := fun i =>
    z i • (beta i).scalarPolynomialFunction
  have hmap : eT (mapCharacters qM) =
      MvPolynomial.aeval targetVariables Q := by
    have hhom : (eT.toAlgHom.comp mapCharacters).comp
        (MvPolynomial.aeval vars) =
        MvPolynomial.aeval targetVariables := by
      apply MvPolynomial.algHom_ext
      intro i
      have hi : eT.toAlgHom (mapCharacters (vars i)) =
          targetVariables i := by
        rw [show mapCharacters (vars i) =
            MonoidAlgebra.single (beta i) (z i) by
          simp [mapCharacters, vars]]
        exact heTsingle (beta i) (z i)
      simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using hi
    exact DFunLike.congr_fun hhom Q
  have htarget : MvPolynomial.aeval targetVariables Q =
      alpha.scalarPolynomialFunction := by
    apply Variety.PolynomialFunction.ext
    intro s
    rw [TorusCharacter.scalarPolynomialFunction_apply]
    let ev : Variety.PolynomialFunction T →+* k :=
      { toFun := fun f => f s
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have heval := MvPolynomial.map_aeval targetVariables ev Q
    change (MvPolynomial.aeval targetVariables Q) s = _
    rw [← show ev (MvPolynomial.aeval targetVariables Q) =
        (MvPolynomial.aeval targetVariables Q) s by rfl, heval]
    change MvPolynomial.eval₂ _
      (fun i => (z i • (beta i).scalarPolynomialFunction) s) Q = _
    have hscalar : ev.comp
        (algebraMap k (Variety.PolynomialFunction T)) = RingHom.id k := by
      apply RingHom.ext
      intro r
      exact polynomialFunction_algebraMap_apply T r s
    rw [hscalar, MvPolynomial.eval₂_id]
    simp only [polynomialFunction_smul_apply,
      TorusCharacter.scalarPolynomialFunction_apply]
    simpa [mul_comm] using hQ s
  have hsingle : eT (MonoidAlgebra.single alpha 1) =
      alpha.scalarPolynomialFunction := by
    simpa using heTsingle alpha 1
  have hq : mapCharacters qM = MonoidAlgebra.single alpha 1 := by
    apply eT.injective
    rw [hmap, htarget, hsingle]
  have hcoeff : (mapCharacters qM).coeff alpha ≠ 0 := by
    rw [hq]
    simp
  have hcoeff' : (Finsupp.mapDomain M.subtype qM.coeff) alpha ≠ 0 := by
    simpa only [mapCharacters, MonoidAlgebra.mapDomainAlgHom_apply,
      MonoidAlgebra.mapDomain] using hcoeff
  obtain ⟨alphaM, halphaM⟩ :=
    Finsupp.mem_range_of_mapDomain_ne_zero hcoeff'
  have hqm : qM.coeff alphaM ≠ 0 := by
    intro hh
    apply hcoeff'
    rw [← halphaM, Finsupp.mapDomain_apply (Submonoid.subtype_injective M)]
    exact hh
  let betaM : sigma → M := fun i =>
    ⟨beta i, Submonoid.subset_closure (Set.mem_range_self i)⟩
  obtain ⟨d, hd, hprod⟩ := source_of_coeff betaM z Q alphaM (by
    simpa [vars, betaM] using hqm)
  refine ⟨d, hd, ?_⟩
  calc
    alpha = M.subtype alphaM := halphaM.symm
    _ = d.prod (fun i e => M.subtype ((betaM i) ^ e)) := by
      rw [Finsupp.prod]
      rw [← map_prod M.subtype]
      exact (congrArg Subtype.val hprod).symm
    _ = d.prod (fun i e => beta i ^ e) := by simp [betaM]

public theorem mixedPolynomialCharacterSupport_of_isTorus
    (T : Variety k) [AlgebraicGroup T] [IsAlgClosed k] (hT : IsTorus T) :
    MixedPolynomialCharacterSupport T := by

  intro sigma inst side a b c P hnonzero hscale herase
  classical
  obtain ⟨z, hz⟩ := hnonzero
  let d0 : k := MvPolynomial.eval z P
  let Q : MvPolynomial sigma k := d0⁻¹ • P
  have hd0 : d0 ≠ 0 := hz
  have hQscale : ∀ s : Variety.Point T,
      MvPolynomial.eval
        (fun i => (if side i then a else b).pointCharacter s * z i) Q =
          c.pointCharacter s := by
    intro s
    dsimp [Q]
    change MvPolynomial.aeval
      (fun i => (if side i then a else b).pointCharacter s * z i)
      (d0⁻¹ • P) = c.pointCharacter s
    rw [MulActionSemiHomClass.map_smulₛₗ]
    change d0⁻¹ * MvPolynomial.eval
      (fun i => (if side i then a else b).pointCharacter s * z i) P =
        c.pointCharacter s
    rw [hscale s z]
    field_simp [d0]
    exact mul_comm _ _
  obtain ⟨d, hdQ, hchar⟩ := affine_char_with_source
    (T := T) (hT := hT) (fun i => if side i then a else b) z Q c hQscale
  have hdP : P.coeff d ≠ 0 := by
    simpa [Q, d0, hd0] using hdQ
  have hsideT := coeff_hits_erase side true P (herase true) hdP
  have hsideF := coeff_hits_erase side false P (herase false) hdP
  obtain ⟨i, hi, hit⟩ := hsideT
  obtain ⟨j, hj, hij⟩ := hsideF
  let I : ℕ := ∑ x ∈ d.support, if side x then d x else 0
  let J : ℕ := ∑ x ∈ d.support, if side x then 0 else d x
  refine ⟨I, J, ?_, ?_, ?_⟩
  · dsimp [I]
    have hdi : 0 < d i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
    have hle : (if side i then d i else 0) ≤
        ∑ x ∈ d.support, if side x then d x else 0 :=
      Finset.single_le_sum (f := fun x => if side x then d x else 0)
        (fun _ _ => Nat.zero_le _) hi
    have hle' : d i ≤ ∑ x ∈ d.support, if side x then d x else 0 := by
      simpa [hit] using hle
    exact lt_of_lt_of_le hdi hle'
  · dsimp [J]
    have hdj : 0 < d j := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj)
    have hle : (if side j then 0 else d j) ≤
        ∑ x ∈ d.support, if side x then 0 else d x :=
      Finset.single_le_sum (f := fun x => if side x then 0 else d x)
        (fun _ _ => Nat.zero_le _) hj
    have hle' : d j ≤ ∑ x ∈ d.support, if side x then 0 else d x := by
      simpa [hij] using hle
    exact lt_of_lt_of_le hdj hle'
  · have hprod :
        (∏ x ∈ d.support, (if side x then a else b) ^ d x) =
          (∏ x ∈ d.support, a ^ (if side x then d x else 0)) *
            (∏ x ∈ d.support, b ^ (if side x then 0 else d x)) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro x hx
      by_cases hs : side x
      · simp [hs]
      · simp [hs]
    calc
      c = d.prod (fun i e => (if side i then a else b) ^ e) := hchar
      _ = ∏ x ∈ d.support, (if side x then a else b) ^ d x := by
        rfl
      _ = (∏ x ∈ d.support, a ^ (if side x then d x else 0)) *
            (∏ x ∈ d.support, b ^ (if side x then 0 else d x)) := hprod
      _ = a ^ I * b ^ J := by
        rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
end Theory.AlgebraicGroup
