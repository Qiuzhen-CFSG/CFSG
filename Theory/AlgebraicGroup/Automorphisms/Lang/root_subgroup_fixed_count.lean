module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Set.Card
public import Theory.AlgebraicGroup.Automorphisms.Lang.proposition_2_1_10
public import Theory.AlgebraicGroup.RootSubgroups.Defs

/-!
# Fixed points of Frobenius on a root subgroup

A positive iterate of a Frobenius endomorphism that maps a torus root subgroup
onto itself has `q₀ ^ m` fixed points there. The proof restricts the iterate to
the closed subgroup and transports it through an additive one-parameter
parametrization. Regularity supplies a coordinate polynomial. A polynomial
inverse to the embedded parameter shows that its Frobenius iterate has zero
derivative, while a separating ambient matrix coordinate determines its exact
degree. Thus the fixed points are the simple roots of `f - X`.

This is the fixed-point-count step of GLS3, Chapter 2, Theorem 2.1.12. It
integrates the checked one-parameter polynomial argument with the production
closed-subgroup, restriction, and parametrization APIs.
-/

universe u

namespace Theory.AlgebraicGroup

noncomputable section

set_option linter.style.haveILetI false

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma kPlusPoint_add (s t : k) :
    kPlusPoint (s + t) = kPlusPoint s * kPlusPoint t := by
  apply (additiveGroupPointEquiv k).injective
  rfl

omit [IsAlgClosed k] in
private lemma oneParameter_value_add
    {X : Variety k} [AlgebraicGroup X]
    (x : OneParameterParametrization X) (s t : k) :
    x.value (s + t) = x.value s * x.value t := by
  change x.hom.onPoints (kPlusPoint (s + t)) =
    x.hom.onPoints (kPlusPoint s) * x.hom.onPoints (kPlusPoint t)
  rw [kPlusPoint_add, map_mul]

omit [IsAlgClosed k] in
private lemma oneParameter_value_injective
    {X : Variety k} [AlgebraicGroup X]
    (x : OneParameterParametrization X) : Function.Injective x.value := by
  intro s t h
  have h' := congrArg x.inv.onPoints h
  change x.inv.onPoints (x.hom.onPoints (kPlusPoint s)) =
    x.inv.onPoints (x.hom.onPoints (kPlusPoint t)) at h'
  rw [x.hom_inv_id, x.hom_inv_id] at h'
  exact congrArg (fun z : Variety.Point (KPlus k) =>
    Multiplicative.toAdd (additiveGroupPointEquiv k z)) h'

omit [IsAlgClosed k] in
private theorem oneParameter_endomorphism_polynomial
    {X : Variety k} [AlgebraicGroup X]
    (x : OneParameterParametrization X)
    (sigma : AlgebraicGroup.Morphism X X) :
    exists f : Polynomial k, forall t : k,
      sigma.onPoints (x.value t) = x.value (f.eval t) := by
  let coordinateMorphism : AlgebraicGroup.Morphism (KPlus k) (KPlus k) :=
    x.inv.comp (sigma.comp x.hom)
  obtain ⟨p, hp⟩ := coordinateMorphism.toVariety.regular PUnit.unit
  let f : Polynomial k := MvPolynomial.uniqueAlgEquiv k PUnit p
  refine ⟨f, ?_⟩
  intro t
  have hc : coordinateMorphism.onPoints (kPlusPoint t) = kPlusPoint (f.eval t) := by
    apply Variety.Point.ext
    funext i
    cases i
    change (coordinateMorphism.toVariety.toFun (kPlusPoint t)).val PUnit.unit =
      (kPlusPoint (f.eval t)).val PUnit.unit
    rw [hp]
    change MvPolynomial.eval₂ (RingHom.id k) (fun _ => t) p = f.eval t
    exact MvPolynomial.eval₂_const_uniqueAlgEquiv.symm
  have hc' := congrArg x.hom.onPoints hc
  change x.hom.onPoints (x.inv.onPoints (sigma.onPoints (x.value t))) =
    x.value (f.eval t) at hc'
  rw [x.inv_hom_id] at hc'
  exact hc'

omit [IsAlgClosed k] in
private lemma coordinatePolynomial_additive
    {X : Variety k} [AlgebraicGroup X]
    (x : OneParameterParametrization X)
    (sigma : AlgebraicGroup.Morphism X X) (f : Polynomial k)
    (hcompat : forall t : k,
      sigma.onPoints (x.value t) = x.value (f.eval t)) :
    forall s t : k, f.eval (s + t) = f.eval s + f.eval t := by
  intro s t
  apply oneParameter_value_injective x
  calc
    x.value (f.eval (s + t)) = sigma.onPoints (x.value (s + t)) := (hcompat _).symm
    _ = sigma.onPoints (x.value s * x.value t) := by rw [oneParameter_value_add]
    _ = sigma.onPoints (x.value s) * sigma.onPoints (x.value t) :=
      sigma.map_mul _ _
    _ = x.value (f.eval s) * x.value (f.eval t) := by rw [hcompat, hcompat]
    _ = x.value (f.eval s + f.eval t) := (oneParameter_value_add x _ _).symm

omit [IsAlgClosed k] in
private lemma coordinatePolynomial_iterate
    {X : Variety k} [AlgebraicGroup X]
    (x : OneParameterParametrization X)
    (sigma : AlgebraicGroup.Morphism X X) (f : Polynomial k)
    (hcompat : forall t : k,
      sigma.onPoints (x.value t) = x.value (f.eval t)) :
    forall (n : Nat) (t : k),
      (sigma.onPoints^[n]) (x.value t) =
        x.value ((((fun p : Polynomial k => f.comp p)^[n]) Polynomial.X).eval t) := by
  intro n t
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hcompat]
      rw [Polynomial.eval_comp]

private theorem additive_derivative_constant
    (f : Polynomial k)
    (hadd : forall s t : k, f.eval (s + t) = f.eval s + f.eval t) :
    exists c : k, f.derivative = Polynomial.C c := by
  have htranslate (t : k) :
      f.comp (Polynomial.X + Polynomial.C t) = Polynomial.C (f.eval t) + f := by
    apply Polynomial.funext
    intro s
    simpa [Polynomial.eval_comp, add_comm] using hadd t s
  have hderivative_translate (t : k) :
      f.derivative.comp (Polynomial.X + Polynomial.C t) = f.derivative := by
    have h := congrArg Polynomial.derivative (htranslate t)
    simpa [Polynomial.derivative_comp] using h
  refine ⟨f.derivative.eval 0, ?_⟩
  apply Polynomial.funext
  intro t
  have h := congrArg (Polynomial.eval 0) (hderivative_translate t)
  simpa [Polynomial.eval_comp] using h

omit [IsAlgClosed k] in
private theorem derivative_iterate_comp_eq_C_pow
    (f : Polynomial k) (c : k)
    (hconstant : f.derivative = Polynomial.C c) (n : Nat) :
    (f.comp^[n] Polynomial.X).derivative = Polynomial.C (c ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Polynomial.derivative_comp,
        hconstant, ih]
      simp [pow_succ, mul_comm]

omit [IsAlgClosed k] in
private theorem derivative_eq_zero_of_iterate
    (f : Polynomial k) (M : Nat) (hM : 0 < M)
    (hconstant : exists c : k, f.derivative = Polynomial.C c)
    (hiterate : (f.comp^[M] Polynomial.X).derivative = 0) :
    f.derivative = 0 := by
  obtain ⟨c, hc⟩ := hconstant
  have hderivative := derivative_iterate_comp_eq_C_pow f c hc M
  have hC : Polynomial.C (c ^ M) = (0 : Polynomial k) :=
    hderivative.symm.trans hiterate
  have hpow : c ^ M = 0 := Polynomial.C_eq_zero.mp hC
  have hc0 : c = 0 := (pow_eq_zero_iff hM.ne').mp hpow
  rw [hc, hc0, map_zero]

private theorem fixedPoint_ncard_of_derivative_zero
    (f : Polynomial k) {q : Nat} (hq : 1 < q)
    (hdegree : f.natDegree = q) (hderivative : f.derivative = 0) :
    Set.ncard {t : k | f.eval t = t} = q := by
  have hdegreeX : (Polynomial.X : Polynomial k).natDegree < f.natDegree := by
    simpa [hdegree] using hq
  have hdegreeSub : (f - Polynomial.X).natDegree = q := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hdegreeX, hdegree]
  have hderivativeSub : (f - Polynomial.X).derivative = -1 := by
    rw [Polynomial.derivative_sub, hderivative, Polynomial.derivative_X]
    simp
  have hseparable : (f - Polynomial.X).Separable := by
    rw [Polynomial.separable_def, hderivativeSub]
    exact (isCoprime_one_right :
      IsCoprime (f - Polynomial.X) (1 : Polynomial k)).neg_right
  have hnonzero : f - Polynomial.X ≠ 0 := by
    intro h
    have hf : f = Polynomial.X := sub_eq_zero.mp h
    have : q = 1 := by
      simpa [hdegree] using congrArg Polynomial.natDegree hf
    omega
  have hset : {t : k | f.eval t = t} = (f - Polynomial.X).rootSet k := by
    ext t
    rw [Polynomial.mem_rootSet]
    simp [hnonzero, Polynomial.aeval_def, sub_eq_zero]
  rw [hset]
  have hsplit :
      (Polynomial.map (algebraMap k k) (f - Polynomial.X)).Splits := by
    simpa only [Algebra.algebraMap_self, Polynomial.map_id] using
      (IsAlgClosed.splits (f - Polynomial.X))
  rw [← Set.fintypeCard_eq_ncard]
  simpa [hdegreeSub] using
    (Polynomial.card_rootSet_eq_natDegree (K := k) hseparable hsplit)

omit [IsAlgClosed k] in
private lemma derivative_eval₂_powers_eq_zero
    {ι : Type*} (q : Nat) (hq : (q : k) = 0)
    (p : MvPolynomial ι k) (P : ι -> Polynomial k) :
    (MvPolynomial.eval₂ Polynomial.C (fun i => P i ^ q) p).derivative = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p s hp hs => simp [hp, hs]
  | mul_X p i hp =>
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
        Polynomial.derivative_mul, hp, Polynomial.derivative_pow]
      simp [hq]

omit [IsAlgClosed k] in
private lemma generalLinearFrobenius_point_coordinate
    {r n a : Nat} [Fact r.Prime] [CharP k r]
    (A : GL (Fin n) k) (c : glCoordinates n) :
    ((glPointEquiv n).symm
        (generalLinearFrobenius (k := k) n r a A)).val c =
      (((glPointEquiv n).symm A).val c) ^ (r ^ a) := by
  cases c with
  | inl ij =>
      rcases ij with ⟨i, j⟩
      rfl
  | inr hunit =>
      cases hunit
      rw [show ((glPointEquiv n).symm
          (generalLinearFrobenius (k := k) n r a A)).val
            (Sum.inr PUnit.unit) =
          (((generalLinearFrobenius (k := k) n r a A : GL (Fin n) k) :
            Matrix (Fin n) (Fin n) k).det)⁻¹ by rfl]
      rw [show ((glPointEquiv n).symm A).val (Sum.inr PUnit.unit) =
          ((A : Matrix (Fin n) (Fin n) k).det)⁻¹ by rfl]
      rw [inv_pow]
      congr 1
      change ((iterateFrobenius k r a).mapMatrix
        (A : Matrix (Fin n) (Fin n) k)).det =
          (A : Matrix (Fin n) (Fin n) k).det ^ r ^ a
      rw [← RingHom.map_det]
      rfl

private def curveCoordinatePolynomial
    {n : Nat} (E : Variety.Morphism (KPlus k) (glVariety n))
    (c : glCoordinates n) : Polynomial k :=
  MvPolynomial.uniqueAlgEquiv k PUnit (Classical.choose (E.regular c))

omit [IsAlgClosed k] in
private lemma curveCoordinatePolynomial_eval
    {n : Nat} (E : Variety.Morphism (KPlus k) (glVariety n))
    (c : glCoordinates n) (t : k) :
    (E.toFun (kPlusPoint t)).val c =
      (curveCoordinatePolynomial E c).eval t := by
  rw [Classical.choose_spec (E.regular c) (kPlusPoint t)]
  change MvPolynomial.eval₂ (RingHom.id k) (fun _ => t)
      (Classical.choose (E.regular c)) = _
  exact MvPolynomial.eval₂_const_uniqueAlgEquiv.symm

omit [IsAlgClosed k] in
private theorem exists_frobenius_parameter_polynomial
    {r n a : Nat} [Fact r.Prime] [CharP k r]
    (H : ClosedSubgroup (glVariety n : Variety k))
    (ha : 0 < a) :
    letI := H.carrierAlgebraicGroup
    ∀ y : OneParameterParametrization H.carrierVariety,
      ∃ R : Polynomial k,
        R.derivative = 0 ∧
          ∀ s t : k,
            H.includePoint (y.value s) =
                (glPointEquiv n).symm
                  (generalLinearFrobenius (k := k) n r a
                    (glPointEquiv n (H.includePoint (y.value t)))) →
              R.eval t = s := by
  letI := H.carrierAlgebraicGroup
  intro y
  obtain ⟨F, hF⟩ :=
    oneParameterParametrization_exists_ambient_parameterPolynomial H y
  obtain ⟨p, hp⟩ := F.representedBy
  let E : Variety.Morphism (KPlus k) (glVariety n) :=
    H.inclusion.toVariety.comp y.hom.toVariety
  let q : Nat := r ^ a
  let R : Polynomial k :=
    MvPolynomial.eval₂ Polynomial.C
      (fun c : glCoordinates n => curveCoordinatePolynomial E c ^ q) p
  have hq : (q : k) = 0 := by
    apply (CharP.cast_eq_zero_iff k r q).2
    exact dvd_pow_self r ha.ne'
  have hRderivative : R.derivative = 0 := by
    exact derivative_eval₂_powers_eq_zero q hq p
      (curveCoordinatePolynomial E)
  have hR (t : k) :
      R.eval t =
        F ((glPointEquiv n).symm
          (generalLinearFrobenius (k := k) n r a
            (glPointEquiv n (H.includePoint (y.value t))))) := by
    dsimp only [R]
    rw [MvPolynomial.polynomial_eval_eval₂, hp]
    have hcoeff :
        (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id k := by
      ext z
      simp
    rw [hcoeff]
    congr 1
    funext c
    rw [Polynomial.eval_pow, generalLinearFrobenius_point_coordinate]
    congr 1
    rw [← curveCoordinatePolynomial_eval]
    rw [Equiv.symm_apply_apply]
    rfl

  refine ⟨R, hRderivative, ?_⟩
  intro s t hst
  have h := congrArg F hst
  rw [hF s, ← hR t] at h
  exact h.symm

omit [IsAlgClosed k] in
private theorem oneParameter_fixedPoint_ncard
    {X : Variety k} [AlgebraicGroup X]
    (x : OneParameterParametrization X)
    (sigma : AlgebraicGroup.Morphism X X) (f : Polynomial k)
    (hcompat : ∀ t : k,
      sigma.onPoints (x.value t) = x.value (f.eval t)) :
    Set.ncard {z : Variety.Point X | sigma.onPoints z = z} =
      Set.ncard {t : k | f.eval t = t} := by
  let valueEquiv : k ≃ Variety.Point X := {
    toFun := x.value
    invFun := fun z => Multiplicative.toAdd
      (additiveGroupPointEquiv k (x.inv.onPoints z))
    left_inv := by
      intro t
      change Multiplicative.toAdd
        (additiveGroupPointEquiv k
          (x.inv.onPoints (x.hom.onPoints (kPlusPoint t)))) = t
      rw [x.hom_inv_id]
      rfl
    right_inv := by
      intro z
      change x.hom.onPoints
        (kPlusPoint (Multiplicative.toAdd
          (additiveGroupPointEquiv k (x.inv.onPoints z)))) = z
      have hk :
          kPlusPoint (Multiplicative.toAdd
            (additiveGroupPointEquiv k (x.inv.onPoints z))) =
            x.inv.onPoints z := by
        apply (additiveGroupPointEquiv k).injective
        rfl
      rw [hk, x.inv_hom_id]
  }
  let fixedEquiv :
      {t : k // f.eval t = t} ≃
        {z : Variety.Point X // sigma.onPoints z = z} := {
    toFun := fun t => ⟨valueEquiv t, by
      change sigma.onPoints (x.value t) = x.value t
      rw [hcompat, t.property]⟩
    invFun := fun z => ⟨valueEquiv.symm z, by
      have hv : x.value (valueEquiv.symm z) = z :=
        valueEquiv.apply_symm_apply z
      apply oneParameter_value_injective x
      rw [← hcompat]
      exact (congrArg sigma.onPoints hv).trans (z.property.trans hv.symm)⟩
    left_inv := by
      intro t
      apply Subtype.ext
      exact valueEquiv.symm_apply_apply t
    right_inv := by
      intro z
      apply Subtype.ext
      exact valueEquiv.apply_symm_apply z
  }
  change Nat.card {z : Variety.Point X // sigma.onPoints z = z} =
    Nat.card {t : k // f.eval t = t}
  exact Nat.card_congr fixedEquiv.symm

private theorem oneParameter_fixedPoints_ncard_eq_level
    {X : Variety k} [AlgebraicGroup X]
    {r : Nat} [Fact r.Prime] [CharP k r]
    (sigma : AlgebraicGroup.Morphism X X) (q₀ : NNReal)
    (hsigma : IsFrobeniusEndomorphismOfLevel (r := r) q₀ sigma)
    (hX : IsOneParameterGroup X) :
  ((Set.ncard {z : Variety.Point X | sigma.onPoints z = z} : Nat) : NNReal) =
      q₀ := by
  rcases hsigma with ⟨M, a, n, H, hM, ha, hlevel, e, he⟩
  letI := H.carrierAlgebraicGroup
  obtain ⟨x⟩ := hX
  obtain ⟨f, hcompat⟩ := oneParameter_endomorphism_polynomial x sigma
  let g : Polynomial k := f.comp^[M] Polynomial.X
  let y : OneParameterParametrization H.carrierVariety := e.comp x
  obtain ⟨R, hRderivative, hR⟩ :=
    exists_frobenius_parameter_polynomial H ha y
  have hiterate (t : k) :
      (sigma.onPoints^[M]) (x.value t) = x.value (g.eval t) := by
    exact coordinatePolynomial_iterate x sigma f hcompat M t
  have hfrobenius (t : k) :
      H.includePoint (y.value (g.eval t)) =
        (glPointEquiv n).symm
          (generalLinearFrobenius (k := k) n r a
            (glPointEquiv n (H.includePoint (y.value t)))) := by
    change H.inclusion.onPoints (e.hom.onPoints (x.value (g.eval t))) =
      (glPointEquiv n).symm
        (generalLinearFrobenius (k := k) n r a
          (glPointEquiv n
            (H.inclusion.onPoints (e.hom.onPoints (x.value t)))))
    apply (glPointEquiv n).injective
    rw [← hiterate]
    simpa only [Equiv.apply_symm_apply] using he (x.value t)
  have hgR : g = R := by
    apply Polynomial.funext
    intro t
    exact (hR (g.eval t) t (hfrobenius t)).symm
  have hgderivative : g.derivative = 0 := by
    rw [hgR, hRderivative]
  let E : Variety.Morphism (KPlus k) (glVariety n) :=
    H.inclusion.toVariety.comp y.hom.toVariety
  have hEne :
      E.toFun (kPlusPoint (0 : k)) ≠ E.toFun (kPlusPoint (1 : k)) := by
    intro h
    have hy : y.value (0 : k) = y.value (1 : k) := by
      apply H.inclusion_injective
      exact h
    exact zero_ne_one (oneParameter_value_injective y hy)
  obtain ⟨c, hc⟩ : ∃ c : glCoordinates n,
      (E.toFun (kPlusPoint (0 : k))).val c ≠
        (E.toFun (kPlusPoint (1 : k))).val c := by
    by_contra hall
    push Not at hall
    apply hEne
    apply Variety.Point.ext
    funext c
    exact hall c
  let P : Polynomial k := curveCoordinatePolynomial E c
  have hPeval : P.eval 0 ≠ P.eval 1 := by
    simpa only [P, ← curveCoordinatePolynomial_eval] using hc
  have hPdegree : 0 < P.natDegree := by
    apply Nat.pos_of_ne_zero
    intro hdegree
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdegree] at hPeval
    simp at hPeval
  let q : Nat := r ^ a
  have hPg : P.comp g = P ^ q := by
    apply Polynomial.funext
    intro t
    rw [Polynomial.eval_comp, Polynomial.eval_pow]
    calc
      P.eval (g.eval t) =
          (E.toFun (kPlusPoint (g.eval t))).val c :=
        (curveCoordinatePolynomial_eval E c (g.eval t)).symm
      _ = ((glPointEquiv n).symm
          (generalLinearFrobenius (k := k) n r a
            (glPointEquiv n (E.toFun (kPlusPoint t))))).val c := by
        exact congrArg (fun z => z.val c) (hfrobenius t)
      _ = ((E.toFun (kPlusPoint t)).val c) ^ q := by
        simpa only [q, Equiv.symm_apply_apply] using
          (generalLinearFrobenius_point_coordinate
            (a := a) (glPointEquiv n (E.toFun (kPlusPoint t))) c)
      _ = (P.eval t) ^ q := by
        rw [curveCoordinatePolynomial_eval]
  have hgdegree : g.natDegree = q := by
    have hdegrees := congrArg Polynomial.natDegree hPg
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_pow] at hdegrees
    apply Nat.eq_of_mul_eq_mul_left hPdegree
    simpa [Nat.mul_comm] using hdegrees
  have hdegreePower : f.natDegree ^ M = q := by
    rw [← hgdegree]
    dsimp only [g]
    rw [Polynomial.natDegree_iterate_comp, Polynomial.natDegree_X, mul_one]
  have hq : 1 < q := by
    exact Nat.one_lt_pow ha.ne' (Fact.out : Nat.Prime r).one_lt
  have hfdegree : 1 < f.natDegree := by
    apply (one_lt_pow_iff hM.ne').mp
    rw [hdegreePower]
    exact hq
  have hconstant : ∃ c : k, f.derivative = Polynomial.C c :=
    additive_derivative_constant f
      (coordinatePolynomial_additive x sigma f hcompat)
  have hfderivative : f.derivative = 0 :=
    derivative_eq_zero_of_iterate f M hM hconstant hgderivative
  have hfixed : Set.ncard {t : k | f.eval t = t} = f.natDegree :=
    fixedPoint_ncard_of_derivative_zero f hfdegree rfl hfderivative
  have hdegreeLevel : (f.natDegree : NNReal) = q₀ := by
    have hdegreePowerNN :
        (f.natDegree : NNReal) ^ M = (q : NNReal) := by
      exact_mod_cast hdegreePower
    have hlevelQ : q₀ ^ M = (q : NNReal) := by
      simpa only [q, Nat.cast_pow] using hlevel
    exact pow_left_injective hM.ne' (hdegreePowerNN.trans hlevelQ.symm)
  rw [oneParameter_fixedPoint_ncard x sigma f hcompat, hfixed]
  exact hdegreeLevel

/-- If a positive iterate of a Frobenius endomorphism preserves a torus root
subgroup surjectively, its fixed points on that root subgroup have cardinality
equal to the corresponding power of the Frobenius level. -/
public theorem rootSubgroup_fixedPoints_ncard_eq_level_pow
    {K : Variety k} [AlgebraicGroup K]
    {r : Nat} [Fact r.Prime] [CharP k r]
    (sigma : AlgebraicGroup.Morphism K K) (q₀ : NNReal)
    (hsigma : IsFrobeniusEndomorphismOfLevel (r := r) q₀ sigma)
    (T X : ClosedSubgroup K) (hX : IsTorusRootSubgroup T X)
    (m : Nat) (hm : 0 < m)
    (hmaps : Set.MapsTo (sigma.onPoints^[m])
      (X : Set (Variety.Point K)) (X : Set (Variety.Point K)))
    (hsurj : Set.SurjOn (sigma.onPoints^[m])
      (X : Set (Variety.Point K)) (X : Set (Variety.Point K))) :
    ((Set.ncard {z : Variety.Point K |
        z ∈ X.toSubgroup ∧ (sigma.onPoints^[m]) z = z} : Nat) : NNReal) =
      q₀ ^ m := by
  obtain ⟨tau, htauLevel, htau⟩ :=
    ((proposition_2_1_10 sigma q₀).1 hsigma).2 m hm
  have hInv : tau.onPoints '' (X : Set (Variety.Point K)) =
      (X : Set (Variety.Point K)) := by
    apply Set.Subset.antisymm
    · rintro z ⟨y, hy, rfl⟩
      rw [htau]
      exact hmaps hy
    · intro z hz
      obtain ⟨y, hy, hyz⟩ := hsurj hz
      refine ⟨y, hy, ?_⟩
      rw [htau]
      exact hyz
  obtain ⟨rho, hrhoLevel, hcomm⟩ :=
    proposition_2_1_10_invariant_subgroup tau (q₀ ^ m) htauLevel X hInv
  have hcarrier :=
    oneParameter_fixedPoints_ncard_eq_level rho (q₀ ^ m) hrhoLevel hX.2
  have hfixedSet :
      {z : Variety.Point K |
          z ∈ X.toSubgroup ∧ (sigma.onPoints^[m]) z = z} =
        X.inclusion.onPoints ''
          {y : Variety.Point X.carrierVariety | rho.onPoints y = y} := by
    ext z
    constructor
    · intro hz
      let y : Variety.Point X.carrierVariety :=
        X.pointEquiv.symm ⟨z, hz.1⟩
      have hyinc : X.inclusion.onPoints y = z := by
        change (X.pointEquiv y).val = z
        dsimp only [y]
        rw [X.pointEquiv.apply_symm_apply]
      refine ⟨y, ?_, hyinc⟩
      apply X.inclusion_injective
      rw [hcomm, hyinc, htau]
      exact hz.2
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(X.pointEquiv y).property, ?_⟩
      rw [← htau, ← hcomm, hy]
  rw [hfixedSet, Set.ncard_image_of_injective _ X.inclusion_injective]
  exact hcarrier

end

end Theory.AlgebraicGroup
