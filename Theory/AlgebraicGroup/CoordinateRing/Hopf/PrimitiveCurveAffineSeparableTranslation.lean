module

public import Theory.AlgebraicGroup.CoordinateRing.Hopf.PrimitiveCurveSeparableKernelCharP

/-!
# Affine translations of a primitive Hopf-curve separable closure

Let `t` be a transcendental primitive element in a finite-type Hopf domain of
transcendence degree one.  Every regular character translates `t` by the
scalar `q t`.  This module extends that coordinate-ring translation to the
ambient fraction field and extends `Polynomial.taylorEquiv (q t)` to
`RatFunc k`.  The two fraction-field equivalences commute with
`primitiveFractionMap`.

The commuting square transports separability by
`IsSeparable.of_equiv_equiv`, so the ambient fraction translation restricts to
a ring equivalence of the separable closure.  Character commutativity, proved
by `primitive_hopf_curve_character_mul_comm`, then shows that this semilinear
translation commutes with the primitive-kernel Galois action.  When the
coordinate ring is normal, the action exhausts the Galois group; consequently
the translation preserves every fixed field and transports its relative
trace.  Application lemmas expose all ambient actions without exposing the
implementations of the equivalences.

This is the affine semilinear ingredient in the regular trace-ideal argument
for the normal index-`p` Artin--Schreier layer following Borel's discussion of
Theorem 10.9 and Corollary 11.6 (whose omitted index-`p` step cites SGA 3,
Expose VII, Lemma 3).  The proof uses only the primitive fraction map, direct
Hopf character translations, and the separable-kernel action.  It does not use
the parent rationality theorem, an affine-line classification, or a primitive
generator theorem.
-/

open scoped TensorProduct

namespace Theory.AlgebraicGroup

noncomputable section

universe u v

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {k : Type u} {A : Type v}
variable [Field k] [IsAlgClosed k] [CommRing A] [HopfAlgebra k A]
variable [IsDomain A] [Algebra.FiniteType k A]

/-- The extension of a regular character translation to the fraction field. -/
public noncomputable def regularCharacterFractionTranslation
    (q : WithConv (A →ₐ[k] k)) : FractionRing A ≃ₐ[k] FractionRing A :=
  IsFractionRing.algEquivOfAlgEquiv (regularCharacterTranslation q)

/-- A fraction-field character translation agrees with regular translation on
coordinate-ring elements. -/
public theorem regularCharacterFractionTranslation_algebraMap
    (q : WithConv (A →ₐ[k] k)) (a : A) :
    regularCharacterFractionTranslation q
        (algebraMap A (FractionRing A) a) =
      algebraMap A (FractionRing A) (regularCharacterTranslation q a) := by
  exact IsFractionRing.algEquivOfAlgEquiv_algebraMap
    (regularCharacterTranslation q) a

/-- Taylor translation by the value of a character at `t`, extended to the
rational function field. -/
public noncomputable def primitiveRatFuncTranslation
    (t : A) (q : WithConv (A →ₐ[k] k)) : RatFunc k ≃ₐ[k] RatFunc k :=
  IsFractionRing.algEquivOfAlgEquiv (Polynomial.taylorEquiv (q t))

/-- Rational-function translation applies polynomial Taylor translation to
polynomial elements. -/
public theorem primitiveRatFuncTranslation_algebraMap
    (t : A) (q : WithConv (A →ₐ[k] k)) (P : Polynomial k) :
    primitiveRatFuncTranslation t q
        (algebraMap (Polynomial k) (RatFunc k) P) =
      algebraMap (Polynomial k) (RatFunc k) (Polynomial.taylor (q t) P) := by
  exact IsFractionRing.algEquivOfAlgEquiv_algebraMap
    (Polynomial.taylorEquiv (q t)) P

/-- The regular fraction translation and rational-function Taylor translation
commute with the primitive fraction map. -/
public theorem regularCharacterFractionTranslation_primitiveFractionMap
    (t : A) (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (q : WithConv (A →ₐ[k] k)) (x : RatFunc k) :
    regularCharacterFractionTranslation q (primitiveFractionMap t ht x) =
      primitiveFractionMap t ht (primitiveRatFuncTranslation t q x) := by
  let lhs : RatFunc k →+* FractionRing A :=
    (regularCharacterFractionTranslation q).toRingHom.comp
      (primitiveFractionMap t ht).toRingHom
  let rhs : RatFunc k →+* FractionRing A :=
    (primitiveFractionMap t ht).toRingHom.comp
      (primitiveRatFuncTranslation t q).toRingHom
  have heq : lhs = rhs := by
    apply IsFractionRing.ringHom_ext (A := Polynomial k)
    intro P
    change regularCharacterFractionTranslation q
        (primitiveFractionMap t ht
          (algebraMap (Polynomial k) (RatFunc k) P)) =
      primitiveFractionMap t ht
        (primitiveRatFuncTranslation t q
          (algebraMap (Polynomial k) (RatFunc k) P))
    rw [show algebraMap (Polynomial k) (RatFunc k) P =
      algebraMap (Polynomial k) (RatFunc k) P /
        algebraMap (Polynomial k) (RatFunc k) 1 by simp]
    rw [primitiveFractionMap_apply_div]
    simp only [map_one, div_one]
    rw [regularCharacterFractionTranslation_algebraMap,
      primitiveRatFuncTranslation_algebraMap]
    rw [show algebraMap (Polynomial k) (RatFunc k)
        (Polynomial.taylor (q t) P) =
      algebraMap (Polynomial k) (RatFunc k)
          (Polynomial.taylor (q t) P) /
        algebraMap (Polynomial k) (RatFunc k) 1 by simp]
    rw [primitiveFractionMap_apply_div]
    simp only [map_one, div_one]
    congr 1
    calc
      regularCharacterTranslation q (Polynomial.aeval t P) =
          Polynomial.aeval (regularCharacterTranslation q t) P :=
        (Polynomial.aeval_algHom_apply
          (regularCharacterTranslation q).toAlgHom t P).symm
      _ = Polynomial.aeval (algebraMap k A (q t) + t) P := by
        rw [regularCharacterTranslation_apply_of_primitive q t hprimitive]
      _ = Polynomial.aeval t (Polynomial.taylor (q t) P) := by
        rw [Polynomial.taylor_apply, Polynomial.aeval_comp]
        simp [add_comm]
  exact DFunLike.congr_fun heq x

/-- Semilinear fraction translation preserves and reflects separability over
the rational function field. -/
public theorem regularCharacterFractionTranslation_isSeparable_iff
    (t : A) (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (q : WithConv (A →ₐ[k] k)) (x : FractionRing A) :
    let f := primitiveFractionMap (k := k) t ht
    letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
    IsSeparable (RatFunc k) (regularCharacterFractionTranslation q x) ↔
      IsSeparable (RatFunc k) x := by
  let f := primitiveFractionMap (k := k) t ht
  letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
  dsimp only
  have hcomp :
      RingHom.comp (algebraMap (RatFunc k) (FractionRing A))
          (primitiveRatFuncTranslation t q).toRingEquiv.toRingHom =
        RingHom.comp
          (regularCharacterFractionTranslation q).toRingEquiv.toRingHom
          (algebraMap (RatFunc k) (FractionRing A)) := by
    ext y
    exact (regularCharacterFractionTranslation_primitiveFractionMap
      t ht hprimitive q y).symm
  constructor
  · intro hx
    have hinvcomp :
        RingHom.comp (algebraMap (RatFunc k) (FractionRing A))
            (primitiveRatFuncTranslation t q).symm.toRingEquiv.toRingHom =
          RingHom.comp
            (regularCharacterFractionTranslation q).symm.toRingEquiv.toRingHom
            (algebraMap (RatFunc k) (FractionRing A)) := by
      ext y
      change primitiveFractionMap t ht
          ((primitiveRatFuncTranslation t q).symm y) =
        (regularCharacterFractionTranslation q).symm
          (primitiveFractionMap t ht y)
      apply (regularCharacterFractionTranslation q).injective
      rw [(regularCharacterFractionTranslation q).apply_symm_apply]
      simpa using regularCharacterFractionTranslation_primitiveFractionMap
        t ht hprimitive q ((primitiveRatFuncTranslation t q).symm y)
    have hsep := IsSeparable.of_equiv_equiv
      (primitiveRatFuncTranslation t q).symm.toRingEquiv
      (regularCharacterFractionTranslation q).symm.toRingEquiv
      hinvcomp hx
    simpa using hsep
  · intro hx
    exact IsSeparable.of_equiv_equiv
      (primitiveRatFuncTranslation t q).toRingEquiv
      (regularCharacterFractionTranslation q).toRingEquiv hcomp hx

/-- The semilinear regular character translation restricted to the separable
closure of the primitive rational function field. -/
public noncomputable def regularCharacterSeparableTranslation
    (t : A) (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (q : WithConv (A →ₐ[k] k)) :
    let f := primitiveFractionMap (k := k) t ht
    letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
    let F := separableClosure (RatFunc k) (FractionRing A)
    F ≃+* F := by
  let f := primitiveFractionMap (k := k) t ht
  letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
  let F := separableClosure (RatFunc k) (FractionRing A)
  let tau := regularCharacterFractionTranslation q
  exact
    { toFun := fun x => ⟨tau x.1,
        (regularCharacterFractionTranslation_isSeparable_iff
          t ht hprimitive q x.1).2 x.2⟩
      invFun := fun x => ⟨tau.symm x.1, by
        apply (regularCharacterFractionTranslation_isSeparable_iff
          t ht hprimitive q (tau.symm x.1)).1
        simpa [tau] using
          (show IsSeparable (RatFunc k) x.1 from x.2)⟩
      left_inv := fun x => by ext; simp [tau]
      right_inv := fun x => by ext; simp [tau]
      map_add' := fun x y => by ext; simp [tau]
      map_mul' := fun x y => by ext; simp [tau] }

/-- Restricted separable translation is the ambient fraction translation on
underlying elements. -/
public theorem regularCharacterSeparableTranslation_apply
    (t : A) (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (q : WithConv (A →ₐ[k] k)) :
    let f := primitiveFractionMap (k := k) t ht
    letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
    let F := separableClosure (RatFunc k) (FractionRing A)
    ∀ x : F,
      (((regularCharacterSeparableTranslation t ht hprimitive q) x : F) :
          FractionRing A) = regularCharacterFractionTranslation q x.1 := by
  let f := primitiveFractionMap (k := k) t ht
  letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
  dsimp only
  intro x
  rfl

/-- Ambient regular fraction translation commutes with every primitive-kernel
fraction translation. -/
public theorem regularCharacterFractionTranslation_commute_primitiveFractionTranslation
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (q : WithConv (A →ₐ[k] k))
    (r : primitiveCharacterKernel t hprimitive) :
    let f := primitiveFractionMap (k := k) t ht
    letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
    ∀ x : FractionRing A,
      regularCharacterFractionTranslation q
          (primitiveFractionTranslation t ht hprimitive r x) =
        primitiveFractionTranslation t ht hprimitive r
          (regularCharacterFractionTranslation q x) := by
  let f := primitiveFractionMap (k := k) t ht
  letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
  dsimp only
  intro x
  let lhs : FractionRing A →+* FractionRing A :=
    (regularCharacterFractionTranslation q).toRingHom.comp
      (primitiveFractionTranslation t ht hprimitive r).toRingHom
  let rhs : FractionRing A →+* FractionRing A :=
    (primitiveFractionTranslation t ht hprimitive r).toRingHom.comp
      (regularCharacterFractionTranslation q).toRingHom
  have heq : lhs = rhs := by
    apply IsFractionRing.ringHom_ext (A := A)
    intro a
    change regularCharacterFractionTranslation q
        (primitiveFractionTranslation t ht hprimitive r
          (algebraMap A (FractionRing A) a)) =
      primitiveFractionTranslation t ht hprimitive r
        (regularCharacterFractionTranslation q
          (algebraMap A (FractionRing A) a))
    rw [primitiveFractionTranslation_algebraMap,
      regularCharacterFractionTranslation_algebraMap,
      regularCharacterFractionTranslation_algebraMap,
      primitiveFractionTranslation_algebraMap]
    congr 1
    have hcomm := primitive_hopf_curve_character_mul_comm
      htrdeg t ht hprimitive q r.1
    have hmul_qr := regularCharacterTranslation_mul q r.1
    have hmul_rq := regularCharacterTranslation_mul r.1 q
    calc
      regularCharacterTranslation q (regularCharacterTranslation r.1 a) =
          regularCharacterTranslation (r.1 * q) a := by
            rw [hmul_rq]
            rfl
      _ = regularCharacterTranslation (q * r.1) a := by rw [hcomm]
      _ = regularCharacterTranslation r.1
          (regularCharacterTranslation q a) := by
            rw [hmul_qr]
            rfl
  exact DFunLike.congr_fun heq x

/-- Restricted semilinear translation commutes with the primitive separable
kernel action. -/
public theorem regularCharacterSeparableTranslation_commute_kernelAction
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (q : WithConv (A →ₐ[k] k))
    (r : (primitiveCharacterKernel t hprimitive)ᵐᵒᵖ) :
    let f := primitiveFractionMap (k := k) t ht
    letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
    let F := separableClosure (RatFunc k) (FractionRing A)
    ∀ x : F,
      regularCharacterSeparableTranslation t ht hprimitive q
          ((primitiveSeparableKernelAction t ht hprimitive) r x) =
        (primitiveSeparableKernelAction t ht hprimitive) r
          (regularCharacterSeparableTranslation t ht hprimitive q x) := by
  let f := primitiveFractionMap (k := k) t ht
  letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
  dsimp only
  intro x
  apply Subtype.ext
  rw [regularCharacterSeparableTranslation_apply,
    primitiveSeparableKernelAction_apply,
    primitiveSeparableKernelAction_apply,
    regularCharacterSeparableTranslation_apply]
  exact regularCharacterFractionTranslation_commute_primitiveFractionTranslation
    htrdeg t ht hprimitive q r.unop x.1

/-- For a normal coordinate ring, semilinear translation commutes with every
automorphism of the separable closure over the primitive rational function
field. -/
public theorem regularCharacterSeparableTranslation_commute
    [IsIntegrallyClosed A]
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (q : WithConv (A →ₐ[k] k)) :
    let f := primitiveFractionMap (k := k) t ht
    letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
    let F := separableClosure (RatFunc k) (FractionRing A)
    ∀ (σ : F ≃ₐ[RatFunc k] F) (x : F),
      regularCharacterSeparableTranslation t ht hprimitive q (σ x) =
        σ (regularCharacterSeparableTranslation t ht hprimitive q x) := by
  let f := primitiveFractionMap (k := k) t ht
  letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
  dsimp only
  intro σ x
  obtain ⟨r, rfl⟩ :=
    (primitiveSeparableKernelAction_bijective htrdeg t ht hprimitive).2 σ
  exact regularCharacterSeparableTranslation_commute_kernelAction
    htrdeg t ht hprimitive q r x

/-- Semilinear translation preserves and reflects membership in every fixed
field of the separable closure. -/
public theorem regularCharacterSeparableTranslation_mem_fixedField_iff
    [IsIntegrallyClosed A]
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (q : WithConv (A →ₐ[k] k)) :
    let f := primitiveFractionMap (k := k) t ht
    letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
    let F := separableClosure (RatFunc k) (FractionRing A)
    ∀ (H : Subgroup (F ≃ₐ[RatFunc k] F)) (x : F),
      regularCharacterSeparableTranslation t ht hprimitive q x ∈
          IntermediateField.fixedField H ↔
        x ∈ IntermediateField.fixedField H := by
  let f := primitiveFractionMap (k := k) t ht
  letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
  dsimp only
  intro H x
  simp only [IntermediateField.mem_fixedField_iff]
  constructor
  · intro hx σ hσ
    apply (regularCharacterSeparableTranslation t ht hprimitive q).injective
    rw [regularCharacterSeparableTranslation_commute
      htrdeg t ht hprimitive q σ x, hx σ hσ]
  · intro hx σ hσ
    rw [← regularCharacterSeparableTranslation_commute
      htrdeg t ht hprimitive q σ x, hx σ hσ]

/-- The restriction of semilinear translation to a fixed field. -/
public noncomputable def regularCharacterFixedFieldTranslation
    [IsIntegrallyClosed A]
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (q : WithConv (A →ₐ[k] k)) :
    let f := primitiveFractionMap (k := k) t ht
    letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
    let F := separableClosure (RatFunc k) (FractionRing A)
    ∀ H : Subgroup (F ≃ₐ[RatFunc k] F),
      IntermediateField.fixedField H ≃+* IntermediateField.fixedField H := by
  let f := primitiveFractionMap (k := k) t ht
  letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
  let F := separableClosure (RatFunc k) (FractionRing A)
  dsimp only
  intro H
  let tau := regularCharacterSeparableTranslation t ht hprimitive q
  exact
    { toFun := fun x => ⟨tau x.1,
        (regularCharacterSeparableTranslation_mem_fixedField_iff
          htrdeg t ht hprimitive q H x.1).2 x.2⟩
      invFun := fun x => ⟨tau.symm x.1, by
        apply (regularCharacterSeparableTranslation_mem_fixedField_iff
          htrdeg t ht hprimitive q H (tau.symm x.1)).1
        simp [tau]⟩
      left_inv := fun x => by ext; simp [tau]
      right_inv := fun x => by ext; simp [tau]
      map_add' := fun x y => by ext; simp [tau]
      map_mul' := fun x y => by ext; simp [tau] }

/-- Fixed-field translation is the separable-closure translation on underlying
elements. -/
public theorem regularCharacterFixedFieldTranslation_apply
    [IsIntegrallyClosed A]
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (q : WithConv (A →ₐ[k] k)) :
    let f := primitiveFractionMap (k := k) t ht
    letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
    let F := separableClosure (RatFunc k) (FractionRing A)
    ∀ (H : Subgroup (F ≃ₐ[RatFunc k] F))
      (x : IntermediateField.fixedField H),
      ((regularCharacterFixedFieldTranslation
          htrdeg t ht hprimitive q H x :
          IntermediateField.fixedField H) : F) =
        regularCharacterSeparableTranslation t ht hprimitive q x.1 := by
  let f := primitiveFractionMap (k := k) t ht
  letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
  dsimp only
  intro H x
  rfl

/-- Relative trace to a fixed field is equivariant for semilinear regular
character translation. -/
public theorem regularCharacterSeparableTranslation_trace_fixedField
    [IsIntegrallyClosed A]
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (q : WithConv (A →ₐ[k] k)) :
    let f := primitiveFractionMap (k := k) t ht
    letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
    let F := separableClosure (RatFunc k) (FractionRing A)
    ∀ (H : Subgroup (F ≃ₐ[RatFunc k] F)) (x : F),
      regularCharacterFixedFieldTranslation htrdeg t ht hprimitive q H
          (Algebra.trace (IntermediateField.fixedField H) F x) =
        Algebra.trace (IntermediateField.fixedField H) F
          (regularCharacterSeparableTranslation t ht hprimitive q x) := by
  let f := primitiveFractionMap (k := k) t ht
  letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
  dsimp only
  intro H x
  let E := IntermediateField.fixedField H
  let tauE := regularCharacterFixedFieldTranslation
    htrdeg t ht hprimitive q H
  let tauF := regularCharacterSeparableTranslation t ht hprimitive q
  have hcomp :
      RingHom.comp (algebraMap E
          (separableClosure (RatFunc k) (FractionRing A)))
          tauE.toRingHom =
        RingHom.comp tauF.toRingHom
          (algebraMap E
            (separableClosure (RatFunc k) (FractionRing A))) := by
    ext y
    rfl
  have htrace := Algebra.trace_eq_of_equiv_equiv tauE tauF hcomp x
  rw [htrace, tauE.apply_symm_apply]

end

end Theory.AlgebraicGroup
