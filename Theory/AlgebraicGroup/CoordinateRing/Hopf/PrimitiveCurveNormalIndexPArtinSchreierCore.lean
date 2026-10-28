module

public import Theory.AlgebraicGroup.CoordinateRing.Hopf.PrimitiveCurveNormalIndexPRegularTraceOne
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.PrimitiveCurveArtinSchreierCocycleDescent

/-!
# Regular normal index-p Artin--Schreier core

Let `t` be a transcendental primitive coordinate on a normal affine Hopf curve
of transcendence degree one in prime characteristic `p`.  For every index-`p`
subgroup of the primitive separable Galois group, this module assembles one
certificate containing its character-kernel transport and normality, stability
of its fixed field under all regular character translations, and the regular
trace-one Artin--Schreier generator of that fixed field.

The generator is centered to have counit zero.  Its Artin--Schreier difference
therefore descends to a polynomial in `t`, while its actual reduced coproduct
descends to a normalized symmetric additive bivariate cocycle whose
Artin--Schreier difference is the corresponding additive coboundary.  The
certificate also records the degree-`p` fixed-field computation, its simple
adjoin description, and the strict subgroup-cardinality inequality needed for
the subsequent primitive-coordinate rebasing.

The proof transports the subgroup through the bijective primitive character
action.  Character commutativity makes the Galois group commutative and hence
the subgroup normal; the semilinear affine-translation API preserves its fixed
field.  The regular trace-one construction and cocycle descent then provide
the remaining witnesses.  This is the degree-`p` Artin--Schreier step used in
Borel, *Linear Algebraic Groups*, Theorem 10.9 and the post-11.6 discussion,
which cite SGA 3, Expose VII, Lemma 3.
-/

namespace Theory.AlgebraicGroup

noncomputable section

universe u v

set_option linter.style.haveILetI false

variable {k : Type u} {A : Type v} {p : Nat}
variable [Field k] [IsAlgClosed k] [CharP k p] [Fact p.Prime]
variable [CommRing A] [HopfAlgebra k A] [IsDomain A]
variable [Algebra.FiniteType k A] [IsIntegrallyClosed A]

/-- The complete regular Artin--Schreier certificate attached to an index-`p`
subgroup of the primitive separable Galois group. -/
public theorem primitive_hopf_curve_normal_index_p_artin_schreier_certificate
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0) :
    let f := primitiveFractionMap (k := k) t ht
    letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
    letI : IsScalarTower k (RatFunc k) (FractionRing A) :=
      IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
    let F := separableClosure (RatFunc k) (FractionRing A)
    forall H : Subgroup (F ≃ₐ[RatFunc k] F), H.index = p ->
      exists J : Subgroup ((primitiveCharacterKernel t hprimitive)ᵐᵒᵖ),
      J.map (primitiveSeparableKernelAction t ht hprimitive) = H /\
      H.Normal /\
      (∀ r : WithConv (A →ₐ[k] k), ∀ x : F,
        regularCharacterSeparableTranslation t ht hprimitive r x ∈
            IntermediateField.fixedField H ↔
          x ∈ IntermediateField.fixedField H) /\
      exists sigma : F ≃ₐ[RatFunc k] F,
      exists q : primitiveCharacterKernel t hprimitive,
      exists a0 s0 : A,
      exists haF : algebraMap A (FractionRing A) a0 ∈ F,
      exists hsF : algebraMap A (FractionRing A) s0 ∈ F,
        primitiveSeparableKernelAction t ht hprimitive
            (MulOpposite.op q) = sigma /\
        regularCharacterTranslation q.1 t = t /\
        (∀ x : F,
          ((sigma x : F) : FractionRing A) =
            primitiveFractionTranslation t ht hprimitive q x.1) /\
        sigma ∉ H /\
        let aF : F := ⟨algebraMap A (FractionRing A) a0, haF⟩
        let sF : F := ⟨algebraMap A (FractionRing A) s0, hsF⟩
        exists haE : aF ∈ IntermediateField.fixedField H,
        exists _hsE : sF ∈ IntermediateField.fixedField H,
          Algebra.trace (RatFunc k) (IntermediateField.fixedField H)
              (⟨aF, haE⟩ : IntermediateField.fixedField H) = 1 /\
          Bialgebra.counitAlgHom k A s0 = 0 /\
          sigma sF = sF + 1 /\
          ((sigma sF : F) : FractionRing A) =
            algebraMap A (FractionRing A)
              (regularCharacterTranslation q.1 s0) /\
          Module.finrank (RatFunc k) (IntermediateField.fixedField H) = p /\
          exists g : Polynomial k, exists C : BivariatePolynomial k,
            s0 ^ p - s0 = Polynomial.aeval t g /\
            reducedComultiplication (k := k) s0 = bivariateAeval t C /\
            IsNormalizedPolynomialCocycle C /\
            IsSymmetricPolynomialCocycle C /\
            IsAdditivePolynomialTwoCocycle C /\
            C ^ p - C = additiveCoboundary g /\
            IntermediateField.adjoin (RatFunc k) ({sF} : Set F) =
              IntermediateField.fixedField H /\
            Nat.card H < Nat.card (F ≃ₐ[RatFunc k] F) := by
  let K := RatFunc k
  let L := FractionRing A
  let f := primitiveFractionMap (k := k) t ht
  letI : Algebra K L := f.toRingHom.toAlgebra
  letI : IsScalarTower k K L :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  let F := separableClosure K L
  dsimp only
  intro H hH
  let action := primitiveSeparableKernelAction t ht hprimitive
  have haction := primitiveSeparableKernelAction_bijective
    htrdeg t ht hprimitive
  let J := H.comap action
  have hJ : J.map action = H :=
    Subgroup.map_comap_eq_self_of_surjective haction.2 H
  have hcomm : IsMulCommutative (F ≃ₐ[K] F) := by
    refine ⟨⟨fun sigma tau => ?_⟩⟩
    obtain ⟨q, rfl⟩ := haction.2 sigma
    obtain ⟨r, rfl⟩ := haction.2 tau
    rw [← map_mul, ← map_mul]
    congr 1
    apply MulOpposite.unop_injective
    apply Subtype.ext
    exact primitive_hopf_curve_character_mul_comm
      htrdeg t ht hprimitive r.unop.1 q.unop.1
  letI : IsMulCommutative (F ≃ₐ[K] F) := hcomm
  have hnormal : H.Normal := inferInstance
  have hstable : ∀ r : WithConv (A →ₐ[k] k), ∀ x : F,
      regularCharacterSeparableTranslation t ht hprimitive r x ∈
          IntermediateField.fixedField H ↔
        x ∈ IntermediateField.fixedField H := by
    intro r x
    exact regularCharacterSeparableTranslation_mem_fixedField_iff
      htrdeg t ht hprimitive r H x
  obtain ⟨sigma, q, a0, s0, haF, hsF, hq, hsigmaH, haE, hsE,
      htrace, hcounit, hsigma, _hadjoin, hfinrank⟩ :=
    primitive_hopf_curve_normal_index_p_regular_trace_one
      (p := p) htrdeg t ht hprimitive H hH
  have hfixT : regularCharacterTranslation q.1 t = t := by
    rw [regularCharacterTranslation_apply_of_primitive q.1 t hprimitive,
      (mem_primitiveCharacterKernel t hprimitive q.1).mp q.2,
      map_zero, zero_add]
  obtain ⟨r, hr⟩ := primitive_hopf_curve_galois_automorphism_apply
    htrdeg t ht hprimitive sigma
  have hrAction : action (MulOpposite.op r) = sigma := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    rw [primitiveSeparableKernelAction_apply]
    exact (hr x).symm
  have hrq : r = q := by
    apply MulOpposite.op_injective
    exact haction.1 (hrAction.trans hq.symm)
  have hsigmaAmbient : ∀ x : F,
      ((sigma x : F) : L) =
        primitiveFractionTranslation t ht hprimitive q x.1 := by
    intro x
    rw [← hrq]
    exact hr x
  let sF : F := ⟨algebraMap A L s0, hsF⟩
  have hsigmaRegular : ((sigma sF : F) : L) =
      algebraMap A L (regularCharacterTranslation q.1 s0) := by
    rw [hsigmaAmbient sF, primitiveFractionTranslation_algebraMap]
  obtain ⟨g, C, hAS, hC, hnormalized, hsymmetric, hadditive,
      hCAS, hadjoin, hcard⟩ :=
    primitive_hopf_curve_artin_schreier_cocycle_descent
      (p := p) htrdeg t ht hprimitive H hH sigma q s0 hcounit hsF
        hq hsigmaH hsE hsigma
  exact ⟨J, hJ, hnormal, hstable, sigma, q, a0, s0, haF, hsF, hq,
    hfixT, hsigmaAmbient, hsigmaH, haE, hsE, htrace, hcounit, hsigma,
    hsigmaRegular, hfinrank, g, C, hAS, hC, hnormalized, hsymmetric,
    hadditive, hCAS, hadjoin, hcard⟩

end

end Theory.AlgebraicGroup
