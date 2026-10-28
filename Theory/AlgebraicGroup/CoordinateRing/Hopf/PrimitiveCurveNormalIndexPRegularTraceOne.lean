module

public import Theory.AlgebraicGroup.CoordinateRing.Hopf.PrimitiveCurveAffineSeparableTranslation

/-!
# Regular trace-one descent for primitive index-`p` layers

For a transcendental primitive coordinate on a normal affine Hopf curve in
characteristic `p`, this module constructs a regular trace-one element over
every index-`p` subgroup of the primitive separable Galois group.  It also
constructs a regular element translated by `1` by a lifted quotient
generator, while retaining membership in the subgroup fixed field and proving
that fixed field has degree `p`.  The generator is centered by subtracting its
counit, so it has counit zero without changing its translation law; adjoining
the centered generator still recovers the whole fixed field.

The primitive character action is bijective onto the Galois group, and
commutativity of primitive characters therefore makes every index-`p`
subgroup normal.  Trace surjectivity followed by denominator clearing gives a
nonzero polynomial value attained by the trace of a regular element.  Regular
character translations preserve the fixed field and turn this polynomial into
all of its Taylor translates.  The infinite character-value argument forces
their ideal to be the unit ideal, yielding a regular trace-one element.  A
generator of the cyclic Galois quotient is then lifted through the primitive
action; the weighted sum of its regular orbit translates by `1`.  Finally, its
counit is subtracted.  This scalar belongs to the base field, so fixed-field
membership, translation by `1`, and the generated intermediate field are
unchanged.

This is the regular descent input to the positive-characteristic primitive
Artin--Schreier layer.  The source route follows Borel, *Linear Algebraic
Groups*, Theorem 10.9 and the post-11.6 sketch, which refer this degree-`p`
step to SGA 3, Expose VII, Lemma 3.
-/

open scoped TensorProduct

namespace Theory.AlgebraicGroup

noncomputable section

universe u v

set_option linter.style.haveILetI false

variable {k : Type u} {A : Type v} {p : Nat}

section Characters

variable [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
variable [Algebra.FiniteType k A] [IsDomain A]

private noncomputable def quotientCharacter (J : Ideal A) [J.IsMaximal] :
    (A ⧸ J) →ₐ[k] k := by
  letI : Field (A ⧸ J) := Ideal.Quotient.field J
  letI : Algebra.FiniteType k (A ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k J)
      (Ideal.Quotient.mkₐ_surjective k J)
  letI : Module.Finite k (A ⧸ J) :=
    finite_of_finite_type_of_isJacobsonRing k (A ⧸ J)
  exact IsAlgClosed.lift

private noncomputable def characterOfMaximal (J : Ideal A) [J.IsMaximal] : A →ₐ[k] k :=
  (quotientCharacter (k := k) J).comp (Ideal.Quotient.mkₐ k J)

omit [IsDomain A] in
private lemma characterOfMaximal_eq_zero_iff_mem
    (J : Ideal A) [J.IsMaximal] (a : A) :
    characterOfMaximal (k := k) J a = 0 ↔ a ∈ J := by
  letI : Field (A ⧸ J) := Ideal.Quotient.field J
  constructor
  · intro h
    have hq : Ideal.Quotient.mk J a = 0 :=
      (quotientCharacter (k := k) J).injective
        (by simpa [characterOfMaximal] using h)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq
  · intro h
    have hq : Ideal.Quotient.mk J a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr h
    change quotientCharacter (k := k) J (Ideal.Quotient.mk J a) = 0
    rw [hq, map_zero]

private lemma eq_zero_of_forall_character_eq_zero
    (a : A) (ha : ∀ phi : A →ₐ[k] k, phi a = 0) : a = 0 := by
  letI : IsJacobsonRing A :=
    isJacobsonRing_of_finiteType (A := k) (B := A)
  have hjac : a ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson]
    apply Ideal.mem_sInf.mpr
    intro J hJ
    letI : J.IsMaximal := hJ.2
    exact (characterOfMaximal_eq_zero_iff_mem (k := k) J a).mp
      (ha (characterOfMaximal (k := k) J))
  rw [← Ideal.radical_eq_jacobson, Ideal.radical_bot_of_isReduced] at hjac
  exact Ideal.mem_bot.mp hjac

private lemma character_values_infinite
    (t : A) (ht : Transcendental k t) :
    Set.Infinite (Set.range fun phi : A →ₐ[k] k ↦ phi t) := by
  intro hfinite
  let values := hfinite.toFinset
  let q : Polynomial k := values.prod fun c ↦ Polynomial.X - Polynomial.C c
  have hqne : q ≠ 0 :=
    (Polynomial.monic_prod_X_sub_C (fun c : k ↦ c) values).ne_zero
  have hqeval : Polynomial.aeval t q = 0 := by
    apply eq_zero_of_forall_character_eq_zero (k := k)
    intro phi
    rw [← Polynomial.aeval_algHom_apply phi t q]
    have hmem : phi t ∈ values := hfinite.mem_toFinset.mpr ⟨phi, rfl⟩
    simp only [q, map_prod, Polynomial.aeval_sub, Polynomial.aeval_X,
      Polynomial.aeval_C]
    exact Finset.prod_eq_zero hmem (sub_self _)
  apply hqne
  apply (transcendental_iff_injective.mp ht)
  simpa using hqeval

private lemma span_taylor_character_values_eq_top
    (t : A) (ht : Transcendental k t) (P : Polynomial k) (hP : P ≠ 0) :
    Ideal.span (Set.range fun phi : A →ₐ[k] k ↦ Polynomial.taylor (phi t) P) = ⊤ := by
  by_contra htop
  obtain ⟨J, hJmax, hle⟩ := Ideal.exists_le_maximal _ htop
  letI : J.IsMaximal := hJmax
  let psi := characterOfMaximal (k := k) J
  let r : k := psi Polynomial.X
  have hpsi : psi = Polynomial.aeval r := by
    apply Polynomial.algHom_ext
    simp [r]
  have hvanish : ∀ phi : A →ₐ[k] k,
      Polynomial.eval r (Polynomial.taylor (phi t) P) = 0 := by
    intro phi
    have hmem : Polynomial.taylor (phi t) P ∈ J :=
      hle (Ideal.subset_span (Set.mem_range_self phi))
    have hz := (characterOfMaximal_eq_zero_iff_mem (k := k) J _).mpr hmem
    change psi (Polynomial.taylor (phi t) P) = 0 at hz
    rw [hpsi] at hz
    simpa [Polynomial.aeval_def] using hz
  let values : Set k := Set.range fun phi : A →ₐ[k] k ↦ phi t
  have hvalues : values.Infinite := character_values_infinite (k := k) t ht
  have hshift : ((fun c : k ↦ r + c) '' values).Infinite :=
    hvalues.image (fun _ _ _ _ h ↦ add_left_cancel h)
  have hroots : Set.Infinite
      {x : k | Polynomial.eval x P = Polynomial.eval x (0 : Polynomial k)} := by
    apply hshift.mono
    rintro x ⟨c, ⟨phi, rfl⟩, rfl⟩
    have hz := hvanish phi
    rw [Polynomial.taylor_eval] at hz
    simpa using hz
  exact hP (Polynomial.eq_of_infinite_eval_eq P 0 hroots)

end Characters

variable [Field k] [IsAlgClosed k] [CharP k p] [Fact p.Prime]
variable [CommRing A] [HopfAlgebra k A] [IsDomain A]
variable [Algebra.FiniteType k A] [IsIntegrallyClosed A]

private lemma primitiveSeparableGaloisGroup_isMulCommutative
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0) :
    let f := primitiveFractionMap (k := k) t ht
    letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
    let F := separableClosure (RatFunc k) (FractionRing A)
    IsMulCommutative (F ≃ₐ[RatFunc k] F) := by
  let f := primitiveFractionMap (k := k) t ht
  letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
  let F := separableClosure (RatFunc k) (FractionRing A)
  let action := primitiveSeparableKernelAction t ht hprimitive
  have haction := primitiveSeparableKernelAction_bijective
    htrdeg t ht hprimitive
  refine ⟨⟨fun sigma tau ↦ ?_⟩⟩
  obtain ⟨q, rfl⟩ := haction.2 sigma
  obtain ⟨r, rfl⟩ := haction.2 tau
  rw [← map_mul, ← map_mul]
  congr 1
  apply MulOpposite.unop_injective
  apply Subtype.ext
  exact primitive_hopf_curve_character_mul_comm
    htrdeg t ht hprimitive r.unop.1 q.unop.1

private lemma regularCharacterFixedFieldTranslation_trace
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (q : WithConv (A →ₐ[k] k)) :
    let f := primitiveFractionMap (k := k) t ht
    letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
    let F := separableClosure (RatFunc k) (FractionRing A)
    ∀ (H : Subgroup (F ≃ₐ[RatFunc k] F))
      (x : IntermediateField.fixedField H),
      primitiveRatFuncTranslation t q
          (Algebra.trace (RatFunc k) (IntermediateField.fixedField H) x) =
        Algebra.trace (RatFunc k) (IntermediateField.fixedField H)
          (regularCharacterFixedFieldTranslation htrdeg t ht hprimitive q H x) := by
  let f := primitiveFractionMap (k := k) t ht
  letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
  let F := separableClosure (RatFunc k) (FractionRing A)
  dsimp only
  intro H x
  let tauK := primitiveRatFuncTranslation t q
  let tauE := regularCharacterFixedFieldTranslation htrdeg t ht hprimitive q H
  have hcomp :
      RingHom.comp (algebraMap (RatFunc k) (IntermediateField.fixedField H))
          tauK.toRingHom =
        RingHom.comp tauE.toRingHom
          (algebraMap (RatFunc k) (IntermediateField.fixedField H)) := by
    apply RingHom.ext
    intro y
    apply Subtype.ext
    apply Subtype.ext
    simp only [RingHom.coe_comp, Function.comp_apply]
    dsimp only [tauK, tauE]
    change primitiveFractionMap t ht (primitiveRatFuncTranslation t q y) =
      (((regularCharacterFixedFieldTranslation htrdeg t ht hprimitive q H
          (algebraMap (RatFunc k) (IntermediateField.fixedField H) y) :
            IntermediateField.fixedField H) : F) : FractionRing A)
    rw [regularCharacterFixedFieldTranslation_apply,
      regularCharacterSeparableTranslation_apply]
    exact (regularCharacterFractionTranslation_primitiveFractionMap
      t ht hprimitive q y).symm
  have htrace :
      Algebra.trace (RatFunc k) (IntermediateField.fixedField H) x =
        tauK.symm (Algebra.trace (RatFunc k) (IntermediateField.fixedField H)
          (tauE x)) :=
    Algebra.trace_eq_of_equiv_equiv
      (A₁ := RatFunc k) (B₁ := IntermediateField.fixedField H)
      (A₂ := RatFunc k) (B₂ := IntermediateField.fixedField H)
      tauK tauE hcomp x
  rw [htrace, tauK.apply_symm_apply]

private lemma exists_regular_fixedField_trace_one
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0) (p : Nat)
    [CharP k p] [Fact p.Prime] :
    let f := primitiveFractionMap (k := k) t ht
    letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
    letI : IsScalarTower k (RatFunc k) (FractionRing A) :=
      IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
    let F := separableClosure (RatFunc k) (FractionRing A)
    ∀ H : Subgroup (F ≃ₐ[RatFunc k] F),
      ∃ a0 : A,
      ∃ haF : algebraMap A (FractionRing A) a0 ∈ F,
      ∃ haE : (⟨algebraMap A (FractionRing A) a0, haF⟩ : F) ∈
          IntermediateField.fixedField H,
        Algebra.trace (RatFunc k) (IntermediateField.fixedField H)
          (⟨⟨algebraMap A (FractionRing A) a0, haF⟩, haE⟩ :
            IntermediateField.fixedField H) = 1 := by
  let f := primitiveFractionMap (k := k) t ht
  letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
  letI : IsScalarTower k (RatFunc k) (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  let F := separableClosure (RatFunc k) (FractionRing A)
  dsimp only
  intro H
  letI : Module.Finite (RatFunc k) F :=
    primitive_hopf_curve_separableClosure_finite htrdeg t ht hprimitive
  letI : IsGalois (RatFunc k) F :=
    (primitive_hopf_curve_separable_kernel_is_galois_pGroup
      (p := p) htrdeg t ht hprimitive).1
  letI : IsMulCommutative (F ≃ₐ[RatFunc k] F) :=
    primitiveSeparableGaloisGroup_isMulCommutative htrdeg t ht hprimitive
  let E := IntermediateField.fixedField H
  letI : CharP E p :=
    charP_of_injective_algebraMap (algebraMap k E).injective p
  letI : Algebra (Polynomial k) A :=
    (Polynomial.aeval t).toRingHom.toAlgebra
  letI : IsScalarTower (Polynomial k) A (FractionRing A) :=
    OreLocalization.instIsScalarTower
  letI : IsScalarTower (Polynomial k) (RatFunc k) (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq fun P ↦ by
      change algebraMap A (FractionRing A) (Polynomial.aeval t P) =
        primitiveFractionMap t ht (algebraMap (Polynomial k) (RatFunc k) P)
      rw [show algebraMap (Polynomial k) (RatFunc k) P =
          algebraMap (Polynomial k) (RatFunc k) P /
            algebraMap (Polynomial k) (RatFunc k) 1 by simp,
        primitiveFractionMap_apply_div]
      simp
  let RegularTrace (P : Polynomial k) : Prop :=
    ∃ (a : A) (haF : algebraMap A (FractionRing A) a ∈ F),
    ∃ haE : (⟨algebraMap A (FractionRing A) a, haF⟩ : F) ∈ E,
      Algebra.trace (RatFunc k) E
          (⟨⟨algebraMap A (FractionRing A) a, haF⟩, haE⟩ : E) =
        algebraMap (Polynomial k) (RatFunc k) P
  have hpolyB (P : Polynomial k) :
      algebraMap A (FractionRing A) (Polynomial.aeval t P) =
        algebraMap (RatFunc k) (FractionRing A)
          (algebraMap (Polynomial k) (RatFunc k) P) := by
    calc
      algebraMap A (FractionRing A) (Polynomial.aeval t P) =
          algebraMap (Polynomial k) (FractionRing A) P :=
        (IsScalarTower.algebraMap_apply
          (Polynomial k) A (FractionRing A) P).symm
      _ = algebraMap (RatFunc k) (FractionRing A)
          (algebraMap (Polynomial k) (RatFunc k) P) :=
        IsScalarTower.algebraMap_apply
          (Polynomial k) (RatFunc k) (FractionRing A) P
  let traceIdeal : Ideal (Polynomial k) :=
    { carrier := {P | RegularTrace P}
      zero_mem' := by
        have hzeroF : algebraMap A (FractionRing A) (0 : A) ∈ F := by simp
        have hzeroEq :
            (⟨algebraMap A (FractionRing A) (0 : A), hzeroF⟩ : F) = 0 := by
          ext
          simp
        have hzeroE : (⟨algebraMap A (FractionRing A) (0 : A), hzeroF⟩ : F) ∈ E :=
          hzeroEq.symm ▸ E.zero_mem
        refine ⟨0, hzeroF, hzeroE, ?_⟩
        have hzeroEEq :
            (⟨⟨algebraMap A (FractionRing A) (0 : A), hzeroF⟩, hzeroE⟩ : E) = 0 := by
          ext
          simp
        rw [hzeroEEq, map_zero, map_zero]
      add_mem' := by
        intro P Q hP hQ
        rcases hP with ⟨a, haF, haE, htraceA⟩
        rcases hQ with ⟨b, hbF, hbE, htraceB⟩
        have habF : algebraMap A (FractionRing A) (a + b) ∈ F := by
          simpa using F.add_mem haF hbF
        have habEq :
            (⟨algebraMap A (FractionRing A) (a + b), habF⟩ : F) =
              (⟨algebraMap A (FractionRing A) a, haF⟩ : F) +
              (⟨algebraMap A (FractionRing A) b, hbF⟩ : F) := by
          ext
          simp
        have habE : (⟨algebraMap A (FractionRing A) (a + b), habF⟩ : F) ∈ E :=
          habEq.symm ▸ E.add_mem haE hbE
        refine ⟨a + b, habF, habE, ?_⟩
        rw [show (⟨⟨algebraMap A (FractionRing A) (a + b), habF⟩, habE⟩ : E) =
              (⟨⟨algebraMap A (FractionRing A) a, haF⟩, haE⟩ : E) +
              (⟨⟨algebraMap A (FractionRing A) b, hbF⟩, hbE⟩ : E) by
                ext
                exact congrArg Subtype.val habEq,
            map_add, htraceA, htraceB, map_add]
      smul_mem' := by
        intro P Q hQ
        rcases hQ with ⟨a, haF, haE, htraceA⟩
        let c := algebraMap (Polynomial k) (RatFunc k) P
        have hPaF :
            algebraMap A (FractionRing A) (Polynomial.aeval t P * a) ∈ F := by
          rw [map_mul, hpolyB]
          exact F.mul_mem (F.algebraMap_mem c) haF
        have hPaEq :
            (⟨algebraMap A (FractionRing A) (Polynomial.aeval t P * a), hPaF⟩ : F) =
              algebraMap (RatFunc k) F c *
                (⟨algebraMap A (FractionRing A) a, haF⟩ : F) := by
          ext
          simp [c, hpolyB]
        have hPaE :
            (⟨algebraMap A (FractionRing A) (Polynomial.aeval t P * a), hPaF⟩ : F) ∈ E :=
          hPaEq.symm ▸ E.mul_mem (E.algebraMap_mem c) haE
        refine ⟨Polynomial.aeval t P * a, hPaF, hPaE, ?_⟩
        rw [show
              (⟨⟨algebraMap A (FractionRing A)
                    (Polynomial.aeval t P * a), hPaF⟩, hPaE⟩ : E) =
                c • (⟨⟨algebraMap A (FractionRing A) a, haF⟩, haE⟩ : E) by
                  ext
                  exact congrArg Subtype.val hPaEq,
            map_smul, htraceA]
        simp [c] }
  obtain ⟨x, hxtrace⟩ :=
    Algebra.trace_surjective (RatFunc k) E (1 : RatFunc k)
  have hxalgK : IsAlgebraic (RatFunc k) x.1.1 :=
    (IsSeparable.isIntegral x.1.2).isAlgebraic
  have hxalg : IsAlgebraic (Polynomial k) x.1.1 :=
    (IsFractionRing.isAlgebraic_iff
      (Polynomial k) (RatFunc k) (FractionRing A)).2 hxalgK
  obtain ⟨d, hdne, hdint⟩ := hxalg.exists_integral_multiple
  have hdintA : IsIntegral A (d • x.1.1) := hdint.tower_top
  obtain ⟨a, ha⟩ :=
    (isIntegrallyClosed_iff (FractionRing A)).mp
      (inferInstance : IsIntegrallyClosed A) hdintA
  have hdmem : d ∈ traceIdeal := by
    let c : RatFunc k := algebraMap (Polynomial k) (RatFunc k) d
    let y : E := c • x
    have hyval : (y.1.1 : FractionRing A) = d • x.1.1 := by
      simp only [y, Algebra.smul_def]
      change algebraMap (RatFunc k) (FractionRing A) c * x.1.1 =
        algebraMap (Polynomial k) (FractionRing A) d * x.1.1
      rw [show algebraMap (RatFunc k) (FractionRing A) c =
          algebraMap (Polynomial k) (FractionRing A) d by
        exact (IsScalarTower.algebraMap_apply
          (Polynomial k) (RatFunc k) (FractionRing A) d).symm]
    have haF : algebraMap A (FractionRing A) a ∈ F := by
      rw [ha, ← hyval]
      exact y.1.2
    have haFEq :
        (⟨algebraMap A (FractionRing A) a, haF⟩ : F) = y.1 := by
      ext
      exact ha.trans hyval.symm
    have haE : (⟨algebraMap A (FractionRing A) a, haF⟩ : F) ∈ E :=
      haFEq.symm ▸ y.2
    refine ⟨a, haF, haE, ?_⟩
    have haEEq :
        (⟨⟨algebraMap A (FractionRing A) a, haF⟩, haE⟩ : E) = y := by
      ext
      exact congrArg Subtype.val haFEq
    rw [haEEq]
    change Algebra.trace (RatFunc k) E (c • x) = _
    rw [map_smul, hxtrace]
    simp [c]
  have htranslations :
      Set.range (fun phi : A →ₐ[k] k ↦ Polynomial.taylor (phi t) d) ⊆
        traceIdeal := by
    rintro P ⟨phi, rfl⟩
    rcases hdmem with ⟨a, haF, haE, htrace⟩
    let q : WithConv (A →ₐ[k] k) := WithConv.toConv phi
    let a' : A := regularCharacterTranslation q a
    have ha'F : algebraMap A (FractionRing A) a' ∈ F := by
      rw [← regularCharacterFractionTranslation_algebraMap]
      exact (regularCharacterFractionTranslation_isSeparable_iff
        t ht hprimitive q (algebraMap A (FractionRing A) a)).2 haF
    have haFEq :
        (⟨algebraMap A (FractionRing A) a', ha'F⟩ : F) =
          regularCharacterSeparableTranslation t ht hprimitive q
            (⟨algebraMap A (FractionRing A) a, haF⟩ : F) := by
      ext
      rw [regularCharacterSeparableTranslation_apply,
        regularCharacterFractionTranslation_algebraMap]
    have ha'E : (⟨algebraMap A (FractionRing A) a', ha'F⟩ : F) ∈ E :=
      haFEq.symm ▸
        (regularCharacterSeparableTranslation_mem_fixedField_iff
          htrdeg t ht hprimitive q H _).2 haE
    refine ⟨a', ha'F, ha'E, ?_⟩
    have haEEq :
        (⟨⟨algebraMap A (FractionRing A) a', ha'F⟩, ha'E⟩ : E) =
          regularCharacterFixedFieldTranslation
            htrdeg t ht hprimitive q H
              (⟨⟨algebraMap A (FractionRing A) a, haF⟩, haE⟩ : E) := by
      ext
      rw [regularCharacterFixedFieldTranslation_apply]
      exact congrArg Subtype.val haFEq
    rw [haEEq, ← regularCharacterFixedFieldTranslation_trace
      htrdeg t ht hprimitive q H, htrace,
      primitiveRatFuncTranslation_algebraMap]
  have hspan := span_taylor_character_values_eq_top t ht d hdne
  have htop : traceIdeal = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact Ideal.span_le.2 htranslations
  have hone : (1 : Polynomial k) ∈ traceIdeal := by
    rw [htop]
    simp
  rcases hone with ⟨a0, haF, haE, htrace⟩
  refine ⟨a0, haF, haE, ?_⟩
  simpa using htrace

private lemma weighted_orbit_sum_translate
    {K L : Type*} [Field K] [Field L] [Algebra K L] [CharP L p]
    (tau : L ≃ₐ[K] L) (a : L)
    (hperiod : (tau ^ p) a = a)
    (hsum : ∑ i ∈ Finset.range p, (tau ^ i) a = 1) :
    tau (-∑ i ∈ Finset.range p, (i : L) * (tau ^ i) a) =
      -∑ i ∈ Finset.range p, (i : L) * (tau ^ i) a + 1 := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp0
  have hmap (i : Nat) : tau ((tau ^ i) a) = (tau ^ (i + 1)) a := by
    rw [pow_succ']
    rfl
  rw [map_neg, map_sum]
  simp_rw [map_mul, map_natCast, hmap]
  change -(∑ i ∈ Finset.range (n + 1), (i : L) * (tau ^ (i + 1)) a) =
    -(∑ i ∈ Finset.range (n + 1), (i : L) * (tau ^ i) a) + 1
  let x : Nat → L := fun i ↦ (tau ^ i) a
  have hleft :
      (∑ i ∈ Finset.range (n + 1), (i : L) * x (i + 1)) =
        (∑ i ∈ Finset.range n, (i : L) * x (i + 1)) +
          (n : L) * x (n + 1) := by
    simpa using Finset.sum_range_succ (fun i ↦ (i : L) * x (i + 1)) n
  have hweight :
      (∑ i ∈ Finset.range (n + 1), (i : L) * x i) =
        ∑ i ∈ Finset.range n, ((i + 1 : Nat) : L) * x (i + 1) := by
    rw [Finset.sum_range_succ']
    simp
  have hsplit :
      (∑ i ∈ Finset.range n, ((i + 1 : Nat) : L) * x (i + 1)) =
        (∑ i ∈ Finset.range n, (i : L) * x (i + 1)) +
          ∑ i ∈ Finset.range n, x (i + 1) := by
    simp_rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Finset.sum_add_distrib]
  have hsum' : x 0 + ∑ i ∈ Finset.range n, x (i + 1) = 1 := by
    simpa [x, Finset.sum_range_succ', add_comm] using hsum
  have hpcast : ((n + 1 : Nat) : L) = 0 := CharP.cast_eq_zero L (n + 1)
  have hn : (n : L) * a = -a := by
    rw [Nat.cast_add, Nat.cast_one] at hpcast
    calc
      (n : L) * a = (((n : L) + 1) * a) - a := by ring
      _ = -a := by rw [hpcast, zero_mul, zero_sub]
  change -(∑ i ∈ Finset.range (n + 1), (i : L) * x (i + 1)) =
    -(∑ i ∈ Finset.range (n + 1), (i : L) * x i) + 1
  have hxperiod : x (n + 1) = a := by simpa [x] using hperiod
  have hxzero : x 0 = a := by simp [x]
  rw [hleft, hweight, hsplit]
  rw [hxperiod]
  rw [hn]
  rw [hxzero] at hsum'
  linear_combination hsum'

/-- The uncentered weighted-orbit construction used by
`primitive_hopf_curve_normal_index_p_regular_trace_one`. -/
private theorem primitive_hopf_curve_normal_index_p_regular_trace_one_uncentered
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0) :
    let f := primitiveFractionMap (k := k) t ht
    letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
    letI : IsScalarTower k (RatFunc k) (FractionRing A) :=
      IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
    let F := separableClosure (RatFunc k) (FractionRing A)
    forall H : Subgroup (F ≃ₐ[RatFunc k] F), H.index = p ->
      exists sigma : F ≃ₐ[RatFunc k] F,
      exists q : primitiveCharacterKernel t hprimitive,
      exists a0 s0 : A,
      exists haF : algebraMap A (FractionRing A) a0 ∈ F,
      exists hsF : algebraMap A (FractionRing A) s0 ∈ F,
        primitiveSeparableKernelAction t ht hprimitive
            (MulOpposite.op q) = sigma /\
        sigma ∉ H /\
        let aF : F := ⟨algebraMap A (FractionRing A) a0, haF⟩
        let sF : F := ⟨algebraMap A (FractionRing A) s0, hsF⟩
        exists haE : aF ∈ IntermediateField.fixedField H,
        exists _hsE : sF ∈ IntermediateField.fixedField H,
          Algebra.trace (RatFunc k) (IntermediateField.fixedField H)
              (⟨aF, haE⟩ : IntermediateField.fixedField H) = 1 /\
          sigma sF = sF + 1 /\
          Module.finrank (RatFunc k) (IntermediateField.fixedField H) = p := by
  let f := primitiveFractionMap (k := k) t ht
  letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
  letI : IsScalarTower k (RatFunc k) (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  let F := separableClosure (RatFunc k) (FractionRing A)
  dsimp only
  intro H hH
  letI : Module.Finite (RatFunc k) F :=
    primitive_hopf_curve_separableClosure_finite htrdeg t ht hprimitive
  letI : IsGalois (RatFunc k) F :=
    (primitive_hopf_curve_separable_kernel_is_galois_pGroup
      (p := p) htrdeg t ht hprimitive).1
  letI : IsMulCommutative (F ≃ₐ[RatFunc k] F) :=
    primitiveSeparableGaloisGroup_isMulCommutative htrdeg t ht hprimitive
  let E := IntermediateField.fixedField H
  letI : CharP E p :=
    charP_of_injective_algebraMap (algebraMap k E).injective p
  have hfinrank : Module.finrank (RatFunc k) E = p := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index F E,
      IntermediateField.fixingSubgroup_fixedField H, hH]
  have hqcard : Nat.card ((F ≃ₐ[RatFunc k] F) ⧸ H) = p := by
    rw [← H.index_eq_card, hH]
  letI : IsCyclic ((F ≃ₐ[RatFunc k] F) ⧸ H) :=
    isCyclic_of_prime_card hqcard
  obtain ⟨g, hg⟩ :=
    IsCyclic.exists_generator (α := (F ≃ₐ[RatFunc k] F) ⧸ H)
  obtain ⟨sigma, hsigma⟩ := QuotientGroup.mk'_surjective H g
  have hg_ne_one : g ≠ 1 := by
    intro hg1
    have hcard_one : Nat.card ((F ≃ₐ[RatFunc k] F) ⧸ H) = 1 := by
      apply Nat.card_eq_one_iff_unique.mpr
      refine ⟨?_, ⟨1⟩⟩
      constructor
      intro x y
      obtain ⟨z, hz⟩ := hg x
      obtain ⟨w, hw⟩ := hg y
      rw [← hz, ← hw, hg1]
      simp
    exact (Fact.out : p.Prime).ne_one (hqcard ▸ hcard_one)
  have hsigma_not_mem : sigma ∉ H := by
    intro hsigma_mem
    apply hg_ne_one
    rw [← hsigma]
    exact (QuotientGroup.eq_one_iff sigma).mpr hsigma_mem
  obtain ⟨qop, hqop⟩ :=
    (primitiveSeparableKernelAction_bijective
      htrdeg t ht hprimitive).2 sigma
  let q : primitiveCharacterKernel t hprimitive := qop.unop
  obtain ⟨a0, haF, haE, htrace⟩ :=
    exists_regular_fixedField_trace_one
      htrdeg t ht hprimitive p H
  let aF : F := ⟨algebraMap A (FractionRing A) a0, haF⟩
  let aE : E := ⟨aF, haE⟩
  let tau : E ≃ₐ[RatFunc k] E :=
    IsGalois.normalAutEquivQuotient H g
  have htau_generator : ∀ rho : E ≃ₐ[RatFunc k] E,
      rho ∈ Subgroup.zpowers tau := by
    intro rho
    obtain ⟨n, hn⟩ := hg
      ((IsGalois.normalAutEquivQuotient H).symm rho)
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨n, ?_⟩
    calc
      tau ^ n = (IsGalois.normalAutEquivQuotient H) (g ^ n) := by
        rw [map_zpow]
      _ = (IsGalois.normalAutEquivQuotient H)
          ((IsGalois.normalAutEquivQuotient H).symm rho) :=
        congrArg (IsGalois.normalAutEquivQuotient H) hn
      _ = rho := (IsGalois.normalAutEquivQuotient H).apply_symm_apply rho
  have htau_order : orderOf tau = p := by
    rw [orderOf_eq_card_of_forall_mem_zpowers htau_generator,
      IsGalois.card_aut_eq_finrank, hfinrank]
  have htau_p : tau ^ p = 1 := by
    rw [← htau_order]
    exact pow_orderOf_eq_one tau
  have hpows_bijective : Function.Bijective
      (fun i : Fin p ↦ tau ^ (i : Nat)) := by
    apply (Fintype.bijective_iff_injective_and_card _).2
    constructor
    · intro i j hij
      apply Fin.ext
      exact pow_injOn_Iio_orderOf
        (htau_order.symm ▸ i.isLt) (htau_order.symm ▸ j.isLt) hij
    · rw [Fintype.card_fin, ← Nat.card_eq_fintype_card,
        IsGalois.card_aut_eq_finrank, hfinrank]
  have horbit_sum :
      ∑ i ∈ Finset.range p, (tau ^ i) aE = 1 := by
    rw [← Fin.sum_univ_eq_sum_range]
    calc
      (∑ i : Fin p, (tau ^ (i : Nat)) aE) =
          ∑ rho : E ≃ₐ[RatFunc k] E, rho aE :=
        hpows_bijective.sum_comp (fun rho ↦ rho aE)
      _ = 1 := by
        rw [← trace_eq_sum_automorphisms, htrace]
        simp
  have hperiod : (tau ^ p) aE = aE := by
    have := congrArg (fun e : E ≃ₐ[RatFunc k] E ↦ e aE) htau_p
    simpa using this
  have hweighted :
      tau (-∑ i ∈ Finset.range p, (i : E) * (tau ^ i) aE) =
        -∑ i ∈ Finset.range p, (i : E) * (tau ^ i) aE + 1 :=
    weighted_orbit_sum_translate (p := p) tau aE hperiod
      (by simpa using horbit_sum)
  let r (i : Nat) : A :=
    regularCharacterTranslation (qop ^ i).unop.1 a0
  have hrF (i : Nat) : algebraMap A (FractionRing A) (r i) ∈ F := by
    rw [← primitiveFractionTranslation_algebraMap]
    exact (primitiveSeparableKernelAction_apply
      t ht hprimitive (qop ^ i) aF) ▸
        ((primitiveSeparableKernelAction t ht hprimitive) (qop ^ i) aF).2
  have hrFEq (i : Nat) :
      (⟨algebraMap A (FractionRing A) (r i), hrF i⟩ : F) =
        (sigma ^ i) aF := by
    apply Subtype.ext
    calc
      algebraMap A (FractionRing A) (r i) =
          primitiveFractionTranslation t ht hprimitive (qop ^ i).unop aF.1 :=
        (primitiveFractionTranslation_algebraMap
          t ht hprimitive (qop ^ i).unop a0).symm
      _ = (((primitiveSeparableKernelAction t ht hprimitive) (qop ^ i)) aF).1 :=
        (primitiveSeparableKernelAction_apply
          t ht hprimitive (qop ^ i) aF).symm
      _ = ((sigma ^ i) aF).1 := by rw [map_pow, hqop]
  have htau_sigma :
      tau = (AlgEquiv.restrictNormalHom E) sigma := by
    calc
      tau = IsGalois.normalAutEquivQuotient H
          ((QuotientGroup.mk' H) sigma) :=
        congrArg (IsGalois.normalAutEquivQuotient H) hsigma.symm
      _ = (AlgEquiv.restrictNormalHom E) sigma :=
        IsGalois.normalAutEquivQuotient_apply H sigma
  have horbitE (i : Nat) :
      (((tau ^ i) aE : E) : F) = (sigma ^ i) aF := by
    rw [htau_sigma, ← map_pow]
    exact AlgEquiv.restrictNormalHom_apply E (sigma ^ i) aE
  have horbitB (i : Nat) :
      algebraMap A (FractionRing A) (r i) =
        ((((tau ^ i) aE : E) : F) : FractionRing A) := by
    exact congrArg Subtype.val ((hrFEq i).trans (horbitE i).symm)
  let s0 : A := -∑ i ∈ Finset.range p, (i : A) * r i
  let wE : E :=
    -∑ i ∈ Finset.range p, (i : E) * (tau ^ i) aE
  have hsB : algebraMap A (FractionRing A) s0 = (wE.1.1 : FractionRing A) := by
    have hs0B : algebraMap A (FractionRing A) s0 =
        -(∑ i ∈ Finset.range p, (i : FractionRing A) *
          algebraMap A (FractionRing A) (r i)) := by
      simp [s0]
    have hwB : (wE.1.1 : FractionRing A) =
        -(∑ i ∈ Finset.range p, (i : FractionRing A) *
          ((((tau ^ i) aE : E) : F) : FractionRing A)) := by
      change (F.val.comp E.val) wE = _
      simp [wE]
    rw [hs0B, hwB]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [horbitB]
  have hsF : algebraMap A (FractionRing A) s0 ∈ F :=
    hsB.symm ▸ wE.1.2
  let sF : F := ⟨algebraMap A (FractionRing A) s0, hsF⟩
  have hsFEq : sF = wE.1 := by
    ext
    exact hsB
  have hsE : sF ∈ E := hsFEq.symm ▸ wE.2
  have hweighted' : tau wE = wE + 1 := by
    simpa [wE] using hweighted
  have hshift : sigma sF = sF + 1 := by
    calc
      sigma sF = sigma wE.1 := congrArg sigma hsFEq
      _ = (tau wE : E).1 := by
        rw [htau_sigma]
        exact (AlgEquiv.restrictNormalHom_apply E sigma wE).symm
      _ = (wE + 1 : E).1 := congrArg Subtype.val hweighted'
      _ = sF + 1 := by
        rw [hsFEq]
        apply Subtype.ext
        rfl
  refine ⟨sigma, q, a0, s0, haF, hsF, ?_, hsigma_not_mem, ?_⟩
  · simpa [q] using hqop
  refine ⟨haE, hsE, ?_, hshift, hfinrank⟩
  simpa [aF, aE] using htrace

private lemma adjoin_eq_fixedField_of_prime_index
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    {p : Nat} (hp : p.Prime)
    (H : Subgroup (E ≃ₐ[K] E)) (hH : H.index = p)
    (sigma : E ≃ₐ[K] E) (s : E)
    (hs : s ∈ IntermediateField.fixedField H)
    (hsigma : sigma s = s + 1) :
    IntermediateField.adjoin K ({s} : Set E) =
      IntermediateField.fixedField H := by
  let L := IntermediateField.adjoin K ({s} : Set E)
  let M := IntermediateField.fixedField H
  have hLM : L ≤ M := by
    rw [IntermediateField.adjoin_le_iff]
    exact Set.singleton_subset_iff.mpr hs
  have hsnot : s ∉ (⊥ : IntermediateField K E) := by
    intro hsbot
    obtain ⟨x, hx⟩ := hsbot
    have hfix : sigma s = s := by
      rw [← hx]
      exact sigma.commutes x
    have hone : (1 : E) = 0 := by
      apply add_left_cancel (a := s)
      simpa using hsigma.symm.trans hfix
    exact one_ne_zero hone
  have hLne : Module.finrank K L ≠ 1 := by
    intro hfin
    exact hsnot ((IntermediateField.finrank_adjoin_simple_eq_one_iff).mp hfin)
  have hMtop : Module.finrank M E = Nat.card H :=
    by simpa [M] using
      (IntermediateField.finrank_fixedField_eq_card (H := H))
  have hKtop : Module.finrank K E = Nat.card (E ≃ₐ[K] E) := by
    rw [IsGalois.card_aut_eq_finrank]
  have hcard : Nat.card H * p = Nat.card (E ≃ₐ[K] E) := by
    rw [← H.card_mul_index, hH]
  have hKM : Module.finrank K M = p := by
    have htower := Module.finrank_mul_finrank K M E
    rw [hMtop, hKtop, ← hcard] at htower
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos : 0 < Nat.card H) (by
      simpa [mul_comm] using htower)
  have hLd : Module.finrank K L ∣ p := by
    rw [← hKM]
    exact IntermediateField.finrank_dvd_of_le_right hLM
  have hL : Module.finrank K L = p :=
    ((Nat.dvd_prime hp).mp hLd).resolve_left hLne
  exact IntermediateField.eq_of_le_of_finrank_eq hLM (hL.trans hKM.symm)

/-- A regular trace-one element and a counit-zero regular additive generator
for every index-`p` fixed-field layer of the primitive separable Galois group.
The centered generator still generates the full fixed field. -/
public theorem primitive_hopf_curve_normal_index_p_regular_trace_one
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0) :
    let f := primitiveFractionMap (k := k) t ht
    letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
    letI : IsScalarTower k (RatFunc k) (FractionRing A) :=
      IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
    let F := separableClosure (RatFunc k) (FractionRing A)
    forall H : Subgroup (F ≃ₐ[RatFunc k] F), H.index = p ->
      exists sigma : F ≃ₐ[RatFunc k] F,
      exists q : primitiveCharacterKernel t hprimitive,
      exists a0 s0 : A,
      exists haF : algebraMap A (FractionRing A) a0 ∈ F,
      exists hsF : algebraMap A (FractionRing A) s0 ∈ F,
        primitiveSeparableKernelAction t ht hprimitive
            (MulOpposite.op q) = sigma /\
        sigma ∉ H /\
        let aF : F := ⟨algebraMap A (FractionRing A) a0, haF⟩
        let sF : F := ⟨algebraMap A (FractionRing A) s0, hsF⟩
        exists haE : aF ∈ IntermediateField.fixedField H,
        exists _hsE : sF ∈ IntermediateField.fixedField H,
          Algebra.trace (RatFunc k) (IntermediateField.fixedField H)
              (⟨aF, haE⟩ : IntermediateField.fixedField H) = 1 /\
          Bialgebra.counitAlgHom k A s0 = 0 /\
          sigma sF = sF + 1 /\
          IntermediateField.adjoin (RatFunc k) ({sF} : Set F) =
            IntermediateField.fixedField H /\
          Module.finrank (RatFunc k) (IntermediateField.fixedField H) = p := by
  let K := RatFunc k
  let L := FractionRing A
  let f := primitiveFractionMap (k := k) t ht
  letI : Algebra K L := f.toRingHom.toAlgebra
  letI : IsScalarTower k K L :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  let F := separableClosure K L
  letI : Module.Finite K F :=
    primitive_hopf_curve_separableClosure_finite htrdeg t ht hprimitive
  letI : IsGalois K F :=
    (primitive_hopf_curve_separable_kernel_is_galois_pGroup
      (p := p) htrdeg t ht hprimitive).1
  dsimp only
  intro H hH
  obtain ⟨sigma, q, a0, sRaw, haF, hsRawF, hq, hsigmaH,
      haE, hsRawE, htrace, hsigmaRaw, hfinrank⟩ :=
    primitive_hopf_curve_normal_index_p_regular_trace_one_uncentered
      (p := p) htrdeg t ht hprimitive H hH
  let c : k := Bialgebra.counitAlgHom k A sRaw
  let s0 : A := sRaw - algebraMap k A c
  have hscalarF : algebraMap A L (algebraMap k A c) ∈ F := by
    have hscalar : algebraMap A L (algebraMap k A c) =
        algebraMap K L (algebraMap k K c) := by
      rw [← IsScalarTower.algebraMap_apply k A L,
        ← IsScalarTower.algebraMap_apply k K L]
    rw [hscalar]
    exact F.algebraMap_mem _
  have hsF : algebraMap A L s0 ∈ F := by
    simpa [s0, map_sub] using F.sub_mem hsRawF hscalarF
  let rawF : F := ⟨algebraMap A L sRaw, hsRawF⟩
  let scalarF : F := ⟨algebraMap A L (algebraMap k A c), hscalarF⟩
  let sF : F := ⟨algebraMap A L s0, hsF⟩
  have hscalarFEq : scalarF = algebraMap K F (algebraMap k K c) := by
    apply Subtype.ext
    change algebraMap A L (algebraMap k A c) =
      algebraMap K L (algebraMap k K c)
    rw [← IsScalarTower.algebraMap_apply k A L,
      ← IsScalarTower.algebraMap_apply k K L]
  have hsFEq : sF = rawF - scalarF := by
    apply Subtype.ext
    simp [sF, rawF, scalarF, s0]
  have hscalarE : scalarF ∈ IntermediateField.fixedField H := by
    rw [hscalarFEq]
    exact (IntermediateField.fixedField H).algebraMap_mem _
  have hsE : sF ∈ IntermediateField.fixedField H := by
    rw [hsFEq]
    exact (IntermediateField.fixedField H).sub_mem hsRawE hscalarE
  have hcounit : Bialgebra.counitAlgHom k A s0 = 0 := by
    simp [s0, c]
  have hsigmaScalar : sigma scalarF = scalarF := by
    rw [hscalarFEq]
    exact sigma.commutes _
  have hsigma : sigma sF = sF + 1 := by
    calc
      sigma sF = sigma (rawF - scalarF) := congrArg sigma hsFEq
      _ = sigma rawF - sigma scalarF := map_sub sigma rawF scalarF
      _ = (rawF + 1) - scalarF := by rw [hsigmaRaw, hsigmaScalar]
      _ = (rawF - scalarF) + 1 := by ring
      _ = sF + 1 := by rw [hsFEq]
  have hadjoin : IntermediateField.adjoin K ({sF} : Set F) =
      IntermediateField.fixedField H :=
    adjoin_eq_fixedField_of_prime_index
      (Fact.out : p.Prime) H hH sigma sF hsE hsigma
  refine ⟨sigma, q, a0, s0, haF, hsF, hq, hsigmaH, haE, hsE,
    htrace, hcounit, hsigma, hadjoin, hfinrank⟩

end

end Theory.AlgebraicGroup
