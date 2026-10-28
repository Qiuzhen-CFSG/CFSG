module

import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.GroupTheory.Sylow
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.PrimitiveCurveNormalIndexPArtinSchreier

/-!
# Rationality of the separable core of a primitive Hopf curve

Let `t` be a transcendental primitive element of a normal affine Hopf curve in
positive characteristic.  This module proves that the separable closure of
the embedded field `k(t)` in the curve's fraction field is itself a rational
function field over `k`.

The proof follows Borel, *Linear Algebraic Groups*, section 10.9 and the
algebraic sketch after Corollary 11.6.  The primitive character translations
identify the finite separable kernel with a Galois `p`-group.  A nontrivial
kernel has a subgroup of index `p`; the normal index-`p` Artin--Schreier layer
constructs a new primitive coordinate for its fixed field and strictly lowers
the character-kernel cardinality.  Strong induction therefore reaches the
trivial kernel, where the original rational-function parameter generates the
separable closure.

The essential compatibility between consecutive layers is proved here rather
than assumed.  The field range of the new primitive fraction map is the fixed
field supplied by the Artin--Schreier layer.  It is a separable intermediate
extension of the old rational-function field, so invariance of separable
closure in a separable tower, together with transport across the field-range
equivalence, identifies the old and new separable closures.  This keeps the
induction independent of any affine-line or primitive-generator
classification.
-/

namespace Theory.AlgebraicGroup

noncomputable section

universe u v

set_option linter.style.haveILetI false

variable {k : Type u} {A : Type v}
variable [Field k] [IsAlgClosed k] [CommRing A] [HopfAlgebra k A]
variable [IsDomain A] [Algebra.FiniteType k A] [IsIntegrallyClosed A]

omit [IsAlgClosed k] [Algebra.FiniteType k A] [IsIntegrallyClosed A] in
private lemma primitiveFractionMap_X
    (s : A) (hs : Transcendental k s) :
    primitiveFractionMap s hs (RatFunc.X : RatFunc k) =
      algebraMap A (FractionRing A) s := by
  rw [show (RatFunc.X : RatFunc k) =
      algebraMap (Polynomial k) (RatFunc k) Polynomial.X /
        algebraMap (Polynomial k) (RatFunc k) 1 by
          rw [map_one, div_one]
          exact RatFunc.algebraMap_X.symm,
    primitiveFractionMap_apply_div]
  simp

omit [IsAlgClosed k] [Algebra.FiniteType k A] [IsIntegrallyClosed A] in
private lemma primitiveFractionMap_fieldRange
    (s : A) (hs : Transcendental k s) :
    (primitiveFractionMap s hs).fieldRange =
      IntermediateField.adjoin k
        ({algebraMap A (FractionRing A) s} : Set (FractionRing A)) := by
  rw [AlgHom.fieldRange_eq_map, ← RatFunc.adjoin_X]
  rw [IntermediateField.adjoin_map]
  simp [primitiveFractionMap_X s hs]

omit [IsAlgClosed k] [Algebra.FiniteType k A] [IsIntegrallyClosed A] in
private lemma primitiveSeparableClosure_rebase
    (t : A) (ht : Transcendental k t)
    (s : A) (hs : Transcendental k s)
    (hsF :
      let f := primitiveFractionMap (k := k) t ht
      letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
      let F := separableClosure (RatFunc k) (FractionRing A)
      algebraMap A (FractionRing A) s ∈ F)
    (H :
      let f := primitiveFractionMap (k := k) t ht
      letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
      let F := separableClosure (RatFunc k) (FractionRing A)
      Subgroup (F ≃ₐ[RatFunc k] F))
    (hadjoin :
      let f := primitiveFractionMap (k := k) t ht
      letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
      let F := separableClosure (RatFunc k) (FractionRing A)
      IntermediateField.adjoin k
          ({(Subtype.mk (algebraMap A (FractionRing A) s) hsF : F)} : Set F) =
        (IntermediateField.fixedField H).restrictScalars k) :
    let f := primitiveFractionMap (k := k) t ht
    letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
    letI : IsScalarTower k (RatFunc k) (FractionRing A) :=
      IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
    let F := separableClosure (RatFunc k) (FractionRing A)
    forall x : FractionRing A,
      x ∈ F ↔
        @IsSeparable (RatFunc k) (FractionRing A) _ _
          (primitiveFractionMap s hs).toRingHom.toAlgebra x := by
  let f := primitiveFractionMap (k := k) t ht
  letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
  letI : IsScalarTower k (RatFunc k) (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  let F := separableClosure (RatFunc k) (FractionRing A)
  dsimp only at hsF H hadjoin ⊢
  let g := primitiveFractionMap (k := k) s hs
  let E : IntermediateField k (FractionRing A) := g.fieldRange
  have hE : E = (IntermediateField.adjoin k
      ({(Subtype.mk (algebraMap A (FractionRing A) s) hsF : F)} : Set F)).map
        (F.val.restrictScalars k) := by
    rw [show E = IntermediateField.adjoin k
        ({algebraMap A (FractionRing A) s} : Set (FractionRing A)) by
          exact primitiveFractionMap_fieldRange s hs]
    rw [IntermediateField.adjoin_map]
    simp
  have hbase (x : RatFunc k) : f x ∈ E := by
    rw [hE]
    refine ⟨algebraMap (RatFunc k) F x, ?_, ?_⟩
    · rw [hadjoin]
      exact (IntermediateField.fixedField H).algebraMap_mem x
    · rfl
  let j : RatFunc k →ₐ[k] E := f.codRestrict E.toSubalgebra hbase
  letI : Algebra (RatFunc k) E := j.toRingHom.toAlgebra
  letI : IsScalarTower k (RatFunc k) E :=
    IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  letI : IsScalarTower (RatFunc k) E (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change f x = (j x : FractionRing A)
      rfl
  have hEF : E ≤ F.restrictScalars k := by
    rw [hE, hadjoin]
    intro x hx
    obtain ⟨y, _, rfl⟩ := hx
    exact y.2
  letI : Algebra.IsSeparable (RatFunc k) E := by
    constructor
    intro x
    have hxL : (x : FractionRing A) ∈ F := hEF x.2
    exact IsSeparable.tower_bot
      (K := E) (E := FractionRing A) (mem_separableClosure_iff.mp hxL)
  have hsepOld : F =
      (separableClosure E (FractionRing A)).restrictScalars (RatFunc k) :=
    separableClosure.eq_restrictScalars_of_isSeparable
      (RatFunc k) E (FractionRing A)
  intro x
  have hOldE : x ∈ F ↔ IsSeparable E x := by
    rw [hsepOld]
    exact mem_separableClosure_iff
  rw [hOldE]
  letI : Algebra (RatFunc k) (FractionRing A) := g.toRingHom.toAlgebra
  let e : RatFunc k ≃ₐ[k] E := g.equivFieldRange
  constructor
  · intro hx
    exact IsSeparable.of_equiv_equiv e.symm.toRingEquiv
      (RingEquiv.refl (FractionRing A)) (by
        ext y
        change g (e.symm y) = (y : FractionRing A)
        exact congrArg Subtype.val (e.apply_symm_apply y)) hx
  · intro hx
    exact IsSeparable.of_equiv_equiv e.toRingEquiv
      (RingEquiv.refl (FractionRing A)) (by ext; rfl) hx

omit [IsAlgClosed k] [Algebra.FiniteType k A] [IsIntegrallyClosed A] in
private lemma primitive_adjoin_eq_restrictScalars_bot
    (t : A) (ht : Transcendental k t) :
    let f := primitiveFractionMap (k := k) t ht
    letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
    letI : IsScalarTower k (RatFunc k) (FractionRing A) :=
      IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
    let F := separableClosure (RatFunc k) (FractionRing A)
    let tF : F := ⟨algebraMap A (FractionRing A) t, by
      rw [← primitiveFractionMap_X t ht]
      exact F.algebraMap_mem (RatFunc.X : RatFunc k)⟩
    IntermediateField.adjoin k ({tF} : Set F) =
      (⊥ : IntermediateField (RatFunc k) F).restrictScalars k := by
  let f := primitiveFractionMap (k := k) t ht
  letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
  letI : IsScalarTower k (RatFunc k) (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  let F := separableClosure (RatFunc k) (FractionRing A)
  let tF : F := ⟨algebraMap A (FractionRing A) t, by
    rw [← primitiveFractionMap_X t ht]
    exact F.algebraMap_mem (RatFunc.X : RatFunc k)⟩
  let b : RatFunc k →ₐ[k] F := IsScalarTower.toAlgHom k (RatFunc k) F
  have hbX : b (RatFunc.X : RatFunc k) = tF := by
    apply Subtype.ext
    exact primitiveFractionMap_X t ht
  calc
    IntermediateField.adjoin k ({tF} : Set F) =
        IntermediateField.adjoin k ({b (RatFunc.X : RatFunc k)} : Set F) := by
          rw [hbX]
    _ = (IntermediateField.adjoin k
          ({RatFunc.X} : Set (RatFunc k))).map b := by
          rw [IntermediateField.adjoin_map]
          simp
    _ = (⊤ : IntermediateField k (RatFunc k)).map b := by
          rw [RatFunc.adjoin_X]
    _ = b.fieldRange := AlgHom.fieldRange_eq_map b |>.symm
    _ = (⊥ : IntermediateField (RatFunc k) F).restrictScalars k := by
      ext x
      simp [b, IntermediateField.mem_bot]

/-- The separable closure of the primitive rational-function field inside the
fraction field of a normal Hopf curve is generated over `k` by one
transcendental element. -/
public theorem primitive_hopf_curve_separable_core_is_rational_of_charP
    {p : Nat} [CharP k p] [Fact p.Prime]
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0) :
    let f := primitiveFractionMap (k := k) t ht
    letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
    letI : IsScalarTower k (RatFunc k) (FractionRing A) :=
      IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
    let F := separableClosure (RatFunc k) (FractionRing A)
    exists z : F, Transcendental k z ∧
      IntermediateField.adjoin k ({z} : Set F) = ⊤ := by
  classical
  letI : CharP A p :=
    charP_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective k A) p
  let P : Nat → Prop := fun n =>
    ∀ (t : A) (ht : Transcendental k t)
      (hprimitive : reducedComultiplication (k := k) t = 0),
      Nat.card (primitiveCharacterKernel t hprimitive) = n →
      let f := primitiveFractionMap (k := k) t ht
      letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
      letI : IsScalarTower k (RatFunc k) (FractionRing A) :=
        IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
      let F := separableClosure (RatFunc k) (FractionRing A)
      exists z : F, Transcendental k z ∧
        IntermediateField.adjoin k ({z} : Set F) = ⊤
  have hind : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro t ht hprimitive hcard
      let f := primitiveFractionMap (k := k) t ht
      letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
      letI : IsScalarTower k (RatFunc k) (FractionRing A) :=
        IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
      let F := separableClosure (RatFunc k) (FractionRing A)
      dsimp only
      letI : Finite (primitiveCharacterKernel t hprimitive) :=
        primitiveCharacterKernel_finite htrdeg t ht hprimitive
      letI : Module.Finite (RatFunc k) F :=
        primitive_hopf_curve_separableClosure_finite htrdeg t ht hprimitive
      letI : IsScalarTower k (RatFunc k) F :=
        IsScalarTower.of_algebraMap_eq fun x => by
          apply Subtype.ext
          exact IsScalarTower.algebraMap_apply k (RatFunc k)
            (FractionRing A) x
      letI : IsScalarTower k F (FractionRing A) :=
        IsScalarTower.of_algebraMap_eq fun x => by
          rw [IsScalarTower.algebraMap_apply k (RatFunc k) F]
          change algebraMap k (FractionRing A) x =
            f (algebraMap k (RatFunc k) x)
          exact (f.commutes x).symm
      have hgp := primitive_hopf_curve_separable_kernel_is_galois_pGroup
        (p := p) htrdeg t ht hprimitive
      letI : IsGalois (RatFunc k) F := hgp.1
      let G := F ≃ₐ[RatFunc k] F
      letI : Finite G := inferInstance
      obtain ⟨m, hm⟩ := (IsPGroup.iff_card.mp hgp.2)
      cases m with
      | zero =>
          have hcardG : Nat.card G = 1 := by simpa using hm
          have htopbot : (⊤ : Subgroup G) = ⊥ := by
            rw [Subgroup.eq_bot_iff_card]
            simpa using hcardG
          have hbotTop : (⊥ : IntermediateField (RatFunc k) F) = ⊤ := by
            calc
              (⊥ : IntermediateField (RatFunc k) F) =
                  IntermediateField.fixedField (⊤ : Subgroup G) :=
                (primitive_hopf_curve_separable_kernel_fixedField_eq_bot
                  (p := p) htrdeg t ht hprimitive).symm
              _ = IntermediateField.fixedField (⊥ : Subgroup G) := by
                rw [htopbot]
              _ = ⊤ := IntermediateField.fixedField_bot
          let tF : F := ⟨algebraMap A (FractionRing A) t, by
            rw [← primitiveFractionMap_X t ht]
            exact F.algebraMap_mem (RatFunc.X : RatFunc k)⟩
          refine ⟨tF, ?_, ?_⟩
          · apply (transcendental_algebraMap_iff F.val.injective).mp
            change Transcendental k (algebraMap A (FractionRing A) t)
            exact (transcendental_algebraMap_iff
              (FaithfulSMul.algebraMap_injective A (FractionRing A))).mpr ht
          · rw [primitive_adjoin_eq_restrictScalars_bot t ht, hbotTop]
            rfl
      | succ m =>
          obtain ⟨H, hHcard⟩ := Sylow.exists_subgroup_card_pow_prime
            (G := G) p (n := m) (by
              rw [hm, pow_succ']
              exact dvd_mul_left (p ^ m) p)
          have hHindex : H.index = p := by
            apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos : 0 < Nat.card H)
            calc
              Nat.card H * H.index = Nat.card G := H.card_mul_index
              _ = p ^ (m + 1) := hm
              _ = p ^ m * p := by rw [pow_succ]
              _ = Nat.card H * p := by rw [hHcard]
          obtain ⟨s, hs, hsp, hsF, hadjoin, hcardlt⟩ :=
            primitive_hopf_curve_normal_index_p_artin_schreier_layer
              (p := p) htrdeg t ht hprimitive H hHindex
          have hslt : Nat.card (primitiveCharacterKernel s hsp) < n := by
            rw [← hcard]
            exact hcardlt
          obtain ⟨z, hztrans, hzgen⟩ :=
            ih (Nat.card (primitiveCharacterKernel s hsp)) hslt
              s hs hsp rfl
          have hrebase := primitiveSeparableClosure_rebase
            t ht s hs hsF H hadjoin
          let Fs := @separableClosure (RatFunc k) (FractionRing A) _ _
            (primitiveFractionMap s hs).toRingHom.toAlgebra
          have hzF : (z : FractionRing A) ∈ F :=
            (hrebase (z : FractionRing A)).mpr z.2
          let zF : F := ⟨z, hzF⟩
          let toF : Fs →ₐ[k] F := {
            toFun x := ⟨x, (hrebase (x : FractionRing A)).mpr x.2⟩
            map_one' := rfl
            map_mul' _ _ := rfl
            map_zero' := rfl
            map_add' _ _ := rfl
            commutes' x := by
              apply Subtype.ext
              change algebraMap k (FractionRing A) x =
                algebraMap k (FractionRing A) x
              rfl }
          have htoF : Function.Bijective toF := by
            constructor
            · exact toF.injective
            · intro x
              refine ⟨⟨x, (hrebase (x : FractionRing A)).mp x.2⟩, ?_⟩
              rfl
          let eF : Fs ≃ₐ[k] F := AlgEquiv.ofBijective toF htoF
          have hez : eF z = zF := by
            apply Subtype.ext
            rfl
          have hmaptop :
              (⊤ : IntermediateField k Fs).map eF.toAlgHom = ⊤ := by
            rw [← AlgHom.fieldRange_eq_map, AlgHom.fieldRange_eq_top]
            exact eF.surjective
          refine ⟨zF, ?_, ?_⟩
          · intro hzalg
            apply hztrans
            have hzback := hzalg.algHom eF.symm.toAlgHom
            have heback : eF.symm zF = z := by
              calc
                eF.symm zF = eF.symm (eF z) := congrArg eF.symm hez.symm
                _ = z := eF.symm_apply_apply z
            exact heback ▸ hzback
          · calc
              IntermediateField.adjoin k ({zF} : Set F) =
                  IntermediateField.adjoin k ({eF z} : Set F) := by rw [hez]
              _ = (IntermediateField.adjoin k ({z} : Set Fs)).map
                    eF.toAlgHom := by
                rw [IntermediateField.adjoin_map]
                simp
              _ = (⊤ : IntermediateField k Fs).map eF.toAlgHom := by
                rw [hzgen]
              _ = ⊤ := hmaptop
  simpa only [P] using
    (hind (Nat.card (primitiveCharacterKernel t hprimitive))
      t ht hprimitive rfl)

end

end Theory.AlgebraicGroup
