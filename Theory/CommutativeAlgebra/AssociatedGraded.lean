module

public import Theory.CommutativeAlgebra.HilbertSamuel
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Associated graded rings and Hilbert--Samuel polynomials

For an ideal `I` in a Noetherian local ring, this module constructs the associated
graded ring `⊕ n, I ^ n / I ^ (n + 1)` as a commutative graded algebra over `R / I`.
When `I` is an ideal of definition, its homogeneous pieces have finite length and
Hilbert--Serre supplies their eventual numerical polynomial. Summing the exact
successive-quotient sequence then gives the cumulative Hilbert--Samuel polynomial.

The public associated-graded ring, its residue-field algebra and homogeneous-component
API are available to later arguments that compare it with polynomial rings; the
quotient-lift implementation remains private. The final existence and generator-bound
results are the reusable input for the maximal-ideal degree theorem.
This is the associated-graded reduction in the proof of Stacks Project,
Proposition 10.60.9 (tag 00KQ).
-/

namespace HilbertSamuel

noncomputable section

open Filter

set_option maxHeartbeats 800000

private abbrev IdealPow {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :=
  (I ^ n : Submodule R R)

private abbrev IdealPowSuccessor {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) : Submodule R (IdealPow I n) :=
  Submodule.comap (IdealPow I n).subtype (I ^ (n + 1) : Submodule R R)

/-- The degree-`n` component of the associated graded ring of `I`. -/
public abbrev AssociatedGradedPiece {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :=
  (I ^ n : Submodule R R) ⧸
    Submodule.comap ((I ^ n : Submodule R R).subtype) (I ^ (n + 1) : Submodule R R)

private def idealPowMul {R : Type*} [CommRing R] (I : Ideal R) (i j : ℕ) :
    IdealPow I i →ₗ[R] IdealPow I j →ₗ[R] IdealPow I (i + j) where
  toFun a :=
    { toFun := fun b => ⟨(a : R) * (b : R), by
        change (a : R) * (b : R) ∈ I ^ (i + j)
        simpa only [pow_add] using Ideal.mul_mem_mul a.property b.property⟩
      map_add' := fun b c => by
        ext
        exact mul_add (a : R) (b : R) (c : R)
      map_smul' := fun r b => by
        ext
        change (a : R) * (r * (b : R)) = r * ((a : R) * (b : R))
        ac_rfl }
  map_add' a b := by
    ext c
    exact add_mul (a : R) (b : R) (c : R)
  map_smul' r a := by
    ext b
    change (r * (a : R)) * (b : R) = r * ((a : R) * (b : R))
    exact mul_assoc r (a : R) (b : R)

private def idealPowMulToQuotient {R : Type*} [CommRing R]
    (I : Ideal R) (i j : ℕ) :
    IdealPow I i →ₗ[R] IdealPow I j →ₗ[R] AssociatedGradedPiece I (i + j) where
  toFun a := (IdealPowSuccessor I (i + j)).mkQ.comp (idealPowMul I i j a)
  map_add' a b := by
    ext c
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply, map_add]
  map_smul' r a := by
    ext b
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
      RingHom.id_apply, map_smul]

private lemma idealPowSuccessor_le_mul_ker_left {R : Type*} [CommRing R]
    (I : Ideal R) (i j : ℕ) :
    IdealPowSuccessor I i ≤ LinearMap.ker (idealPowMulToQuotient I i j) := by
  intro a ha
  rw [LinearMap.mem_ker]
  ext b
  change Submodule.Quotient.mk ((idealPowMul I i j a) b) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  change (a : R) * (b : R) ∈ I ^ (i + j + 1)
  have ha' : (a : R) ∈ I ^ (i + 1) := ha
  have hmul : (a : R) * (b : R) ∈ I ^ ((i + 1) + j) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul ha' b.property
  simpa only [show i + j + 1 = (i + 1) + j by omega] using hmul

private lemma idealPowSuccessor_le_mul_ker_right {R : Type*} [CommRing R]
    (I : Ideal R) (i j : ℕ) :
    IdealPowSuccessor I j ≤ LinearMap.ker (idealPowMulToQuotient I i j).flip := by
  intro b hb
  rw [LinearMap.mem_ker]
  ext a
  change Submodule.Quotient.mk ((idealPowMul I i j a) b) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  change (a : R) * (b : R) ∈ I ^ (i + j + 1)
  have hb' : (b : R) ∈ I ^ (j + 1) := hb
  have hmul : (a : R) * (b : R) ∈ I ^ (i + (j + 1)) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul a.property hb'
  simpa only [show i + j + 1 = i + (j + 1) by omega] using hmul

/-- Multiplication of homogeneous classes in the associated graded ring. -/
public def associatedGradedPieceMul {R : Type*} [CommRing R] (I : Ideal R) (i j : ℕ) :
    AssociatedGradedPiece I i →ₗ[R]
      AssociatedGradedPiece I j →ₗ[R] AssociatedGradedPiece I (i + j) :=
  (idealPowMulToQuotient I i j).liftQ₂
    (IdealPowSuccessor I i) (IdealPowSuccessor I j)
    (idealPowSuccessor_le_mul_ker_left I i j)
    (idealPowSuccessor_le_mul_ker_right I i j)

/-- Multiplication in the associated graded ring is induced by multiplication
of representatives in the corresponding ideal powers. -/
@[simp]
public lemma associatedGradedPieceMul_mk {R : Type*} [CommRing R]
    (I : Ideal R) (i j : ℕ) (a : (I ^ i : Submodule R R))
    (b : (I ^ j : Submodule R R)) :
    associatedGradedPieceMul I i j (Submodule.Quotient.mk a)
        (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk
        (⟨(a : R) * (b : R), by
          simpa only [pow_add] using Ideal.mul_mem_mul a.property b.property⟩ :
          (I ^ (i + j) : Submodule R R)) := by
  rfl

private def associatedGradedPieceOne {R : Type*} [CommRing R]
    (I : Ideal R) : AssociatedGradedPiece I 0 :=
  Submodule.Quotient.mk ⟨1, by simp⟩

private instance {R : Type*} [CommRing R] (I : Ideal R) :
    GradedMonoid.GOne (AssociatedGradedPiece I) where
  one := associatedGradedPieceOne I

private instance {R : Type*} [CommRing R] (I : Ideal R) :
    GradedMonoid.GMul (AssociatedGradedPiece I) where
  mul := fun a b => associatedGradedPieceMul I _ _ a b

private lemma associatedGradedPiece_mk_heq {R : Type*} [CommRing R]
    (I : Ideal R) {i j : ℕ} (hij : i = j) (a : IdealPow I i) (b : IdealPow I j)
    (hab : (a : R) = (b : R)) :
    HEq (Submodule.Quotient.mk a : AssociatedGradedPiece I i)
      (Submodule.Quotient.mk b : AssociatedGradedPiece I j) := by
  subst j
  have : a = b := Subtype.ext hab
  subst b
  rfl

@[instance_reducible] private def associatedGradedGCommRing
    {R : Type*} [CommRing R] (I : Ideal R) :
    DirectSum.GCommRing (AssociatedGradedPiece I) where
  one_mul := by
    rintro ⟨i, a⟩
    apply Sigma.ext (zero_add i)
    induction a using Submodule.Quotient.induction_on with
    | _ a =>
        change HEq
          (Submodule.Quotient.mk (idealPowMul I 0 i ⟨1, by simp [IdealPow]⟩ a))
          (Submodule.Quotient.mk a)
        apply associatedGradedPiece_mk_heq I (zero_add i)
        simp [idealPowMul]
  mul_one := by
    rintro ⟨i, a⟩
    apply Sigma.ext (add_zero i)
    induction a using Submodule.Quotient.induction_on with
    | _ a =>
        change HEq
          (Submodule.Quotient.mk (idealPowMul I i 0 a ⟨1, by simp [IdealPow]⟩))
          (Submodule.Quotient.mk a)
        apply associatedGradedPiece_mk_heq I (add_zero i)
        simp [idealPowMul]
  mul_assoc := by
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩
    apply Sigma.ext (add_assoc i j k)
    induction a using Submodule.Quotient.induction_on with
    | _ a =>
      induction b using Submodule.Quotient.induction_on with
      | _ b =>
        induction c using Submodule.Quotient.induction_on with
        | _ c =>
          change HEq
            (Submodule.Quotient.mk
              (idealPowMul I (i + j) k (idealPowMul I i j a b) c))
            (Submodule.Quotient.mk
              (idealPowMul I i (j + k) a (idealPowMul I j k b c)))
          apply associatedGradedPiece_mk_heq I (add_assoc i j k)
          simp [idealPowMul, mul_assoc]
  mul_zero := by
    intro i j a
    exact map_zero (associatedGradedPieceMul I i j a)
  zero_mul := by
    intro i j b
    exact DFunLike.congr_fun (map_zero (associatedGradedPieceMul I i j)) b
  mul_add := by
    intro i j a b c
    exact map_add (associatedGradedPieceMul I i j a) b c
  add_mul := by
    intro i j a b c
    exact DFunLike.congr_fun (map_add (associatedGradedPieceMul I i j) a b) c
  mul_comm := by
    rintro ⟨i, a⟩ ⟨j, b⟩
    apply Sigma.ext (add_comm i j)
    induction a using Submodule.Quotient.induction_on with
    | _ a =>
      induction b using Submodule.Quotient.induction_on with
      | _ b =>
        change HEq
          (Submodule.Quotient.mk (idealPowMul I i j a b))
          (Submodule.Quotient.mk (idealPowMul I j i b a))
        apply associatedGradedPiece_mk_heq I (add_comm i j)
        simp [idealPowMul, mul_comm]
  natCast := fun n => n • associatedGradedPieceOne I
  natCast_zero := zero_nsmul _
  natCast_succ := fun n => succ_nsmul (associatedGradedPieceOne I) n
  intCast := fun z => z • associatedGradedPieceOne I
  intCast_ofNat := fun n => natCast_zsmul (associatedGradedPieceOne I) n
  intCast_negSucc_ofNat := fun n => negSucc_zsmul (associatedGradedPieceOne I) n

private instance {R : Type*} [CommRing R] (I : Ideal R) :
    DirectSum.GCommRing (AssociatedGradedPiece I) :=
  associatedGradedGCommRing I

open scoped DirectSum

attribute [-instance] DirectSum.semiring DirectSum.commSemiring DirectSum.ring
  Ideal.Quotient.semiring Ideal.Quotient.commSemiring Ideal.Quotient.ring

public abbrev AssociatedGraded {R : Type*} [CommRing R] (I : Ideal R) :=
  ⨁ n : ℕ, AssociatedGradedPiece I n

@[instance_reducible] private def associatedGradedCommRing
    {R : Type*} [CommRing R] (I : Ideal R) : CommRing (AssociatedGraded I) :=
  DirectSum.commRing (AssociatedGradedPiece I)

private instance {R : Type*} [CommRing R] (I : Ideal R) :
    CommRing (AssociatedGraded I) := associatedGradedCommRing I

private abbrev AssociatedGradedBase {R : Type*} [CommRing R] (I : Ideal R) :=
  AssociatedGradedPiece I 0

private def associatedGradedBaseMk {R : Type*} [CommRing R] (I : Ideal R) :
    R →+* AssociatedGradedBase I where
  toFun r := Submodule.Quotient.mk ⟨r, by simp⟩
  map_one' := rfl
  map_mul' r s := by
    change associatedGradedPieceMul I 0 0
      (Submodule.Quotient.mk ⟨r, by simp⟩)
      (Submodule.Quotient.mk ⟨s, by simp⟩) =
        Submodule.Quotient.mk ⟨r * s, by simp⟩
    rw [associatedGradedPieceMul_mk]
  map_zero' := rfl
  map_add' _ _ := rfl

private lemma associatedGradedBaseMk_surjective {R : Type*} [CommRing R] (I : Ideal R) :
    Function.Surjective (associatedGradedBaseMk I) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => exact ⟨(x : R), rfl⟩

private lemma associatedGradedBaseMk_ker {R : Type*} [CommRing R] (I : Ideal R) :
    RingHom.ker (associatedGradedBaseMk I) = I := by
  ext r
  change (Submodule.Quotient.mk
      (⟨r, by simp [IdealPow]⟩ : IdealPow I 0) : AssociatedGradedBase I) = 0 ↔ r ∈ I
  rw [Submodule.Quotient.mk_eq_zero]
  simp

private noncomputable def associatedGradedBaseEquiv {R : Type*} [CommRing R]
    (I : Ideal R) : R ⧸ I ≃+* AssociatedGradedBase I :=
  (Ideal.quotEquivOfEq (associatedGradedBaseMk_ker I).symm).trans
    (RingHom.quotientKerEquivOfSurjective (associatedGradedBaseMk_surjective I))

private lemma associatedGradedPiece_isTorsionBySet {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) : Module.IsTorsionBySet R (AssociatedGradedPiece I n) I := by
  intro x r
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      change Submodule.Quotient.mk ((r : R) • x) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      change (r : R) * (x : R) ∈ I ^ (n + 1)
      have h : (r : R) * (x : R) ∈ I ^ (1 + n) := by
        rw [pow_add, pow_one]
        exact Ideal.mul_mem_mul r.property x.property
      simpa only [Nat.add_comm] using h

private def associatedGradedAlgebraMap {R : Type*} [CommRing R] (I : Ideal R) :
    R ⧸ I →+* AssociatedGraded I :=
  (DirectSum.ofZeroRingHom (AssociatedGradedPiece I)).comp
    (associatedGradedBaseEquiv I).toRingHom

@[instance_reducible] private def associatedGradedAlgebra
    {R : Type*} [CommRing R] (I : Ideal R) :
    Algebra (R ⧸ I) (AssociatedGraded I) :=
  (associatedGradedAlgebraMap I).toAlgebra

private instance {R : Type*} [CommRing R] (I : Ideal R) :
    Algebra (R ⧸ I) (AssociatedGraded I) :=
  associatedGradedAlgebra I

@[instance_reducible] private def associatedGradedModule
    {R : Type*} [CommRing R] (I : Ideal R) :
    Module (R ⧸ I) (AssociatedGraded I) :=
  @Algebra.toModule (R ⧸ I) (AssociatedGraded I)
    (Ideal.Quotient.commRing I).toCommSemiring
    (DirectSum.commRing (AssociatedGradedPiece I)).toSemiring
    (associatedGradedAlgebra I)

private instance {R : Type*} [CommRing R] (I : Ideal R) :
    Module (R ⧸ I) (AssociatedGraded I) :=
  associatedGradedModule I

private def associatedGradedComponent {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) : Submodule (R ⧸ I) (AssociatedGraded I) where
  carrier := Set.range (DirectSum.of (AssociatedGradedPiece I) n)
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ x y⟩
  smul_mem' := by
    rintro q _ ⟨x, rfl⟩
    induction q using Quotient.inductionOn' with
    | _ r =>
        refine ⟨associatedGradedBaseMk I r • x, ?_⟩
        change DirectSum.of (AssociatedGradedPiece I) n
            (associatedGradedBaseMk I r • x) =
          DirectSum.of (AssociatedGradedPiece I) 0 (associatedGradedBaseMk I r) *
            DirectSum.of (AssociatedGradedPiece I) n x
        exact DirectSum.of_zero_smul (AssociatedGradedPiece I)
          (associatedGradedBaseMk I r) x

private def associatedGradedPieceToComponent {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) :
    AssociatedGradedPiece I n →+ associatedGradedComponent I n where
  toFun x := ⟨DirectSum.of (AssociatedGradedPiece I) n x, ⟨x, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

private def associatedGradedDecompose {R : Type*} [CommRing R]
    (I : Ideal R) :
    AssociatedGraded I →+ ⨁ n : ℕ, associatedGradedComponent I n :=
  DirectSum.toAddMonoid fun n ↦
    (DirectSum.of (fun n ↦ associatedGradedComponent I n) n).comp
      (associatedGradedPieceToComponent I n)

private lemma associatedGraded_recompose_decompose {R : Type*} [CommRing R]
    (I : Ideal R) (x : AssociatedGraded I) :
    DirectSum.coeAddMonoidHom (associatedGradedComponent I)
        (associatedGradedDecompose I x) = x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n x => simp [associatedGradedDecompose, associatedGradedPieceToComponent]
  | add x y hx hy => simp [hx, hy]

private lemma associatedGraded_decompose_recompose {R : Type*} [CommRing R]
    (I : Ideal R) (x : ⨁ n : ℕ, associatedGradedComponent I n) :
    associatedGradedDecompose I
        (DirectSum.coeAddMonoidHom (associatedGradedComponent I) x) = x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n x =>
      obtain ⟨_, y, rfl⟩ := x
      simp [associatedGradedDecompose, associatedGradedPieceToComponent]
  | add x y hx hy => simp [hx, hy]

private lemma associatedGradedComponent_isInternal {R : Type*} [CommRing R]
    (I : Ideal R) : DirectSum.IsInternal (associatedGradedComponent I) := by
  constructor
  · intro x y hxy
    rw [← associatedGraded_decompose_recompose I x,
      ← associatedGraded_decompose_recompose I y, hxy]
  · intro x
    exact ⟨associatedGradedDecompose I x, associatedGraded_recompose_decompose I x⟩

@[instance_reducible] private noncomputable def associatedGradedComponent_decomposition
    {R : Type*} [CommRing R] (I : Ideal R) :
    DirectSum.Decomposition (associatedGradedComponent I) :=
  (associatedGradedComponent_isInternal I).chooseDecomposition

@[instance_reducible] private noncomputable def associatedGradedGradedRing
    {R : Type*} [CommRing R] (I : Ideal R) :
    GradedRing (associatedGradedComponent I) where
  one_mem := ⟨associatedGradedPieceOne I,
    DirectSum.of_zero_one (AssociatedGradedPiece I)⟩
  mul_mem := by
    rintro i j _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨associatedGradedPieceMul I i j x y,
      (DirectSum.of_mul_of x y).symm⟩
  toDecomposition := associatedGradedComponent_decomposition I

private instance {R : Type*} [CommRing R] (I : Ideal R) :
    GradedRing (associatedGradedComponent I) :=
  associatedGradedGradedRing I

private instance {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    Module (R ⧸ I) (AssociatedGradedPiece I n) :=
  (associatedGradedPiece_isTorsionBySet I n).module

private lemma associatedGraded_quotient_smul {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) (r : R) (x : AssociatedGradedPiece I n) :
    Ideal.Quotient.mk I r • x = associatedGradedBaseMk I r • x := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      let a : IdealPow I (0 + n) :=
        idealPowMul I 0 n ⟨r, by simp [IdealPow]⟩ x
      let b : IdealPow I n := r • x
      change Submodule.Quotient.mk b =
        @Eq.rec ℕ (0 + n) (fun i _ ↦ AssociatedGradedPiece I i)
          (Submodule.Quotient.mk a) n (zero_add n)
      symm
      apply eq_of_heq
      exact (@eqRec_heq ℕ (fun i ↦ AssociatedGradedPiece I i) (0 + n) n
        (zero_add n) (Submodule.Quotient.mk a)).trans
        (associatedGradedPiece_mk_heq I (zero_add n) a b rfl)

private def associatedGradedOfLinear {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) :
    AssociatedGradedPiece I n →ₗ[R ⧸ I] AssociatedGraded I where
  toFun := DirectSum.of (AssociatedGradedPiece I) n
  map_add' := map_add _
  map_smul' q x := by
    induction q using Quotient.inductionOn' with
    | _ r =>
        change DirectSum.of (AssociatedGradedPiece I) n
            (Ideal.Quotient.mk I r • x) =
          DirectSum.of (AssociatedGradedPiece I) 0 (associatedGradedBaseMk I r) *
            DirectSum.of (AssociatedGradedPiece I) n x
        rw [associatedGraded_quotient_smul]
        exact DirectSum.of_zero_smul (AssociatedGradedPiece I)
          (associatedGradedBaseMk I r) x

private noncomputable def associatedGradedComponentEquiv {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) :
    AssociatedGradedPiece I n ≃ₗ[R ⧸ I] associatedGradedComponent I n :=
  LinearEquiv.ofBijective
    ((associatedGradedOfLinear I n).codRestrict (associatedGradedComponent I n)
      (fun x ↦ ⟨x, rfl⟩)) ⟨by
        intro x y hxy
        exact DirectSum.of_injective n (congrArg Subtype.val hxy), by
        rintro ⟨z, x, rfl⟩
        exact ⟨x, rfl⟩⟩

private noncomputable def associatedGradedProjectionLinear
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    AssociatedGraded I →ₗ[R ⧸ I] AssociatedGradedPiece I n :=
  (associatedGradedComponentEquiv I n).symm.toLinearMap.comp
    ((DirectSum.component (R ⧸ I) ℕ (fun i ↦ associatedGradedComponent I i) n).comp
      (DirectSum.decomposeAlgEquiv (associatedGradedComponent I)).toLinearMap)

@[simp]
private theorem associatedGradedProjectionLinear_of
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)
    (x : AssociatedGradedPiece I n) :
    associatedGradedProjectionLinear I n
        (DirectSum.of (AssociatedGradedPiece I) n x) = x := by
  let y : associatedGradedComponent I n :=
    ⟨DirectSum.of (AssociatedGradedPiece I) n x, ⟨x, rfl⟩⟩
  change (associatedGradedComponentEquiv I n).symm
      ((DirectSum.decompose (associatedGradedComponent I) (y : AssociatedGraded I)) n) = x
  rw [DirectSum.decompose_coe, DirectSum.of_eq_same]
  exact (associatedGradedComponentEquiv I n).symm_apply_apply x

private theorem associatedGradedBaseIsArtinian
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I.IsIdealOfDefinition) : IsArtinianRing (R ⧸ I) := by
  let m : Ideal R := IsLocalRing.maximalIdeal R
  let _ : m.IsPrime := by
    dsimp [m]
    infer_instance
  have hm : m ∈ I.minimalPrimes := by
    change IsLocalRing.maximalIdeal R ∈ I.minimalPrimes
    rw [← I.radical_minimalPrimes, hI,
      Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  exact IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hm

private theorem associatedGradedPieceFinite
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) (n : ℕ) :
    Module.Finite (R ⧸ I) (AssociatedGradedPiece I n) := by
  let _ : Module.Finite R (IdealPow I n) :=
    Module.Finite.of_fg (IsNoetherian.noetherian (IdealPow I n))
  let _ : Module.Finite R (AssociatedGradedPiece I n) := inferInstance
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ I)
    (AssociatedGradedPiece I n)

private theorem associatedGradedComponentFinite
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) (n : ℕ) :
    Module.Finite (R ⧸ I) (associatedGradedComponent I n) := by
  let _ : Module.Finite (R ⧸ I) (AssociatedGradedPiece I n) :=
    associatedGradedPieceFinite I n
  exact Module.Finite.equiv (associatedGradedComponentEquiv I n)

private lemma associatedGradedComponent_length_eq
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) (n : ℕ) :
    Module.length (R ⧸ I) (associatedGradedComponent I n) =
      Module.length R (AssociatedGradedPiece I n) := by
  let _ : Module.Finite (R ⧸ I) (AssociatedGradedPiece I n) :=
    associatedGradedPieceFinite I n
  calc
    Module.length (R ⧸ I) (associatedGradedComponent I n) =
        Module.length (R ⧸ I) (AssociatedGradedPiece I n) :=
      (associatedGradedComponentEquiv I n).length_eq.symm
    _ = Module.length R (AssociatedGradedPiece I n) :=
      (Module.length_eq_of_surjective
        (R := R ⧸ I) (S := R) (M := AssociatedGradedPiece I n)
        Ideal.Quotient.mk_surjective).symm

private def associatedGradedDegreeOne {R : Type*} [CommRing R] (I : Ideal R) :
    I → AssociatedGradedPiece I 1 := fun x ↦
  Submodule.Quotient.mk ⟨x, by
    rw [pow_one]
    exact x.property⟩

private lemma associatedGraded_of_zero_eq_algebraMap
    {R : Type*} [CommRing R] (I : Ideal R) (x : IdealPow I 0) :
    DirectSum.of (AssociatedGradedPiece I) 0 (Submodule.Quotient.mk x) =
      associatedGradedAlgebraMap I (Ideal.Quotient.mk I x.1) := by
  rfl

private lemma associatedGraded_of_mem_adjoin
    {R : Type*} [CommRing R] (I : Ideal R) (S : Set (AssociatedGraded I))
    (hdegreeOne : ∀ x : AssociatedGradedPiece I 1,
      DirectSum.of (AssociatedGradedPiece I) 1 x ∈ Algebra.adjoin (R ⧸ I) S) :
    ∀ (n : ℕ) (x : IdealPow I n),
      DirectSum.of (AssociatedGradedPiece I) n (Submodule.Quotient.mk x) ∈
        Algebra.adjoin (R ⧸ I) S := by
  intro n
  induction n with
  | zero =>
      intro x
      rw [associatedGraded_of_zero_eq_algebraMap]
      exact Subalgebra.algebraMap_mem _ _
  | succ n ih =>
      intro x
      have hx : (x : R) ∈ I ^ (n + 1) := x.property
      rw [pow_succ'] at hx
      let p : R → Prop := fun y ↦
        ∃ hy : y ∈ I ^ (n + 1),
          DirectSum.of (AssociatedGradedPiece I) (n + 1)
              (Submodule.Quotient.mk
                (⟨y, hy⟩ : IdealPow I (n + 1))) ∈
            Algebra.adjoin (R ⧸ I) S
      have hp : p (x : R) := Submodule.smul_induction_on hx (p := p) (by
        intro r hr y hy
        have hry : r * y ∈ I ^ (n + 1) := by
          rw [pow_succ']
          exact Submodule.smul_mem_smul hr hy
        refine ⟨hry, ?_⟩
        have hmul := (Algebra.adjoin (R ⧸ I) S).mul_mem
          (ih ⟨y, hy⟩) (hdegreeOne (associatedGradedDegreeOne I ⟨r, hr⟩))
        change DirectSum.of (AssociatedGradedPiece I) n
            (Submodule.Quotient.mk ⟨y, hy⟩) *
              DirectSum.of (AssociatedGradedPiece I) 1
                (associatedGradedDegreeOne I ⟨r, hr⟩) ∈
          Algebra.adjoin (R ⧸ I) S at hmul
        rw [DirectSum.of_mul_of] at hmul
        change DirectSum.of (AssociatedGradedPiece I) (n + 1)
            (associatedGradedPieceMul I n 1
              (Submodule.Quotient.mk ⟨y, hy⟩)
              (associatedGradedDegreeOne I ⟨r, hr⟩)) ∈
          Algebra.adjoin (R ⧸ I) S at hmul
        simpa [associatedGradedDegreeOne, associatedGradedPieceMul_mk,
          idealPowMul, smul_eq_mul, mul_comm] using hmul) (by
        intro y z hy hz
        obtain ⟨hy', hy⟩ := hy
        obtain ⟨hz', hz⟩ := hz
        refine ⟨(I ^ (n + 1)).add_mem hy' hz', ?_⟩
        have hadd := (Algebra.adjoin (R ⧸ I) S).add_mem hy hz
        convert hadd using 1
        rw [← map_add]
        apply congrArg (DirectSum.of (AssociatedGradedPiece I) (n + 1))
        have heq :
            (⟨y + z, (I ^ (n + 1)).add_mem hy' hz'⟩ : IdealPow I (n + 1)) =
              ⟨y, hy'⟩ + ⟨z, hz'⟩ := Subtype.ext rfl
        rw [heq]
        exact map_add (IdealPowSuccessor I (n + 1)).mkQ _ _)
      obtain ⟨hx', hp⟩ := hp
      convert hp using 1

private lemma associatedGraded_of_smul
    {R : Type*} [CommRing R] (I : Ideal R) (q : R ⧸ I)
    (x : AssociatedGradedPiece I 1) :
    DirectSum.of (AssociatedGradedPiece I) 1 (q • x) =
      associatedGradedAlgebraMap I q *
        DirectSum.of (AssociatedGradedPiece I) 1 x := by
  induction q using Quotient.inductionOn' with
  | _ r =>
      change DirectSum.of (AssociatedGradedPiece I) 1
          (Ideal.Quotient.mk I r • x) =
        DirectSum.of (AssociatedGradedPiece I) 0
            (associatedGradedBaseMk I r) *
          DirectSum.of (AssociatedGradedPiece I) 1 x
      rw [associatedGraded_quotient_smul]
      exact DirectSum.of_zero_smul (AssociatedGradedPiece I)
        (associatedGradedBaseMk I r) x

private lemma associatedGraded_standardGenerated
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    ∃ s : Finset (AssociatedGraded I),
      Algebra.adjoin (R ⧸ I) (s : Set (AssociatedGraded I)) = ⊤ ∧
        ∀ a ∈ s, a ∈ associatedGradedComponent I 1 := by
  classical
  let _ : Module.Finite (R ⧸ I) (AssociatedGradedPiece I 1) :=
    associatedGradedPieceFinite I 1
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top :
    (⊤ : Submodule (R ⧸ I) (AssociatedGradedPiece I 1)).FG)
  let f : AssociatedGradedPiece I 1 → AssociatedGraded I :=
    DirectSum.of (AssociatedGradedPiece I) 1
  let s : Finset (AssociatedGraded I) := t.image f
  have hdegreeOne : ∀ x : AssociatedGradedPiece I 1,
      f x ∈ Algebra.adjoin (R ⧸ I) (s : Set (AssociatedGraded I)) := by
    intro x
    have hx : x ∈ Submodule.span (R ⧸ I) (t : Set (AssociatedGradedPiece I 1)) := by
      rw [ht]
      trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
        exact Algebra.subset_adjoin (by
          exact Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    | zero =>
        change DirectSum.of (AssociatedGradedPiece I) 1 0 ∈
          Algebra.adjoin (R ⧸ I) (s : Set (AssociatedGraded I))
        rw [map_zero]
        exact (Algebra.adjoin (R ⧸ I) (s : Set (AssociatedGraded I))).zero_mem
    | add x y _ _ hx hy =>
        simpa [f] using
          (Algebra.adjoin (R ⧸ I) (s : Set (AssociatedGraded I))).add_mem hx hy
    | smul q x _ hx =>
        change DirectSum.of (AssociatedGradedPiece I) 1 (q • x) ∈
          Algebra.adjoin (R ⧸ I) (s : Set (AssociatedGraded I))
        rw [associatedGraded_of_smul]
        exact (Algebra.adjoin (R ⧸ I) (s : Set (AssociatedGraded I))).mul_mem
          (Subalgebra.algebraMap_mem _ _) hx
  refine ⟨s, ?_, ?_⟩
  · apply top_unique
    intro z _
    induction z using DirectSum.induction_on with
    | zero => exact Subalgebra.zero_mem _
    | of n x =>
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
            exact associatedGraded_of_mem_adjoin I (s : Set (AssociatedGraded I))
              (by simpa [f] using hdegreeOne) n x
    | add x y hx hy => exact Subalgebra.add_mem _ (hx trivial) (hy trivial)
  · intro a ha
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨x, rfl⟩

private lemma associatedGraded_standardGenerated_of_span
    {R : Type*} [CommRing R] (I : Ideal R) (s : Finset R)
    (hs : Ideal.span (s : Set R) = I) :
    ∃ t : Finset (AssociatedGraded I),
      t.card ≤ s.card ∧
        Algebra.adjoin (R ⧸ I) (t : Set (AssociatedGraded I)) = ⊤ ∧
        ∀ a ∈ t, a ∈ associatedGradedComponent I 1 := by
  classical
  have hs_mem (a : s) : (a : R) ∈ I := by
    rw [← hs]
    exact Ideal.subset_span a.property
  let f : s → AssociatedGraded I := fun a =>
    DirectSum.of (AssociatedGradedPiece I) 1
      (associatedGradedDegreeOne I ⟨a, hs_mem a⟩)
  let t : Finset (AssociatedGraded I) := Finset.univ.image f
  have hdegreeOne : ∀ x : AssociatedGradedPiece I 1,
      DirectSum.of (AssociatedGradedPiece I) 1 x ∈
        Algebra.adjoin (R ⧸ I) (t : Set (AssociatedGraded I)) := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      have hxI : (x : R) ∈ I := by
        simpa [IdealPow] using x.property
      have hx : (x : R) ∈ Ideal.span (s : Set R) := by
        rw [hs]
        exact hxI
      have hp : DirectSum.of (AssociatedGradedPiece I) 1
            (associatedGradedDegreeOne I ⟨x, hxI⟩) ∈
          Algebra.adjoin (R ⧸ I) (t : Set (AssociatedGraded I)) := by
        refine Submodule.span_induction (s := (s : Set R))
          (p := fun y hy =>
            DirectSum.of (AssociatedGradedPiece I) 1
                (associatedGradedDegreeOne I
                  ⟨y, by rw [← hs]; exact hy⟩) ∈
              Algebra.adjoin (R ⧸ I) (t : Set (AssociatedGraded I)))
          ?_ ?_ ?_ ?_ hx
        · intro y hy
          apply Algebra.subset_adjoin
          let a : s := ⟨y, hy⟩
          refine Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ?_⟩
          simp only [f]
          congr 3
        ·
          change DirectSum.of (AssociatedGradedPiece I) 1
              (0 : AssociatedGradedPiece I 1) ∈
            Algebra.adjoin (R ⧸ I) (t : Set (AssociatedGraded I))
          rw [map_zero]
          exact Subalgebra.zero_mem _
        · intro y z hy hz ihy ihz
          change DirectSum.of (AssociatedGradedPiece I) 1
              (associatedGradedDegreeOne I
                  ⟨y, by rw [← hs]; exact hy⟩ +
                associatedGradedDegreeOne I
                  ⟨z, by rw [← hs]; exact hz⟩) ∈
            Algebra.adjoin (R ⧸ I) (t : Set (AssociatedGraded I))
          rw [map_add]
          exact (Algebra.adjoin (R ⧸ I) (t : Set (AssociatedGraded I))).add_mem ihy ihz
        · intro r y hy ihy
          change DirectSum.of (AssociatedGradedPiece I) 1
              (Ideal.Quotient.mk I r • associatedGradedDegreeOne I
                ⟨y, by rw [← hs]; exact hy⟩) ∈
            Algebra.adjoin (R ⧸ I) (t : Set (AssociatedGraded I))
          rw [associatedGraded_of_smul]
          exact (Algebra.adjoin (R ⧸ I) (t : Set (AssociatedGraded I))).mul_mem
            (Subalgebra.algebraMap_mem _ (Ideal.Quotient.mk I r)) ihy
      change DirectSum.of (AssociatedGradedPiece I) 1
          (associatedGradedDegreeOne I ⟨x, hxI⟩) ∈
        Algebra.adjoin (R ⧸ I) (t : Set (AssociatedGraded I))
      exact hp
  refine ⟨t, ?_, ?_, ?_⟩
  · calc
      t.card ≤ Fintype.card s := Finset.card_image_le
      _ = s.card := Fintype.card_coe _
  · apply top_unique
    intro z _
    induction z using DirectSum.induction_on with
    | zero => exact Subalgebra.zero_mem _
    | of n x =>
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
            exact associatedGraded_of_mem_adjoin I (t : Set (AssociatedGraded I))
              hdegreeOne n x
    | add x y hx hy => exact Subalgebra.add_mem _ (hx trivial) (hy trivial)
  · intro a ha
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨associatedGradedDegreeOne I ⟨x, hs_mem x⟩, rfl⟩

private theorem associatedGraded_eventuallyRepresents
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.IsIdealOfDefinition) :
    ∃ hseries : GradedHilbert.HilbertSeriesCertificate
        (associatedGradedComponent I),
      NumericalPolynomial.EventuallyRepresents
        (hseries.numerator.hilbertPoly hseries.denominator)
        (fun n => (Module.length R (AssociatedGradedPiece I n)).toNat : ℕ → ℤ) := by
  let _ : IsArtinianRing (R ⧸ I) := associatedGradedBaseIsArtinian I hI
  let _ (n : ℕ) : Module.Finite (R ⧸ I) (associatedGradedComponent I n) :=
    associatedGradedComponentFinite I n
  have hfinite (n : ℕ) : IsFiniteLength (R ⧸ I) (associatedGradedComponent I n) := by
    apply ((IsArtinianRing.tfae (R ⧸ I) (associatedGradedComponent I n)).out 0 3).mp
    exact associatedGradedComponentFinite I n
  let hdegreeOne := associatedGraded_standardGenerated I
  let hseries := GradedHilbert.HilbertSeriesCertificate.ofStandardGenerators
    (associatedGradedComponent I) (associatedGradedComponent I)
    hdegreeOne hfinite
  refine ⟨hseries, ?_⟩
  have hrep := GradedHilbert.gradedHilbertSerre
    (associatedGradedComponent I) (associatedGradedComponent I)
    (associatedGradedComponent_decomposition I) hdegreeOne hfinite hseries
  rw [NumericalPolynomial.EventuallyRepresents] at hrep ⊢
  filter_upwards [hrep] with n hn
  rw [← associatedGradedComponent_length_eq I n]
  exact hn

private theorem associatedGraded_eventuallyRepresents_of_span
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (s : Finset R)
    (hs : Ideal.span (s : Set R) = I) :
    ∃ hseries : GradedHilbert.HilbertSeriesCertificate
        (associatedGradedComponent I),
      hseries.denominator ≤ s.card ∧
        NumericalPolynomial.EventuallyRepresents
          (hseries.numerator.hilbertPoly hseries.denominator)
          (fun n => (Module.length R (AssociatedGradedPiece I n)).toNat : ℕ → ℤ) := by
  let _ : IsArtinianRing (R ⧸ I) := associatedGradedBaseIsArtinian I hI
  let _ (n : ℕ) : Module.Finite (R ⧸ I) (associatedGradedComponent I n) :=
    associatedGradedComponentFinite I n
  have hfinite (n : ℕ) : IsFiniteLength (R ⧸ I) (associatedGradedComponent I n) := by
    apply ((IsArtinianRing.tfae (R ⧸ I) (associatedGradedComponent I n)).out 0 3).mp
    exact associatedGradedComponentFinite I n
  obtain ⟨t, htcard, htgen, htdegree⟩ :=
    associatedGraded_standardGenerated_of_span I s hs
  let hseries := GradedHilbert.HilbertSeriesCertificate.ofGenerators
    (associatedGradedComponent I) (associatedGradedComponent I) t htgen htdegree hfinite
  refine ⟨hseries, ?_, ?_⟩
  · change (GradedHilbert.HilbertSeriesCertificate.ofGenerators
        (associatedGradedComponent I) (associatedGradedComponent I)
        t htgen htdegree hfinite).denominator ≤ s.card
    rw [GradedHilbert.HilbertSeriesCertificate.denominator_ofGenerators]
    exact htcard
  · have hrep := GradedHilbert.gradedHilbertSerre
      (associatedGradedComponent I) (associatedGradedComponent I)
      (associatedGradedComponent_decomposition I)
      ⟨t, htgen, htdegree⟩ hfinite hseries
    rw [NumericalPolynomial.EventuallyRepresents] at hrep ⊢
    filter_upwards [hrep] with n hn
    rw [← associatedGradedComponent_length_eq I n]
    exact hn

private def idealCumulativeFunction {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) : ℤ :=
  (Module.length R (R ⧸ I ^ (n + 1))).toNat

private def successiveQuotientInclusion {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) :
    AssociatedGradedPiece I n →ₗ[R] R ⧸ (I ^ (n + 1) : Submodule R R) :=
  Submodule.mapQ _ _ ((I ^ n : Ideal R) : Submodule R R).subtype le_rfl

private lemma successiveQuotientInclusion_injective {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) : Function.Injective (successiveQuotientInclusion I n) := by
  rw [← LinearMap.ker_eq_bot]
  simp [successiveQuotientInclusion, Submodule.ker_mapQ]

private lemma successiveQuotient_exact {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) :
    Function.Exact (successiveQuotientInclusion I n)
      (Submodule.factor (Ideal.pow_le_pow_right n.le_succ)) := by
  rw [LinearMap.exact_iff]
  simp [successiveQuotientInclusion, Submodule.range_mapQ, Submodule.ker_mapQ]

private lemma length_quotient_pow_succ_eq_add {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) :
    Module.length R (R ⧸ I ^ (n + 1)) =
      Module.length R (AssociatedGradedPiece I n) + Module.length R (R ⧸ I ^ n) := by
  simpa [add_comm] using Module.length_eq_add_of_exact
    (successiveQuotientInclusion I n)
    (Submodule.factor (Ideal.pow_le_pow_right n.le_succ))
    (successiveQuotientInclusion_injective I n)
    (Submodule.factor_surjective (Ideal.pow_le_pow_right n.le_succ))
    (successiveQuotient_exact I n)

private lemma maximalIdeal_mem_minimalPrimes_pow_succ
    {R : Type*} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (n : ℕ) :
    IsLocalRing.maximalIdeal R ∈ (I ^ (n + 1)).minimalPrimes := by
  let m : Ideal R := IsLocalRing.maximalIdeal R
  let _ : m.IsPrime := by
    dsimp [m]
    infer_instance
  change m ∈ (I ^ (n + 1)).minimalPrimes
  rw [← (I ^ (n + 1)).radical_minimalPrimes,
    I.radical_pow (Nat.succ_ne_zero n), hI,
    Ideal.minimalPrimes_eq_subsingleton_self]
  exact Set.mem_singleton m

private lemma length_quotient_pow_succ_ne_top
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (n : ℕ) :
    Module.length R (R ⧸ I ^ (n + 1)) ≠ ⊤ := by
  let Q := R ⧸ I ^ (n + 1)
  let _ : IsArtinianRing Q :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _
      (maximalIdeal_mem_minimalPrimes_pow_succ I hI n)
  rw [Module.length_eq_of_surjective (S := R) (R := Q) (M := Q)
    Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

private lemma idealCumulativeFunction_succ_sub
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (n : ℕ) :
    idealCumulativeFunction I (n + 1) - idealCumulativeFunction I n =
      (Module.length R (AssociatedGradedPiece I (n + 1))).toNat := by
  have hlength := length_quotient_pow_succ_eq_add I (n + 1)
  have htotal := length_quotient_pow_succ_ne_top I hI (n + 1)
  have hprevious := length_quotient_pow_succ_ne_top I hI n
  have hgraded :
      Module.length R (AssociatedGradedPiece I (n + 1)) ≠ ⊤ := by
    intro htop
    apply htotal
    rw [hlength, htop, top_add]
  have hnat := congrArg ENat.toNat hlength
  rw [ENat.toNat_add hgraded hprevious] at hnat
  dsimp [idealCumulativeFunction]
  omega

private lemma coeff_hilbertSeries_succ_sub
    (p : Polynomial ℚ) (d n : ℕ) :
    PowerSeries.coeff (n + 1)
          ((p : PowerSeries ℚ) * (PowerSeries.invOneSubPow ℚ (d + 1)).val) -
        PowerSeries.coeff n
          ((p : PowerSeries ℚ) * (PowerSeries.invOneSubPow ℚ (d + 1)).val) =
      PowerSeries.coeff (n + 1)
        ((p : PowerSeries ℚ) * (PowerSeries.invOneSubPow ℚ d).val) := by
  let A : PowerSeries ℚ :=
    (p : PowerSeries ℚ) * (PowerSeries.invOneSubPow ℚ (d + 1)).val
  have hseries : (1 - PowerSeries.X) * A =
      (p : PowerSeries ℚ) * (PowerSeries.invOneSubPow ℚ d).val := by
    dsimp [A]
    calc
      (1 - PowerSeries.X) *
          ((p : PowerSeries ℚ) * (PowerSeries.invOneSubPow ℚ (d + 1)).val) =
          (p : PowerSeries ℚ) *
            ((1 - PowerSeries.X) ^ 1 *
              (PowerSeries.invOneSubPow ℚ (d + 1)).val) := by ring
      _ = (p : PowerSeries ℚ) * (PowerSeries.invOneSubPow ℚ d).val := by
        rw [PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℚ d 1]
  rw [← hseries]
  simp [A, sub_mul, map_sub, PowerSeries.coeff_succ_X_mul]

private lemma eventuallyRepresents_hilbertPoly_antidifference
    (p : Polynomial ℚ) (d : ℕ) {f : ℕ → ℤ}
    (hrep : NumericalPolynomial.EventuallyRepresents (p.hilbertPoly d) f) :
    NumericalPolynomial.EventuallyRepresents
      (NumericalPolynomial.forwardDifference (p.hilbertPoly (d + 1)))
      (fun n => f (n + 1)) := by
  rw [NumericalPolynomial.EventuallyRepresents, eventually_atTop] at hrep ⊢
  obtain ⟨N, hN⟩ := hrep
  refine ⟨max N (p.natDegree + 1), fun n hn => ?_⟩
  have hNn : N ≤ n := le_trans (le_max_left _ _) hn
  have hlarge : p.natDegree < n :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_right _ _) hn)
  have hlarge' : p.natDegree < n + 1 := hlarge.trans_le n.le_succ
  rw [NumericalPolynomial.eval_forwardDifference,
    show (n : ℚ) + 1 = ((n + 1 : ℕ) : ℚ) by norm_num,
    ← Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval (d + 1) hlarge',
    ← Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval (d + 1) hlarge,
    coeff_hilbertSeries_succ_sub p d n,
    Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval d hlarge',
    hN (n + 1) (hNn.trans n.le_succ)]

private lemma exists_eventuallyRepresents_of_forwardDifference
    {f g : ℕ → ℤ} (P : Polynomial ℚ)
    (hrec : ∀ n, f (n + 1) - f n = g (n + 1))
    (hrep : NumericalPolynomial.EventuallyRepresents
      (NumericalPolynomial.forwardDifference P) (fun n => g (n + 1))) :
    ∃ c : ℚ, NumericalPolynomial.EventuallyRepresents (P + Polynomial.C c) f := by
  rw [NumericalPolynomial.EventuallyRepresents, eventually_atTop] at hrep
  obtain ⟨N, hN⟩ := hrep
  let c : ℚ := (f N : ℚ) - P.eval (N : ℚ)
  refine ⟨c, ?_⟩
  rw [NumericalPolynomial.EventuallyRepresents, eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  induction n, hn using Nat.le_induction with
  | base => simp [c]
  | succ n hn ih =>
      rw [Polynomial.eval_add, Polynomial.eval_C]
      rw [Polynomial.eval_add, Polynomial.eval_C] at ih
      have hdiff := hN n hn
      rw [NumericalPolynomial.eval_forwardDifference,
        show (n : ℚ) + 1 = ((n + 1 : ℕ) : ℚ) by norm_num] at hdiff
      have hrec' : (f (n + 1) : ℚ) - f n = g (n + 1) := by
        exact_mod_cast hrec n
      linarith

private lemma natDegree_hilbertPoly_le (p : Polynomial ℚ) (d : ℕ) :
    (p.hilbertPoly d).natDegree ≤ d - 1 := by
  cases d with
  | zero => simp [Polynomial.hilbertPoly_zero_right]
  | succ d =>
      rw [Polynomial.hilbertPoly_succ]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi
      exact (Polynomial.natDegree_smul_le _ _).trans_eq
        (Polynomial.natDegree_preHilbertPoly ℚ d i)

theorem idealCumulativePolynomial_exists
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.IsIdealOfDefinition) :
    ∃ P : Polynomial ℚ,
      NumericalPolynomial.EventuallyRepresents P (idealCumulativeFunction I) := by
  obtain ⟨hseries, hgraded⟩ := associatedGraded_eventuallyRepresents I hI
  let P := hseries.numerator.hilbertPoly (hseries.denominator + 1)
  have hdiff : NumericalPolynomial.EventuallyRepresents
      (NumericalPolynomial.forwardDifference P)
      (fun n =>
        (Module.length R (AssociatedGradedPiece I (n + 1))).toNat : ℕ → ℤ) := by
    exact eventuallyRepresents_hilbertPoly_antidifference
      hseries.numerator hseries.denominator hgraded
  obtain ⟨c, hc⟩ := exists_eventuallyRepresents_of_forwardDifference P
    (f := idealCumulativeFunction I)
    (g := fun n => (Module.length R (AssociatedGradedPiece I n)).toNat)
    (idealCumulativeFunction_succ_sub I hI) hdiff
  exact ⟨P + Polynomial.C c, hc⟩

private theorem idealCumulativePolynomial_exists_of_span
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (s : Finset R)
    (hs : Ideal.span (s : Set R) = I) :
    ∃ P : Polynomial ℚ,
      NumericalPolynomial.EventuallyRepresents P (idealCumulativeFunction I) ∧
        P.natDegree ≤ s.card := by
  obtain ⟨hseries, hden, hgraded⟩ :=
    associatedGraded_eventuallyRepresents_of_span I hI s hs
  let P := hseries.numerator.hilbertPoly (hseries.denominator + 1)
  have hdiff : NumericalPolynomial.EventuallyRepresents
      (NumericalPolynomial.forwardDifference P)
      (fun n =>
        (Module.length R (AssociatedGradedPiece I (n + 1))).toNat : ℕ → ℤ) := by
    exact eventuallyRepresents_hilbertPoly_antidifference
      hseries.numerator hseries.denominator hgraded
  obtain ⟨c, hc⟩ := exists_eventuallyRepresents_of_forwardDifference P
    (f := idealCumulativeFunction I)
    (g := fun n => (Module.length R (AssociatedGradedPiece I n)).toNat)
    (idealCumulativeFunction_succ_sub I hI) hdiff
  refine ⟨P + Polynomial.C c, hc, ?_⟩
  apply le_trans (Polynomial.natDegree_add_le _ _)
  apply le_trans (max_le ?_ ?_) hden
  · simpa [P] using natDegree_hilbertPoly_le hseries.numerator
      (hseries.denominator + 1)
  · simp

private lemma idealCumulative_eventuallyRepresents_taylor_neg_one
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (P : Polynomial ℚ)
    (hP : NumericalPolynomial.EventuallyRepresents P (idealCumulativeFunction I)) :
    IsPolynomial I R (P.taylor (-1)) := by
  rw [NumericalPolynomial.EventuallyRepresents, eventually_atTop] at hP
  rw [IsPolynomial, NumericalPolynomial.EventuallyRepresents, eventually_atTop]
  obtain ⟨N, hN⟩ := hP
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (Nat.le_add_left 1 N) hn
  have hNn : N ≤ n - 1 := by omega
  calc
    (P.taylor (-1)).eval (n : ℚ) = P.eval ((n - 1 : ℕ) : ℚ) := by
      rw [Polynomial.taylor_eval, Nat.cast_sub hn1]
      push_cast
      ring_nf
    _ = (idealCumulativeFunction I (n - 1) : ℚ) := hN (n - 1) hNn
    _ = (hilbertFunction I R n : ℚ) := by
      have htop : (I ^ n • (⊤ : Submodule R R)) = (I ^ n : Submodule R R) := by
        ext x
        simp
      rw [idealCumulativeFunction, hilbertFunction, Nat.sub_add_cancel hn1, htop]

public theorem idealPolynomial_exists
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.IsIdealOfDefinition) :
    ∃ P : Polynomial ℚ, IsPolynomial I R P := by
  obtain ⟨P, hP⟩ := idealCumulativePolynomial_exists I hI
  exact ⟨P.taylor (-1),
    idealCumulative_eventuallyRepresents_taylor_neg_one I P hP⟩

public theorem idealPolynomial_exists_of_span
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (s : Finset R)
    (hs : Ideal.span (s : Set R) = I) :
    ∃ P : Polynomial ℚ, IsPolynomial I R P ∧ P.natDegree ≤ s.card := by
  obtain ⟨P, hP, hdegree⟩ := idealCumulativePolynomial_exists_of_span I hI s hs
  refine ⟨P.taylor (-1),
    idealCumulative_eventuallyRepresents_taylor_neg_one I P hP, ?_⟩
  · rw [Polynomial.natDegree_taylor]
    exact hdegree

/-! ## Public associated-graded API

The Hilbert--Samuel construction above keeps its quotient and direct-sum
bookkeeping private.  The following small interface exposes the resulting
graded algebra, its homogeneous inclusions, and the facts needed to use a
degree-one presentation without making that bookkeeping part of the API.
-/

@[instance_reducible] public noncomputable def associatedGradedGCommRingPublic
    {R : Type*} [CommRing R] (I : Ideal R) :
    DirectSum.GCommRing (AssociatedGradedPiece I) :=
  associatedGradedGCommRing I

public noncomputable instance {R : Type*} [CommRing R] (I : Ideal R) :
    DirectSum.GCommRing (AssociatedGradedPiece I) :=
  associatedGradedGCommRingPublic I

@[expose, instance_reducible] public noncomputable def associatedGradedCommRingPublic
    {R : Type*} [CommRing R] (I : Ideal R) : CommRing (AssociatedGraded I) :=
  DirectSum.commRing (AssociatedGradedPiece I)

public noncomputable instance {R : Type*} [CommRing R] (I : Ideal R) :
    CommRing (AssociatedGraded I) :=
  associatedGradedCommRingPublic I

public noncomputable def associatedGradedAlgebraMapPublic
    {R : Type*} [CommRing R] (I : Ideal R) :
    R ⧸ I →+* AssociatedGraded I :=
  associatedGradedAlgebraMap I

@[expose, instance_reducible] public noncomputable def associatedGradedAlgebraPublic
    {R : Type*} [CommRing R] (I : Ideal R) :
    Algebra (R ⧸ I) (AssociatedGraded I) :=
  (associatedGradedAlgebraMapPublic I).toAlgebra

public noncomputable instance {R : Type*} [CommRing R] (I : Ideal R) :
    Algebra (R ⧸ I) (AssociatedGraded I) :=
  associatedGradedAlgebraPublic I

@[expose, instance_reducible] public noncomputable def associatedGradedModulePublic
    {R : Type*} [CommRing R] (I : Ideal R) :
    Module (R ⧸ I) (AssociatedGraded I) :=
  @Algebra.toModule (R ⧸ I) (AssociatedGraded I)
    (Ideal.Quotient.commRing I).toCommSemiring
    (associatedGradedCommRingPublic I).toSemiring
    (associatedGradedAlgebraPublic I)

public noncomputable instance {R : Type*} [CommRing R] (I : Ideal R) :
    Module (R ⧸ I) (AssociatedGraded I) :=
  associatedGradedModulePublic I

@[expose, instance_reducible] public noncomputable def associatedGradedPieceModule
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    Module (R ⧸ I) (AssociatedGradedPiece I n) :=
  (show Module.IsTorsionBySet R (AssociatedGradedPiece I n) I from by
    intro x r
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
        change Submodule.Quotient.mk ((r : R) • x) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        change (r : R) * (x : R) ∈ I ^ (n + 1)
        have h : (r : R) * (x : R) ∈ I ^ (1 + n) := by
          rw [pow_add, pow_one]
          exact Ideal.mul_mem_mul r.property x.property
        simpa only [Nat.add_comm] using h).module

public noncomputable instance {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    Module (R ⧸ I) (AssociatedGradedPiece I n) :=
  associatedGradedPieceModule I n

/-- The inclusion of one homogeneous piece into the associated graded ring. -/
public noncomputable def associatedGradedOf
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    AssociatedGradedPiece I n →ₗ[R ⧸ I] AssociatedGraded I :=
  associatedGradedOfLinear I n

/-- Projection to one homogeneous component. -/
public noncomputable def associatedGradedProjection
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    AssociatedGraded I →ₗ[R ⧸ I] AssociatedGradedPiece I n := by
  letI : Algebra (R ⧸ I) (AssociatedGraded I) := associatedGradedAlgebra I
  letI : Module (R ⧸ I) (AssociatedGraded I) := associatedGradedModule I
  letI : Module (R ⧸ I) (AssociatedGradedPiece I n) :=
    (associatedGradedPiece_isTorsionBySet I n).module
  exact associatedGradedProjectionLinear I n

@[simp]
public theorem associatedGradedOf_apply
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)
    (x : AssociatedGradedPiece I n) :
    associatedGradedOf I n x = DirectSum.of (AssociatedGradedPiece I) n x := by
  rfl

public theorem associatedGradedOf_injective
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    Function.Injective (associatedGradedOf I n) := by
  intro x y hxy
  exact DirectSum.of_injective n hxy

@[simp]
public theorem associatedGradedProjection_of
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)
    (x : AssociatedGradedPiece I n) :
    associatedGradedProjection I n (associatedGradedOf I n x) = x := by
  exact associatedGradedProjectionLinear_of I n x

@[simp]
public theorem associatedGradedOf_mul
    {R : Type*} [CommRing R] (I : Ideal R) (i j : ℕ)
    (x : AssociatedGradedPiece I i) (y : AssociatedGradedPiece I j) :
    associatedGradedOf I i x * associatedGradedOf I j y =
      associatedGradedOf I (i + j) (associatedGradedPieceMul I i j x y) := by
  change DirectSum.of (AssociatedGradedPiece I) i x *
      DirectSum.of (AssociatedGradedPiece I) j y =
    DirectSum.of (AssociatedGradedPiece I) (i + j)
      (associatedGradedPieceMul I i j x y)
  exact DirectSum.of_mul_of x y

/-- Every homogeneous class belongs to any subalgebra containing degree one. -/
public theorem associatedGradedOf_mem_adjoin
    {R : Type*} [CommRing R] (I : Ideal R) (S : Set (AssociatedGraded I))
    (hdegreeOne : ∀ x : AssociatedGradedPiece I 1,
      associatedGradedOf I 1 x ∈ Algebra.adjoin (R ⧸ I) S) :
    ∀ (n : ℕ) (x : AssociatedGradedPiece I n),
      associatedGradedOf I n x ∈ Algebra.adjoin (R ⧸ I) S := by
  let _ : Algebra (R ⧸ I) (AssociatedGraded I) :=
    associatedGradedAlgebra I
  change (∀ x : AssociatedGradedPiece I 1,
    associatedGradedOfLinear I 1 x ∈ Algebra.adjoin (R ⧸ I) S) at hdegreeOne
  change ∀ (n : ℕ) (x : AssociatedGradedPiece I n),
    associatedGradedOfLinear I n x ∈ Algebra.adjoin (R ⧸ I) S
  intro n x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      exact associatedGraded_of_mem_adjoin I S hdegreeOne n x

/-- Each homogeneous piece is finite over the residue ring. -/
public theorem associatedGradedPiece_finite
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) (n : ℕ) :
    Module.Finite (R ⧸ I) (AssociatedGradedPiece I n) := by
  exact associatedGradedPieceFinite I n

/-- The class of an element of `I` in the degree-one piece. -/
@[expose] public def associatedGradedDegreeOneClass
    {R : Type*} [CommRing R] (I : Ideal R) :
    I → AssociatedGradedPiece I 1 := fun x ↦
  Submodule.Quotient.mk ⟨x, by
    rw [pow_one]
    exact x.property⟩

set_option linter.style.haveILetI false in
/-- Evaluating a homogeneous polynomial at degree-one classes produces a
homogeneous class of the same degree. -/
public theorem associatedGraded_aeval_isHomogeneous
    {R : Type*} [CommRing R] (I : Ideal R) {σ : Type*}
    (x : σ → AssociatedGradedPiece I 1)
    {p : MvPolynomial σ (R ⧸ I)} {n : ℕ} (hp : p.IsHomogeneous n) :
    ∃ y : AssociatedGradedPiece I n,
      MvPolynomial.aeval (fun i ↦ associatedGradedOf I 1 (x i)) p =
        associatedGradedOf I n y := by
  let C : ℕ → Submodule (R ⧸ I) (AssociatedGraded I) := fun n ↦
    LinearMap.range (associatedGradedOf I n)
  letI : SetLike.GradedMonoid C := {
    one_mem := by
      refine ⟨associatedGradedPieceOne I, ?_⟩
      rw [associatedGradedOf_apply]
      exact (DirectSum.of_zero_one (AssociatedGradedPiece I)).symm
    mul_mem := by
      rintro i j _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨associatedGradedPieceMul I i j a b,
        (associatedGradedOf_mul I i j a b).symm⟩ }
  have hmem :
      MvPolynomial.aeval (fun i ↦ associatedGradedOf I 1 (x i)) p ∈
        C n := by
    induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
    | zero => simp
    | add p q hp hq ihp ihq => simpa using Submodule.add_mem _ ihp ihq
    | monomial s c hs =>
        rw [MvPolynomial.aeval_monomial]
        have hc : algebraMap (R ⧸ I) (AssociatedGraded I) c ∈
            C 0 :=
          SetLike.algebraMap_mem_graded _ _
        have hprod :
            s.prod (fun i e ↦ associatedGradedOf I 1 (x i) ^ e) ∈
              C s.degree := by
          simpa [Finsupp.prod, Finsupp.degree_apply] using
            (SetLike.prod_pow_mem_graded
              C
              (fun _ : σ ↦ 1)
              (fun i ↦ associatedGradedOf I 1 (x i))
              (F := s.support) (fun i ↦ s i)
              (fun i _ ↦ (show associatedGradedOf I 1 (x i) ∈
                C 1 from ⟨x i, rfl⟩)))
        have hs' : s.degree = n := by
          rw [Finsupp.degree_eq_weight_one]
          exact hs
        rw [hs'] at hprod
        simpa using SetLike.mul_mem_graded hc hprod
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, hy.symm⟩

end

end HilbertSamuel
