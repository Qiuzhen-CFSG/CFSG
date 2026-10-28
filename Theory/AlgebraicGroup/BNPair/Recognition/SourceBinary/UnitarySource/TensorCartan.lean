module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.TensorRealization
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.FullTorus
public import Theory.Representation.OrthogonalFourMinusRankOne.AmbientActions.ScalarCentralizer

/-!
# Scalars and the full Cartan on the constructed Hermitian coordinates

Transport the actual Cartan-kernel action through a Hermitian intertwiner
on the same source remainder. It commutes with the full root-generated
SL₂ actor. The proved Hermitian commutant theorem therefore makes each
transported operator a fixed-field scalar. Evaluating on a diagonal matrix
makes this scalar unique and proves multiplicativity. The faithful source
Cartan action and its exact order identify the entire kernel with the
nonzero fixed-field scalars, including the fixed field of order two.

Inverting this identification constructs actual source elements with the
required scalar conjugation law. Combining them with the same relabelled
SL₂ torus gives all four positive-root weights and the full B ∩ N. No
independent scalar-action or field-compatibility premise is introduced.
TensorCartanApplication constructs the intertwiner and the kernel order
from the literal original quadratic profile and applies these results.
The other endpoint's root labels and reflection laws remain separate
source obligations; this module does not assert unitary recognition.

Source: Fong--Seitz II (8B), printed pp.201--202, especially the faithful
H ∩ K₂ action on the four-dimensional fixed-field form of Γ ⊗ Γ̄.
-/

@[expose] public noncomputable section
open Subgroup Representation Matrix
open scoped MatrixGroups IsMulCommutative
open Theory.PSL2.SemilinearCoverage
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
open Representation.OrthogonalFourMinus
open Representation.OrthogonalFourMinus.FiniteModel
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open RootCoordinates HexagonStructure GTwoSource

variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i : Fin 2) (hV : simpleRemainder Q split i ≤ localKernel Q i)
  (μ : localGroup Q split i ≃* PSL(2,F)) (s : RootReflection Q split i)
  (n : ℕ) [NeZero n] (f : F ≃+* Field n)
  (e : Multiplicative (Space n) ≃* simpleRemainder Q split i)

local notation "l" => fieldRelabelledActor Q split i hV μ s n f

omit [NeZero n] in
theorem fieldRelabelledActor_mem (g : SL(2,Field n)) :
    l g ∈ coreActor Q split i :=
  (show rankOne Q split i ≤ coreActor Q split i from le_sup_right) ((alignedPinning Q split i hV μ s)
    (SpecialLinearGroup.map f.symm.toRingHom g)).property

omit [NeZero n] in
theorem tensorCartan_commute (a : coreCartan Q i) (g : SL(2,Field n)) :
    Commute (a : X ⧸ Q.D) (l g) :=
  ((mem_centralizer_iff.mp (coreCartan_centralizes_coreActor Q split i a.property))
    (l g) (fieldRelabelledActor_mem Q split i hV μ s n f g)).symm

def tensorCartanEnd (a : coreCartan Q i) : Space n →+ Space n where
  toFun p := (e.symm (coreCartanAction Q split i a (e (.ofAdd p)))).toAdd
  map_zero' := by simp
  map_add' p q := by simp only [ofAdd_add, map_mul, toAdd_mul]

theorem tensorCartanEnd_conjugation (a : coreCartan Q i) (p : Space n) :
    (e (.ofAdd (tensorCartanEnd Q split i n e a p)) : X ⧸ Q.D) =
      (a : X ⧸ Q.D) * (e (.ofAdd p) : X ⧸ Q.D) * (a : X ⧸ Q.D)⁻¹ := by
  change (e (e.symm _) : X ⧸ Q.D) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

variable (he : ∀ (g : SL(2,Field n)) (p : Space n),
  fieldRelabelledActor Q split i hV μ s n f g * (e (.ofAdd p) : X ⧸ Q.D) *
    (fieldRelabelledActor Q split i hV μ s n f g)⁻¹ =
    e (.ofAdd (action n g p)))

include he in
theorem tensorCartanEnd_scalar (a : coreCartan Q i) :
    ∃ c : fixedField n, ∀ p, tensorCartanEnd Q split i n e a p = c • p := by
  apply RankOne.AmbientActions.commuting_addHom_eq_scalar
  intro g p
  apply Multiplicative.ofAdd.injective
  apply e.injective
  apply Subtype.val_injective
  rw [tensorCartanEnd_conjugation, ← he, ← he, tensorCartanEnd_conjugation]
  have hc := tensorCartan_commute Q split i hV μ s n f a g
  calc
    _ = ((a : X ⧸ Q.D) * l g) * e (.ofAdd p) * ((a : X ⧸ Q.D) * l g)⁻¹ := by group
    _ = (l g * (a : X ⧸ Q.D)) * e (.ofAdd p) * (l g * (a : X ⧸ Q.D))⁻¹ := by rw [hc.eq]
    _ = _ := by group

def tensorCartanCoefficient (a : coreCartan Q i) : fixedField n :=
  (tensorCartanEnd_scalar Q split i hV μ s n f e he a).choose

theorem tensorCartanCoefficient_spec (a : coreCartan Q i) (p : Space n) :
    tensorCartanEnd Q split i n e a p =
      tensorCartanCoefficient Q split i hV μ s n f e he a • p :=
  (tensorCartanEnd_scalar Q split i hV μ s n f e he a).choose_spec p

private theorem hermitian_scalar_eq (c d : fixedField n)
    (h : ∀ p : Space n, c • p = d • p) : c = d := by
  apply Subtype.ext
  have hh := congrArg (fun p : Space n => p.val 0 0)
    (h (FourTensor.diagonalTop (Field n) (conjugation n) (conjugation_involutive n) 1))
  change (c : Field n) * 1 = (d : Field n) * 1 at hh
  simpa only [mul_one] using hh

def tensorCartanCoefficients : coreCartan Q i →* fixedField n where
  toFun := tensorCartanCoefficient Q split i hV μ s n f e he
  map_one' := by
    apply hermitian_scalar_eq n
    intro p
    rw [← tensorCartanCoefficient_spec, one_smul]
    change (e.symm (coreCartanAction Q split i 1 (e (.ofAdd p)))).toAdd = p
    rw [map_one]
    exact congrArg Multiplicative.toAdd (e.symm_apply_apply (.ofAdd p))
  map_mul' a b := by
    apply hermitian_scalar_eq n
    intro p
    rw [← tensorCartanCoefficient_spec, mul_smul,
      ← tensorCartanCoefficient_spec, ← tensorCartanCoefficient_spec]
    change (e.symm (coreCartanAction Q split i (a*b) (e (.ofAdd p)))).toAdd =
      (e.symm (coreCartanAction Q split i a
        (e (e.symm (coreCartanAction Q split i b (e (.ofAdd p))))))).toAdd
    rw [MulEquiv.apply_symm_apply, map_mul]
    rfl

theorem tensorCartanCoefficients_conjugation (a : coreCartan Q i) (p : Space n) :
    (a : X ⧸ Q.D) * (e (.ofAdd p) : X ⧸ Q.D) * (a : X ⧸ Q.D)⁻¹ =
      e (.ofAdd (tensorCartanCoefficients Q split i hV μ s n f e he a • p)) := by
  rw [← tensorCartanEnd_conjugation,
    tensorCartanCoefficient_spec Q split i hV μ s n f e he]
  rfl

variable (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple i}) :
  Set (Q.tits.standardParabolic {Q.simple i})) ≤ pCore 2 (Q.tits.standardParabolic {Q.simple i}))

include hc in
theorem tensorCartanCoefficients_injective :
    Function.Injective (tensorCartanCoefficients Q split i hV μ s n f e he) := by
  intro a b hab
  apply coreCartanAction_injective Q split i hc
  ext v
  obtain ⟨p,rfl⟩ := e.surjective v
  change (a : X ⧸ Q.D) * (e p : X ⧸ Q.D) * (a : X ⧸ Q.D)⁻¹ =
    (b : X ⧸ Q.D) * (e p : X ⧸ Q.D) * (b : X ⧸ Q.D)⁻¹
  exact (tensorCartanCoefficients_conjugation Q split i hV μ s n f e he a p.toAdd).trans
    ((congrArg (fun c : fixedField n => (e (.ofAdd (c • p.toAdd)) : X ⧸ Q.D)) hab).trans
      (tensorCartanCoefficients_conjugation Q split i hV μ s n f e he b p.toAdd).symm)

def tensorCartanUnits : coreCartan Q i →* (fixedField n)ˣ :=
  (tensorCartanCoefficients Q split i hV μ s n f e he).toHomUnits

variable (hcard : Nat.card (coreCartan Q i) = 2^n-1)

include hc hcard in
theorem tensorCartanUnits_bijective :
    Function.Bijective (tensorCartanUnits Q split i hV μ s n f e he) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  constructor
  · intro a b hab
    exact tensorCartanCoefficients_injective Q split i hV μ s n f e he hc
      (congrArg Units.val hab)
  · rw [Nat.card_units, card_fixedField, hcard]

def tensorScalarLift : (fixedField n)ˣ ≃* coreCartan Q i :=
  (MulEquiv.ofBijective (tensorCartanUnits Q split i hV μ s n f e he)
    (tensorCartanUnits_bijective Q split i hV μ s n f e he hc hcard)).symm

def tensorScalar : (fixedField n)ˣ →* X ⧸ Q.D :=
  (coreCartan Q i).subtype.comp
    (tensorScalarLift Q split i hV μ s n f e he hc hcard).toMonoidHom

theorem tensorScalar_range :
    (tensorScalar Q split i hV μ s n f e he hc hcard).range = coreCartan Q i := by
  rw [tensorScalar, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (tensorScalarLift Q split i hV μ s n f e he hc hcard).surjective,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem tensorScalar_conjugation (a : (fixedField n)ˣ) (p : Space n) :
    tensorScalar Q split i hV μ s n f e he hc hcard a * (e (.ofAdd p) : X ⧸ Q.D) *
      (tensorScalar Q split i hV μ s n f e he hc hcard a)⁻¹ =
    e (.ofAdd ((a : fixedField n) • p)) := by
  have ha : tensorCartanUnits Q split i hV μ s n f e he
      (tensorScalarLift Q split i hV μ s n f e he hc hcard a) = a :=
    (MulEquiv.ofBijective _
      (tensorCartanUnits_bijective Q split i hV μ s n f e he hc hcard)).apply_symm_apply a
  exact (tensorCartanCoefficients_conjugation Q split i hV μ s n f e he
    (tensorScalarLift Q split i hV μ s n f e he hc hcard a) p).trans
    (congrArg (fun c : fixedField n => (e (.ofAdd (c • p)) : X ⧸ Q.D))
      (congrArg Units.val ha))

theorem tensorScalar_commute (a : (fixedField n)ˣ) (g : SL(2,Field n)) :
    Commute (tensorScalar Q split i hV μ s n f e he hc hcard a) (l g) :=
  tensorCartan_commute Q split i hV μ s n f
    (tensorScalarLift Q split i hV μ s n f e he hc hcard a) g

omit [NeZero n] in
theorem fieldRelabelledActor_torus_range :
    ((l).comp (BenderSuzuki.Converse.torHom (Field n))).range =
      (alignedTorusHom Q split i hV μ s).range := by
  have ht : (l).comp (BenderSuzuki.Converse.torHom (Field n)) =
      (alignedTorusHom Q split i hV μ s).comp (Units.map f.symm.toMonoidHom) := by
    ext a
    apply congrArg (alignedPinningHom Q split i hV μ s)
    ext j k
    change f.symm ((tor a).val j k) = (tor (Units.map f.symm.toMonoidHom a)).val j k
    fin_cases j <;> fin_cases k <;> simp [tor]
  rw [ht, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (Units.map_bijective (f := f.symm.toMonoidHom) f.symm.bijective).surjective,
    ← MonoidHom.range_eq_map]

def tensorCartan : FourWeyl.torusParameters (Field n) (conjugation n) →* X ⧸ Q.D :=
  FourCartan.hom (Field n) (conjugation n) l
    (tensorScalar Q split i hV μ s n f e he hc hcard)
    (tensorScalar_commute Q split i hV μ s n f e he hc hcard)

theorem tensorCartan_range :
    (tensorCartan Q split i hV μ s n f e he hc hcard).range = Q.tits.B ⊓ Q.tits.N := by
  calc
    _ = (tensorScalar Q split i hV μ s n f e he hc hcard).range ⊔
        ((l).comp (BenderSuzuki.Converse.torHom (Field n))).range :=
      FourCartan.hom_range (Field n) (conjugation n) l
        (tensorScalar Q split i hV μ s n f e he hc hcard)
        (tensorScalar_commute Q split i hV μ s n f e he hc hcard)
    _ = coreCartan Q i ⊔ (alignedTorusHom Q split i hV μ s).range :=
      congrArg₂ (· ⊔ ·) (tensorScalar_range Q split i hV μ s n f e he hc hcard)
        (fieldRelabelledActor_torus_range Q split i hV μ s n f)
    _ = _ := coreCartan_sup_actorTorus Q split i hV μ s

theorem tensorCartan_torusLaws :
    (FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l
      ((simpleRemainder Q split i).subtype.comp e.toMonoidHom)).TorusLaws
      (tensorCartan Q split i hV μ s n f e he hc hcard) :=
  FourCartan.torusLaws (Field n) (conjugation n) (conjugation_involutive n) l
    (tensorScalar Q split i hV μ s n f e he hc hcard)
    (tensorScalar_commute Q split i hV μ s n f e he hc hcard)
    ((simpleRemainder Q split i).subtype.comp e.toMonoidHom) he
    (tensorScalar_conjugation Q split i hV μ s n f e he hc hcard)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
