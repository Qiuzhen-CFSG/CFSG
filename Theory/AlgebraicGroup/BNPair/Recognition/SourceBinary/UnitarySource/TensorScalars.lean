module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.CoreCoefficients
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.FourTensor
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Actual source scalars and lifting a realization from the same core

Invert the faithful Cartan-kernel map onto the units of its constructed
coefficient field. This gives actual group elements realizing every
nonzero scalar. When the complementary subgroup has trivial Frattini
subgroup, a semilinear tensor realization of its Frattini section lifts
to that very subgroup. Both scalar and actor intertwining equations then
become literal conjugation equations. Scalar commutation with the whole
core actor follows from the established source centralizer theorem.

The coefficient-field isomorphism can be chosen from the proved orders;
it is not an input to CartanApplication. The genuine equivariant module
realization, remainder containment and exact Cartan order remain source
obligations. This does not identify an arbitrary parabolic with SL₂.

Source: Fong--Seitz II (8B), printed p.201, using I (6A), pp.37--38.
The original-quotient consumer is UnitarySource/CartanApplication.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MonoidAlgebra IsMulCommutative
open Theory.SpecificGroups.ClassicalUnitary
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)
variable (hV : simpleRemainder Q split i ≤ HexagonStructure.localKernel Q i)
variable [Representation.IsIrreducible (coreActorRepresentation Q split i hV)]
variable (n : ℕ) (hn : 0 < n)
variable (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple i}) :
  Set (Q.tits.standardParabolic {Q.simple i})) ≤ pCore 2 (Q.tits.standardParabolic {Q.simple i}))
variable (hcard : Nat.card (coreCartan Q i) = 2^n-1)

def coreCoefficientLift : (CoreCoefficientField Q split i hV n)ˣ ≃* coreCartan Q i :=
  (MulEquiv.ofBijective (coreCoefficientUnits Q split i hV n hcard)
    (coreCoefficientUnits_bijective Q split i hV n hn hc hcard)).symm

theorem coreCoefficientLift_smul (a : (CoreCoefficientField Q split i hV n)ˣ)
    (v : (coreActorRepresentation Q split i hV).asModule) :
    coreFrattiniRepresentation Q split i (coreCoefficientLift Q split i hV n hn hc hcard a)
      ((coreActorRepresentation Q split i hV).asModuleEquiv v) =
      (coreActorRepresentation Q split i hV).asModuleEquiv
        ((a : CoreCoefficientField Q split i hV n) • v) := by
  have he := coreCoefficientUnits_smul Q split i hV n hcard
    (coreCoefficientLift Q split i hV n hn hc hcard a) v
  have ha : coreCoefficientUnits Q split i hV n hcard
      (coreCoefficientLift Q split i hV n hn hc hcard a) = a :=
    (MulEquiv.ofBijective _ (coreCoefficientUnits_bijective Q split i hV n hn hc hcard)).apply_symm_apply a
  rw [ha] at he
  exact he.symm

variable (hphi : frattini (simpleRemainder Q split i) = ⊥)

def coreProjectionEquiv : simpleRemainder Q split i ≃*
    ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i)) :=
  MulEquiv.ofBijective (QuotientGroup.mk' (frattini (simpleRemainder Q split i)))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk',hphi]),
      QuotientGroup.mk'_surjective _⟩

@[simp] theorem coreProjectionEquiv_apply (v : simpleRemainder Q split i) :
    coreProjectionEquiv Q split i hphi v = QuotientGroup.mk' _ v := rfl

variable {E : Type*} [Field E]
variable (σ : E ≃+* E) (hσ : Function.Involutive σ)
/-- Choose coefficients inside the actual commuting field using its proved order. -/
def coreCoefficientFieldEquiv [Finite E]
    (hq : Nat.card (UnitaryFourSylow.FixedField E σ) = 2^n) :
    UnitaryFourSylow.FixedField E σ ≃+* CoreCoefficientField Q split i hV n := by
  letI := Fintype.ofFinite (UnitaryFourSylow.FixedField E σ)
  letI := Fintype.ofFinite (CoreCoefficientField Q split i hV n)
  apply FiniteField.ringEquivOfCardEq
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hq,
    coreCoefficientField_card Q split i hV n hn hc (hcard ▸ dvd_refl _)]

variable (η : UnitaryFourSylow.FixedField E σ ≃+* CoreCoefficientField Q split i hV n)
local instance : RingHomInvPair η.toRingHom η.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv η
local instance : RingHomInvPair η.symm.toRingHom η.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm η

variable (ψ : FourTensor.Core E σ hσ ≃ₛₗ[η.toRingHom]
  (coreActorRepresentation Q split i hV).asModule)

def intrinsicTensorRealization : Multiplicative (FourTensor.Core E σ hσ) ≃*
    simpleRemainder Q split i :=
  (AddEquiv.toMultiplicativeLeft (ψ.toAddEquiv.trans
    (coreActorRepresentation Q split i hV).asModuleEquiv.toAddEquiv)).trans
      (coreProjectionEquiv Q split i hphi).symm

theorem intrinsicTensorRealization_coordinate (v : FourTensor.Core E σ hσ) :
    Additive.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split i))
      (intrinsicTensorRealization Q split i hV n hphi σ hσ η ψ (.ofAdd v))) =
      (coreActorRepresentation Q split i hV).asModuleEquiv (ψ v) := by
  exact congrArg Additive.ofMul
    ((coreProjectionEquiv Q split i hphi).apply_symm_apply _)

def intrinsicScalar : (UnitaryFourSylow.FixedField E σ)ˣ →* (X ⧸ Q.D) :=
  (coreCartan Q i).subtype.comp
    ((coreCoefficientLift Q split i hV n hn hc hcard).toMonoidHom.comp
      (Units.map η.toMonoidHom))

theorem intrinsicScalar_mem (a : (UnitaryFourSylow.FixedField E σ)ˣ) :
    intrinsicScalar Q split i hV n hn hc hcard σ η a ∈ coreCartan Q i :=
  (coreCoefficientLift Q split i hV n hn hc hcard (Units.map η.toMonoidHom a)).property

theorem intrinsicTensorRealization_scalar (a : (UnitaryFourSylow.FixedField E σ)ˣ)
    (v : FourTensor.Core E σ hσ) :
    intrinsicScalar Q split i hV n hn hc hcard σ η a *
      (intrinsicTensorRealization Q split i hV n hphi σ hσ η ψ (.ofAdd v) : X ⧸ Q.D) *
      (intrinsicScalar Q split i hV n hn hc hcard σ η a)⁻¹ =
    (intrinsicTensorRealization Q split i hV n hphi σ hσ η ψ
      (.ofAdd ((a : UnitaryFourSylow.FixedField E σ) • v)) : X ⧸ Q.D) := by
  let k := coreCoefficientLift Q split i hV n hn hc hcard (Units.map η.toMonoidHom a)
  change (coreCartanAction Q split i k
    (intrinsicTensorRealization Q split i hV n hphi σ hσ η ψ (.ofAdd v)) : X ⧸ Q.D) = _
  apply congrArg Subtype.val
  apply (coreProjectionEquiv Q split i hphi).injective
  apply Additive.ofMul.injective
  simp only [coreProjectionEquiv_apply]
  rw [← Subgroup.quotientAut_apply_mk]
  change coreFrattiniRepresentation Q split i k
    (Additive.ofMul (QuotientGroup.mk' _
      (intrinsicTensorRealization Q split i hV n hphi σ hσ η ψ (.ofAdd v)))) = _
  rw [intrinsicTensorRealization_coordinate,intrinsicTensorRealization_coordinate]
  rw [coreCoefficientLift_smul,ψ.map_smulₛₗ]
  rfl

/-- The scalar lift commutes with the whole actual core actor. -/
theorem intrinsicScalar_commute (a : (UnitaryFourSylow.FixedField E σ)ˣ)
    (g : coreActor Q split i) :
    Commute (intrinsicScalar Q split i hV n hn hc hcard σ η a) (g : X ⧸ Q.D) :=
  ((mem_centralizer_iff.mp (coreCartan_centralizes_coreActor Q split i
    (intrinsicScalar_mem Q split i hV n hn hc hcard σ η a))) g g.property).symm

variable (linearActor : Matrix.SpecialLinearGroup (Fin 2) E →* coreActor Q split i)
variable (hlinear : ∀ g v, ψ
    (Representation.OrthogonalFourMinus.hermitianAction (FourTensor.conjugation E σ) hσ g v) =
    coreCoefficientRepresentation Q split i hV n (linearActor g) (ψ v))

include hlinear in
/-- An intertwiner on the original Frattini section gives literal conjugation. -/
theorem intrinsicTensorRealization_actor (g : Matrix.SpecialLinearGroup (Fin 2) E)
    (v : FourTensor.Core E σ hσ) :
    (linearActor g : X ⧸ Q.D) *
      (intrinsicTensorRealization Q split i hV n hphi σ hσ η ψ (.ofAdd v) : X ⧸ Q.D) *
      (linearActor g : X ⧸ Q.D)⁻¹ =
    (intrinsicTensorRealization Q split i hV n hphi σ hσ η ψ
      (.ofAdd (Representation.OrthogonalFourMinus.hermitianAction
        (FourTensor.conjugation E σ) hσ g v)) : X ⧸ Q.D) := by
  change (coreActorAction Q split i hV (linearActor g)
    (intrinsicTensorRealization Q split i hV n hphi σ hσ η ψ (.ofAdd v)) : X ⧸ Q.D) = _
  apply congrArg Subtype.val
  apply (coreProjectionEquiv Q split i hphi).injective
  apply Additive.ofMul.injective
  simp only [coreProjectionEquiv_apply]
  rw [← Subgroup.quotientAut_apply_mk]
  change coreActorRepresentation Q split i hV (linearActor g)
    (Additive.ofMul (QuotientGroup.mk' _
      (intrinsicTensorRealization Q split i hV n hphi σ hσ η ψ (.ofAdd v)))) = _
  rw [intrinsicTensorRealization_coordinate,intrinsicTensorRealization_coordinate,hlinear,
    coreCoefficientRepresentation_apply]


end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
