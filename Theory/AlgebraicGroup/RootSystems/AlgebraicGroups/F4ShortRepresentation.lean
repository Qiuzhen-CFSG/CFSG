module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism.WordDescent
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism.ShortTransport
public import Theory.AlgebraicGroup.Representations.Algebraic.Natural
public import Theory.AlgebraicGroup.Representations.Operations

/-!
# The faithful rational short-ideal action of the literal F4 carrier

In characteristic two the span of the short root coordinates and short simple
Cartan coordinates is invariant in the integral Geck representation. We
restrict the actual carrier's matrix action to that subspace, retaining the
pointwise matrix formula and proving rationality by invariant restriction.

Restricted adjoint transport proves faithfulness: a matrix fixing this ideal
commutes with all short root operators, whose images lie in the ideal and
whose common kernel is zero. The characteristic-two transport proof is
reused from `ExceptionalMorphism.ShortTransport`; no simplicity or
semisimplicity premise enters the construction. Irreducibility is a separate
obligation, not a field of the representation data.

Source: Steinberg, *Lectures on Chevalley Groups*, the integral construction
and the characteristic-two F4 setting of Theorem 28
(`refs/KGroup/GLS3/Chapter2St1.tex`).
-/

@[expose] public section

open scoped Classical Matrix
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open ReeF4.WordRelations ReeF4.WordRelations.Faithfulness.RestrictedAdjoint
open ReeF4.BinaryDegree.ExceptionalTensor.Classification
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism

noncomputable section
namespace Theory.AlgebraicGroup.F4Chevalley
variable {k : Type*} [Field k] [IsAlgClosed k]

/-- The defining matrix action of the literal closed F4 carrier. -/
def naturalRepresentation : RationalRepresentation (Carrier (k := k)) (BasisIndex → k) where
  action := Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp pointMatrix

theorem naturalRepresentation_isRational :
    IsRationalRepresentation (naturalRepresentation (k := k)) := by
  let b := carrierBasis (P := typeF4RootPairing) (b := typeF4RootPairing_base) (k := k)
  let σ := naturalClosedLinearSubgroupRepresentation (K := Carrier (k := k)) b
    (ambientClosedCarrier (k := k)) (AlgebraicGroup.Iso.id (Carrier (k := k)))
  have heq : σ.action = naturalRepresentation.action := by
    apply MonoidHom.eq_of_eqOn_dense
      ReeF4.BinaryDegree.ExceptionalTensor.algebraicRootElements_generate
    rintro _ ⟨⟨r, t⟩, rfl⟩
    change glPointEquivOf k (BasisIndex → k) b
        ((ambientClosedCarrier (k := k)).inclusion.onPoints
          ((rootMorphism r).onPoints (kPlusPoint t))) =
      Matrix.GeneralLinearGroup.toLin
        (pointMatrix (ReeF4.BinaryDegree.ExceptionalTensor.algebraicRootElement r t))
    rw [pointMatrix_root, rootMorphism_inclusion_apply, ambientRootMorphism_apply]
    exact glPointEquivOf_generalLinearRepresentationPoint b _
  obtain ⟨e, f, hf⟩ := naturalClosedLinearSubgroupRepresentation_isRational
    (K := Carrier (k := k)) b (ambientClosedCarrier (k := k))
    (AlgebraicGroup.Iso.id (Carrier (k := k)))
  exact ⟨e, f, fun g => (hf g).trans (DFunLike.congr_fun heq g)⟩

/-- Vectors supported on the short roots and short simple Cartan coordinates. -/
def shortSubmodule : Submodule k (BasisIndex → k) where
  carrier := {v | ShortSupported v}
  zero_mem' := by intro j _; rfl
  add_mem' := by intro x y hx hy j hj; simp [hx j hj, hy j hj]
  smul_mem' := by intro a x hx j hj; simp [hx j hj]

theorem shortSubmodule_invariant [CharP k 2] :
    IsInvariantSubmodule (naturalRepresentation (k := k)) shortSubmodule := by
  intro g v hv
  exact matrixGroup_preserves_short (pointMatrix g) (pointMatrix_mem g) v hv

/-- The rational restriction of the actual F4 action to its short ideal. -/
def shortRepresentation [CharP k 2] :
    RationalRepresentation (Carrier (k := k)) (shortSubmodule (k := k)) :=
  (rationalRepresentation_restriction_exists naturalRepresentation
    naturalRepresentation_isRational shortSubmodule shortSubmodule_invariant).choose

theorem shortRepresentation_restriction [CharP k 2] :
    IsRestrictionRepresentation naturalRepresentation shortSubmodule
      (shortRepresentation (k := k)) :=
  (rationalRepresentation_restriction_exists naturalRepresentation
    naturalRepresentation_isRational shortSubmodule shortSubmodule_invariant).choose_spec.1

theorem shortRepresentation_isRational [CharP k 2] :
    IsRationalRepresentation (shortRepresentation (k := k)) :=
  (rationalRepresentation_restriction_exists naturalRepresentation
    naturalRepresentation_isRational shortSubmodule shortSubmodule_invariant).choose_spec.2

theorem shortRepresentation_apply [CharP k 2]
    (g : Variety.Point (Carrier (k := k))) (v : shortSubmodule (k := k)) :
    ((shortRepresentation.action g : Module.End k shortSubmodule) v : BasisIndex → k) =
      (pointMatrix g : Matrix BasisIndex BasisIndex k) *ᵥ (v : BasisIndex → k) :=
  shortRepresentation_restriction g v

/-- The short-ideal action detects every point of the literal carrier. -/
theorem shortRepresentation_faithful [CharP k 2] :
    Function.Injective (shortRepresentation (k := k)).action := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro g hg
  change g = 1
  change shortRepresentation.action g = 1 at hg
  apply pointMatrix_injective
  rw [map_one]
  apply eq_one_of_short_transport hasShortAdjointTransport _ (pointMatrix_mem g)
  apply (mul_quotientToIdeal_eq_iff _).mpr
  intro j hj i
  let v : shortSubmodule (k := k) := ⟨Pi.single j 1, shortSupported_single j hj⟩
  have h := shortRepresentation_apply g v
  rw [hg] at h
  have hc := congrFun h.symm i
  simpa [v, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] using hc

instance shortSubmodule_nontrivial : Nontrivial (shortSubmodule (k := k)) := by
  let j : BasisIndex := Sum.inr (typeF4RootPairing_baseEquiv 2).val
  have hj : IsShortCoordinate j :=
    (ReeF4.WordRelations.ShortOperators.isShortRoot_simple 2).mpr (by decide)
  let v : shortSubmodule (k := k) := ⟨Pi.single j 1, shortSupported_single j hj⟩
  refine ⟨⟨v, 0, ?_⟩⟩
  intro h
  have hc := congrFun (congrArg Subtype.val h) j
  simp [v] at hc

end Theory.AlgebraicGroup.F4Chevalley
