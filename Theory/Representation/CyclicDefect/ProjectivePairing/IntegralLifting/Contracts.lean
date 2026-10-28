module

public import Theory.Representation.CyclicDefect.ProjectivePairing.LiftContracts
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Coefficient and module inputs for integral projective lifting

The coefficient construction and the lifting of projective summands are
independent. The first supplies a complete discrete valuation ring with the
specified residue field and root correspondence. The second lifts a projective
residue representation over that fixed ring, retaining an actual equivalence
after reduction. Neither structure asserts existence.

The source construction lifts idempotents in a complete algebra (Feit,
*The Representation Theory of Finite Groups*, I.12.3--4), then takes their
projective summands (I.13, I.17). Completeness here is with respect to the
maximal ideal; the nil-kernel lifting theorem alone does not suffice.
-/

public section
noncomputable section

namespace Representation.CyclicDefect.ProjectivePairing.IntegralLifting

variable {k : Type*} [Field k] {m : ℕ}

/-- A complete coefficient ring, independently of any representation. -/
structure CompleteCoefficientRing (L : CyclicRootLift k m) where
  Coeff : Type
  [coeffRing : CommRing Coeff]
  [coeffDomain : IsDomain Coeff]
  [coeffDVR : IsDiscreteValuationRing Coeff]
  [coeffLocal : IsLocalRing Coeff]
  [coeffComplete : IsAdicComplete (IsLocalRing.maximalIdeal Coeff) Coeff]
  complex : Coeff →+* ℂ
  complex_injective : Function.Injective complex
  residue : Coeff →+* k
  residue_surjective : Function.Surjective residue
  residue_ker : RingHom.ker residue = IsLocalRing.maximalIdeal Coeff
  root : Coeff
  root_pow : root ^ m = 1
  root_complex : complex root = L.complexRoot
  root_residue : residue root = L.modularRoot

attribute [instance] CompleteCoefficientRing.coeffRing CompleteCoefficientRing.coeffDomain
  CompleteCoefficientRing.coeffDVR CompleteCoefficientRing.coeffLocal
  CompleteCoefficientRing.coeffComplete

variable {R G : Type*} [CommRing R] [Group G] {n : ℕ}

/-- The precise idempotent lifting input for finite projective group modules.
The coefficient map acts on the actual group algebra and then on matrices. -/
def MatrixIdempotentsLift (f : R →+* k) (G : Type*) [Group G] : Prop :=
  ∀ (n : ℕ) (e : Matrix (Fin n) (Fin n) (MonoidAlgebra k G)),
    IsIdempotentElem e →
    ∃ e' : Matrix (Fin n) (Fin n) (MonoidAlgebra R G),
      IsIdempotentElem e' ∧ (MonoidAlgebra.mapRingHom G f).mapMatrix e' = e

/-- The matrix lifting contract, available without exposing its definition body. -/
theorem matrixIdempotentsLift_iff (f : R →+* k) :
    MatrixIdempotentsLift f G ↔
      ∀ (n : ℕ) (e : Matrix (Fin n) (Fin n) (MonoidAlgebra k G)),
        IsIdempotentElem e →
        ∃ e' : Matrix (Fin n) (Fin n) (MonoidAlgebra R G),
          IsIdempotentElem e' ∧ (MonoidAlgebra.mapRingHom G f).mapMatrix e' = e :=
  Iff.rfl

/-- A projective lift over a specified coefficient ring. Its reduction is
equivalent to the specified residue representation, not just equidimensional. -/
structure ResidueProjectiveLift (f : R →+* k)
    (Q : Representation k G (Fin n → k)) where
  degree : ℕ
  rep : Representation R G (Fin degree → R)
  projective : Module.Projective (MonoidAlgebra R G) rep.asModule
  reduction : (mapCoefficients f rep).Equiv Q

end Representation.CyclicDefect.ProjectivePairing.IntegralLifting
