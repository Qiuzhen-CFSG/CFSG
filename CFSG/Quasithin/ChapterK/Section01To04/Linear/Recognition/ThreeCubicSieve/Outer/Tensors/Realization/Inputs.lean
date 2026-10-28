module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Model

/-!
# Component coordinates and actor lifts for the SL₃ tensor exchange

The component may have a central kernel. Consequently the half tensor is a
representation of SL₃ itself: it need not factor through the image of the full
tensor. An actor lift records its literal intertwining equation on that cover.
A companion is an actual member of the original actor, represented by an
involution of the cover fixed by the lifted automorphism.

The two remaining inputs separate automorphism lifting and selection from
word geometry. Paired coordinates specify only the component action, not the
action of the outer operator. Schur comparison supplies the latter in `Paired`.
Source: GM, Classification of 2F-modules II, Proposition 4.8 steps 2–5,
manuscript pp.26–28; Aschbacher–Smith K.3.2, printed pp.454–456.
-/

@[expose] public section
noncomputable section
open Representation Representation.BinaryOffender
open Representation.BinaryOffender.SchurNormalizer
open Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open scoped MatrixGroups TensorProduct

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization

variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V) [IsIrreducible σ]

/-- A lift to the actual central cover, with the original operator retained. -/
structure LiftedInvolution (t : linearNormalizer σ) where
  automorphism : MulAut SL(3,B.Carrier)
  actor_square : t ^ 2 = 1
  square : automorphism ^ 2 = 1
  intertwines : ∀ g, t.val.val * σ g = σ (automorphism g) * t.val.val

/-- A nonidentity actor with a fixed involutory lift in the component cover. -/
def HasInnerCompanion (A : Subgroup (linearNormalizer σ))
    (α : MulAut SL(3,B.Carrier)) : Prop :=
  ∃ u : A, u ≠ 1 ∧ ∃ x : SL(3,B.Carrier),
    x ^ 2 = 1 ∧ α x = x ∧ u.val.val = σ.asGroupHom x

/-- Only component coordinates are prescribed. The half representation is on
the cover, since its central character can cancel that of the other half. -/
structure PairedTensorCoordinates (α : MulAut SL(3,B.Carrier)) where
  size : ℕ
  three_le : 3 ≤ size
  half : Representation (SplittingField σ) SL(3,B.Carrier)
    (Fin size → SplittingField σ)
  equiv : (SplittingField σ ⊗[SchurField σ] σ.asModule) ≃ₗ[SplittingField σ]
    TensorInterchange.Space (SplittingField σ) size
  component_action : ∀ g v,
    equiv (extendScalars (SplittingField σ) σ.endFieldRep g v) =
      TensorProduct.map (half g) (half (α g)) (equiv v)

/-- Automorphism coverage, scalar-kernel control and rank selection. No tensor
coordinates or fixed-space conclusion are part of this input. -/
def LiftedOuterActors : Prop :=
  ∀ A : Subgroup (linearNormalizer σ), IsElementaryTwo A →
    ¬ A.map (linearNormalizer σ).subtype ≤ actionImage σ →
    ∃ t : A, t.val.val ∉ actionImage σ ∧
      ∃ L : LiftedInvolution B σ t.val,
        2 < rank A → HasInnerCompanion B σ A L.automorphism

/-- Word uniqueness and the field/graph-field calculation must provide paired
component coordinates. In the pure graph case the natural factor is impossible. -/
def NaturalPairedCoordinates : Prop :=
  ∀ M : RepeatedModel B σ, 0 < naturalCount M.block → ¬ M.Small →
    ∀ t : linearNormalizer σ, t.val ∉ actionImage σ → IsSchurLinear σ t →
      ∀ L : LiftedInvolution B σ t,
        Nonempty (PairedTensorCoordinates B σ L.automorphism)

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization
