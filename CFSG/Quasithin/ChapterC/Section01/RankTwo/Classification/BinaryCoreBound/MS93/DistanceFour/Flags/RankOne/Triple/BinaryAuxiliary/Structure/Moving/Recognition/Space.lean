module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural.Kernel.FixedSummand.Linear
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The full moving subrepresentation and its natural coordinates

The moving space is the span of all differences for the genuine S3 action.
It inherits that action. A natural marking includes both a linear equivalence
and a group isomorphism to the literal SL2(2), together with equivariance.
`SmallReflectionBound` states the linear bound proved in `Reflection` to recognize
this subspace; it allows an arbitrary central summand in the ambient module.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
open Incident.Pairing.Transport.Natural.Kernel

/-- The span of all action differences with the inherited full-actor action. -/
def movedSpace {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) BinaryS3.Actor W) : Subrepresentation ρ where
  toSubmodule := subspaceCommutator ρ ⊤ ⊤
  apply_mem_toSubmodule g := by
    change subspaceCommutator ρ ⊤ ⊤ ≤ (subspaceCommutator ρ ⊤ ⊤).comap (ρ g)
    apply Submodule.span_le.mpr
    rintro _ ⟨h, _, v, _, rfl⟩
    have hgh : ρ (g * h) v - v ∈ subspaceCommutator ρ ⊤ ⊤ :=
      Submodule.subset_span ⟨g * h, mem_top _, v, Submodule.mem_top, rfl⟩
    have hg : ρ g v - v ∈ subspaceCommutator ρ ⊤ ⊤ :=
      Submodule.subset_span ⟨g, mem_top _, v, Submodule.mem_top, rfl⟩
    change ρ g (ρ h v - v) ∈ subspaceCommutator ρ ⊤ ⊤
    have he : ρ g (ρ h v - v) = (ρ (g * h) v - v) - (ρ g v - v) := by
      rw [map_sub, map_mul, Module.End.mul_apply]
      abel
    rw [he]
    exact Submodule.sub_mem _ hgh hg

/-- Coordinates for the actual moving action, with an invertible actor marking. -/
structure NaturalMoving {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) BinaryS3.Actor W) where
  marking : BinaryS3.Actor ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
  coordinates : (movedSpace ρ).toSubmodule ≃ₗ[ZMod 2] (Fin 2 → ZMod 2)
  action : ∀ g v, coordinates ((movedSpace ρ).toRepresentation g v) =
    (marking g).val.mulVec (coordinates v)

/-- The representation-theoretic bound established in `Reflection`. Its premise concerns one
reflection on the whole space; its conclusion bounds the full moving subspace.
This proposition does not restrict the dimension of the whole representation. -/
def SmallReflectionBound : Prop :=
  ∀ {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) BinaryS3.Actor W) (t : BinaryS3.Actor),
    t ^ 2 = 1 → t ≠ 1 → Nat.card (BinaryS3.displacement ρ t) ≤ 2 →
      Nat.card (movedSpace ρ).toSubmodule ≤ 4

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
