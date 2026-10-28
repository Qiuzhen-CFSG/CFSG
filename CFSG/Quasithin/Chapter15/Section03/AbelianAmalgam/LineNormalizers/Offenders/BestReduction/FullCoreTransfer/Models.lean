module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement

/-!
# Shared model contracts for the action-image bootstrap

These are the proposed rank-one survivors to be PROVED from the full earlier
B.5.6/B.5.1 alternatives. No classifier or source theorem is asserted here.
The actual model maps retain a central kernel and a trivial outer quotient;
neither extension is required to split. In the symmetric-five branch those
conditions are required only for its embedded alternating-five subgroup.

The two independent consumers are the full rank-one classification dispatch
and the concrete natural-module estimates. Final assembly must produce these
witnesses by the former before applying the latter.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.1, p.99,
B.5.6, p.105, and proof of 15.3.67, pp.1153–1154.
-/

@[expose] public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer
open ChapterB.QuasisimpleSource
universe u v
variable {D : Type u} [Group D] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

/-- An actual central section for a specified embedded model actor. -/
structure ModelSection {L X : Type*} [Group L] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) D W) (f : L →* D)
    (σ : Representation (ZMod 2) L X) where
  space : Subrepresentation (ρ.comp f)
  projection : space.toSubmodule →ₗ[ZMod 2] X
  surjective : Function.Surjective projection
  intertwines : ∀ g v, projection (space.toRepresentation g v) = σ g (projection v)
  kernel_fixed : ∀ g v, projection v = 0 → space.toRepresentation g v = v
  quotient_trivial : ∀ g v, ρ (f g) v - v ∈ space

/-- A target family, not an assumption allowed in the final source theorem.
The rank-one dispatcher must prove this from all of B.5.6, retaining B.5.1's
central-section data. The SL₂ branch includes degree one. -/
inductive RankOneModel (ρ : Representation (ZMod 2) D W) : Prop
  | linearTwo (F : BinaryField)
      (actor : D ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier)
      (sectionData : ModelSection ρ actor.symm.toMonoidHom (linearNatural F 2))
  | symmetricFive (actor : D ≃* Equiv.Perm (Fin 5))
      (sectionData : ModelSection ρ
        (actor.symm.toMonoidHom.comp (alternatingGroup (Fin 5)).subtype)
        (alternatingNatural 5))
  | linearThree (F : BinaryField) (odd_degree : Odd F.degree)
      (copies : ℕ) (copies_one_or_two : copies = 1 ∨ copies = 2)
      (actor : D ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
      (sectionData : ModelSection ρ actor.symm.toMonoidHom
        (repeated (linearNatural F 3) copies))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer
