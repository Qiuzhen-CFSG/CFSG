module
public import Theory.Representation.BinaryPermutation.SevenSourceCubics.Alternating
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Simultaneous Sylow and natural-module markings

Conjugating a quotient marking sends its chosen Sylow subgroup to the marked
Sylow in the permutation model. Acting by the inverse conjugating element on
the model module preserves the given representation equivalence.

Source: Aschbacher–Smith, 14.7.50, printed p.1065, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation BinaryPermutation
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.NaturalMarking

/-- Inner conjugation places the chosen Sylow at any prescribed model Sylow
while retaining an equivalence with the original representation. -/
theorem exists_sylow_marking
    {R X Y M N : Type*} [CommSemiring R]
    [Group X] [Finite X] [Group Y] [Finite Y]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (p : ℕ) [Fact p.Prime] (P : Sylow p X) (Q : Sylow p Y)
    (ρ : Representation R Y M) (σ : Representation R X N)
    (b : X ≃* Y) (m : Representation.Equiv (ρ.comp b.toMonoidHom) σ) :
    ∃ b' : X ≃* Y, (P : Subgroup X).map b'.toMonoidHom = (Q : Subgroup Y) ∧
      Nonempty (Representation.Equiv (ρ.comp b'.toMonoidHom) σ) := by
  let P' := P.mapSurjective (f := b.toMonoidHom) b.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Y P' Q
  refine ⟨b.trans (MulAut.conj g), ?_, ?_⟩
  · change (P : Subgroup X).map ((MulAut.conj g).toMonoidHom.comp b.toMonoidHom) = _
    rw [← Subgroup.map_map]
    change ((g • P' : Sylow p Y) : Subgroup Y) = (Q : Subgroup Y)
    rw [hg]
  · let e := (LinearEquiv.ofBijective (ρ g⁻¹) (ρ.apply_bijective g⁻¹)).trans m.toLinearEquiv
    refine ⟨Representation.Equiv.mk e ?_⟩
    intro x
    ext v
    change m (ρ g⁻¹ (ρ (g * b x * g⁻¹) v)) = σ x (m (ρ g⁻¹ v))
    have hh : ρ g⁻¹ (ρ (g * b x * g⁻¹) v) = ρ (b x) (ρ g⁻¹ v) := by
      simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_left, mul_assoc]
    rw [hh]
    exact congrArg (fun f : M →ₗ[R] N => f (ρ g⁻¹ v)) (m.isIntertwining' x)

variable {X N : Type*} [Group X] [Finite X]
  [AddCommMonoid N] [Module (ZMod 2) N]

/-- An S₇ natural-module marking can carry the actual Sylow to the standard
Sylow without changing the represented local action. -/
theorem symmetric_sylow_marking (P : Sylow 2 X)
    (σ : Representation (ZMod 2) X N) (b : X ≃* Equiv.Perm (Fin 7))
    (m : Representation.Equiv ((coreRepresentation (Fin 7)).comp b.toMonoidHom) σ) :
    ∃ b' : X ≃* Equiv.Perm (Fin 7),
      (P : Subgroup X).map b'.toMonoidHom = standardTwo ∧
      Nonempty (Representation.Equiv ((coreRepresentation (Fin 7)).comp b'.toMonoidHom) σ) :=
  exists_sylow_marking 2 P standardSylow (coreRepresentation (Fin 7)) σ b m

/-- An A₇ natural-module marking can carry the actual Sylow to the even part
of the standard permutation Sylow. -/
theorem alternating_sylow_marking (P : Sylow 2 X)
    (σ : Representation (ZMod 2) X N) (b : X ≃* alternatingGroup (Fin 7))
    (m : Representation.Equiv ((alternatingCoreRepresentation (Fin 7)).comp b.toMonoidHom) σ) :
    ∃ b' : X ≃* alternatingGroup (Fin 7),
      (P : Subgroup X).map b'.toMonoidHom = SevenSourceCubics.Alternating.two ∧
      Nonempty (Representation.Equiv
        ((alternatingCoreRepresentation (Fin 7)).comp b'.toMonoidHom) σ) :=
  exists_sylow_marking 2 P SevenSourceCubics.Alternating.sylow
    (alternatingCoreRepresentation (Fin 7)) σ b m

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.NaturalMarking
