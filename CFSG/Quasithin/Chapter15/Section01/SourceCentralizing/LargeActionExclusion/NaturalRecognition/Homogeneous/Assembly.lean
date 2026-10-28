module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Homogeneous.Repeated
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.NaturalDual

/-!
# Assembly boundary for the homogeneous alternatives

The B.5 moved-case constructors are consumed on the literal quotient action.
This small assembly theorem keeps the source alternatives separate: repeated
and natural-dual branches are discharged by their existing source consumers,
while the orthogonal and exterior branches are supplied by their geometric
exclusions.  The theorem does not identify a model from a dimension tag.

Source: Aschbacher--Smith 15.1.28, printed pp.1102--1103.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Theory.SpecificGroups.BinaryComponentResidual ChapterA.Section05To06 Section03 Section03.InitialSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

namespace HomogeneousAssembly

/-- A literal moved-case exclusion package for one B.5 section. -/
structure Exclusions (ρ : Representation (ZMod 2) D V)
    (L : Subgroup D) (s : MovedSection ρ L) (n : ℕ) where
  naturalDual : L = ⊤ → IsNaturalPlusDual (s.space.toRepresentation.comp L.subtype) n → False
  repeated : ∀ r : ℕ, 0 < r → r ≤ n - 1 →
    IsRepeatedLinearNatural (s.space.toRepresentation.comp L.subtype)
      BinaryField.two n r →
      r = 1 ∧ Nonempty (ActionEquiv (s.space.toRepresentation.comp L.subtype)
        (linearNatural BinaryField.two n))
  orthogonal : n = 4 →
    ActionEquiv (s.action.comp L.subtype) (alternatingNatural 8) →
    (IsAlternatingNatural (s.space.toRepresentation.comp L.subtype) 8 ∨
      Nonempty (ActionEquiv (s.space.toRepresentation.comp L.subtype)
        (BinaryPermutation.alternatingCoreRepresentation (Fin 8)))) →
    (Module.finrank (ZMod 2) s.space.toSubmodule = 6 ∨
      Module.finrank (ZMod 2) s.space.toSubmodule = 7) → False
  exterior : n = 5 → L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) →
    IsIrreducible (s.space.toRepresentation.comp L.subtype) →
    Module.finrank (ZMod 2) s.space.toSubmodule = 10 → False

omit [Finite D] [FiniteDimensional (ZMod 2) V] in
/-- The nonnatural B.5 constructors are removed on the same section. -/
theorem natural_of_movedCase {ρ : Representation (ZMod 2) D V}
    {L : Subgroup D} {s : MovedSection ρ L} {n : ℕ}
    (hwhole : L = ⊤)
    (h : Exclusions ρ L s n)
    (m : BinaryActor.MovedCase s n) :
    Nonempty (ActionEquiv (s.space.toRepresentation.comp L.subtype)
      (linearNatural BinaryField.two n)) := by
  cases m with
  | natural a => exact ⟨a⟩
  | orthogonal hd a hm hdim => exact (h.orthogonal hd a hm hdim).elim
  | exterior hd e hi hdim => exact (h.exterior hd e hi hdim).elim
  | naturalDual hn => exact (h.naturalDual hwhole hn).elim
  | repeatedNatural r hp hb hn =>
      exact (h.repeated r hp hb hn).2

end HomogeneousAssembly
end CFSG.Quasithin.Chapter15.Section01
