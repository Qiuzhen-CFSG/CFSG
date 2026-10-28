module

public import Theory.Representation.BinaryAlternatingNaturalCohomology
public import Theory.Representation.BinaryOffender.Defs

/-!
# Detecting augmentation-core cocycles on a subgroup

Every cocycle of the binary alternating augmentation core becomes principal
in the full permutation module. If the full fixed space of a subgroup P
has augmentation zero, a cocycle vanishing on P is therefore principal
already in the core, with its principal vector fixed by P.

This replaces the full-Sylow splitting argument when a point stabilizer is
available instead. The fixed-space premise concerns the full permutation
module, and must be proved for the particular point subgroup. In degree
eight it holds when the coordinate orbits all have even length.
Source application: Aschbacher--Smith 12.2.16, printed p.800, in place of
the application of B.2.13 (printed p.78).
-/

public section
open Representation Representation.OneCohomology Representation.BinaryOffender
namespace BinaryPermutation
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Vanishing on a subgroup whose full fixed vectors have even augmentation
detects the cohomology class of an augmentation-core cocycle. -/
theorem core_cocycle_principal_of_fixed_le_core
    (hcard : 3 ≤ Nat.card Ω) (P : Subgroup (alternatingGroup Ω))
    (hP : fixedSpace (alternatingRepresentation Ω) P ≤ core Ω)
    (f : cocycles (alternatingCoreRepresentation Ω))
    (hf : ∀ p ∈ P, f.val p = 0) :
    ∃ w : core Ω, w ∈ fixedSpace (alternatingCoreRepresentation Ω) P ∧
      principal (alternatingCoreRepresentation Ω) w = f := by
  let F : cocycles (alternatingRepresentation Ω) :=
    ⟨fun g => (f.val g : Full Ω), fun g h => congrArg Subtype.val (f.property g h)⟩
  obtain ⟨w, hw⟩ := alternating_principal_surjective Ω hcard F
  have hwp : w ∈ fixedSpace (alternatingRepresentation Ω) P := by
    intro p
    have he := congrArg (fun c : cocycles (alternatingRepresentation Ω) => c.val p.val) hw
    change alternatingRepresentation Ω p.val w - w = (f.val p.val).val at he
    rw [hf p.val p.property] at he
    exact sub_eq_zero.mp he
  refine ⟨⟨w, hP hwp⟩, ?_, ?_⟩
  · intro p
    exact Subtype.ext (hwp p)
  · apply Subtype.ext
    funext g
    apply Subtype.ext
    exact congrArg (fun c : cocycles (alternatingRepresentation Ω) => c.val g) hw

end BinaryPermutation
