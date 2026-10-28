module
public import Theory.Representation.BinaryPermutation.CoreFixedLine
public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.Canonical

/-!
# Cubic fixed vectors in the tetrahedral six-edge core

The even syntheme parabolic has the literal tetrahedral A₄ edge action
as its two-residual. Every nonidentity cubic in this action has two
three-cycles on the six coordinates. In the binary augmentation core,
the sum-zero condition forces their two fixed coordinate values to agree.
Thus its fixed vectors are exactly the constant line.

This is the model calculation for the two noncentral binary chief factors
on V in Aschbacher–Smith 13.4.9, printed p.906. The source transport uses
the actual five-dimensional core and the original component quotient.
The finite certificate ranges over twelve permutations and sixty-four
binary words; all reduction is checked by the Lean kernel.
-/

public noncomputable section
open Subgroup
namespace BinaryPermutation.SynthemeCoreChief
open Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition
abbrev W := core (Fin 6)
local instance : Fintype (Equiv.Perm (Fin 4)) := fintypePerm
local instance : Fintype A := Subtype.fintype _
private theorem cubic_fixed_test : ∀ (a : A) (w : Fin 6 → ZMod 2),
    (a ^ 3 = 1 ∧ a ≠ 1 ∧ (∑ i, w i) = 0 ∧
      (fun i => w ((synthemeHom a).symm i)) = w) → w = fun _ => w 0 := by
  decide +kernel

theorem cubic_fixed_iff (a : A) (ha : orderOf a = 3) (w : W) :
    coreRepresentation (Fin 6) (synthemeHom a) w = w ↔
      w.val ∈ constants (Fin 6) := by
  constructor
  · intro hw
    apply (mem_constants_iff w.val).mpr
    refine ⟨w.val 0,fun i => congrFun (cubic_fixed_test a w.val
      ⟨ha ▸ pow_orderOf_eq_one a, (fun he => by simp [he] at ha),w.property,?_⟩) i⟩
    exact congrArg Subtype.val hw
  · intro hw
    obtain ⟨c,hc⟩ := (mem_constants_iff w.val).mp hw
    apply Subtype.ext
    funext i
    exact (hc _).trans (hc i).symm
end BinaryPermutation.SynthemeCoreChief

namespace BinaryPermutation.SynthemeCoreChief
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition
local instance : Fintype (Equiv.Perm (Fin 4)) := fintypePerm
local instance : Fintype A := Subtype.fintype _

/-- The even syntheme parabolic has the same literal tetrahedral residual. -/
theorem even_syntheme_residual :
    (pResidual 2 (synthemeStabilizer ⊓ alternatingGroup (Fin 6) : Subgroup S6)).map
      (synthemeStabilizer ⊓ alternatingGroup (Fin 6)).subtype = synthemeHom.range := by
  apply residual_range
  · rintro g ⟨a,rfl⟩
    refine ⟨synthemeHom_le ⟨a,rfl⟩,?_⟩
    exact (show ∀ a : A, synthemeHom a ∈ alternatingGroup (Fin 6) by
      change ∀ a : A, (synthemeHom a).sign = 1
      decide +kernel) a
  · intro g
    exact syntheme_square ⟨g.val,g.property.1⟩
end BinaryPermutation.SynthemeCoreChief

