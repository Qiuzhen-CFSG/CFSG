module
public import Theory.Representation.BinaryPermutation.SynthemeCoreChief
public import Theory.Representation.BinaryPermutation.SixCoreOrbits

/-!+# Weight-two orbits of the tetrahedral six-edge action

Every pair of edges has two translates under A₄ that, together with the
original pair, partition all six edges. Thus the sum of these three
weight-two words is the constant word. In particular every invariant
additive subgroup containing a weight-two word contains the fixed line.

The certificate checks the 64 binary words and twelve tetrahedral actors;
it does not enumerate subspaces or ambient groups. The original L₂-action
application is in Chapter13 Section04 FixedCoreSource/Nonsolvable.
Source: Aschbacher–Smith 13.4.10(8i), printed pp.909–910.
-/

public section
open Subgroup
namespace BinaryPermutation.SynthemeCoreChief
open Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition
local instance : Fintype (Equiv.Perm (Fin 4)) := fintypePerm
local instance : Fintype A := Subtype.fintype _

private theorem weight_two_test : ∀ w : Fin 6 → ZMod 2,
    wordWeight w = 2 → ∃ a b : A,
      w + (fun i => w ((synthemeHom a).symm i)) +
        (fun i => w ((synthemeHom b).symm i)) = fun _ => 1 := by
  decide +kernel

/-- The constant word is a sum of three words in any weight-two orbit
of the literal tetrahedral residual. -/
theorem weight_two_constant_sum (w : core (Fin 6)) (hw : wordWeight w.val = 2) :
    ∃ a b : A, w + coreRepresentation (Fin 6) (synthemeHom a) w +
      coreRepresentation (Fin 6) (synthemeHom b) w = sixCoreConstant := by
  obtain ⟨a,b,hab⟩ := weight_two_test w.val hw
  exact ⟨a,b,Subtype.ext hab⟩

end BinaryPermutation.SynthemeCoreChief
