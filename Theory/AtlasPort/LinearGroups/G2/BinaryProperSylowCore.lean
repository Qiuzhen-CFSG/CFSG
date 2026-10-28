module

public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Theory.AtlasPort.LinearGroups.G2.BinaryNinePointReduction
public import Theory.AtlasPort.LinearGroups.G2.BinarySylowCoreReduction
public import Theory.SpecificGroups.Alternating.NineCyclicFourSquare

/-!
# Nontrivial two-cores in proper Sylow overgroups of G₂(2)′

The literal commutator subgroup of the binary octonion automorphism group
has order 6048 and Sylow two-subgroups of order 32. The numerical reduction
leaves only index nine. Simplicity and perfectness make an index-nine coset
action faithful and even, contradicting the actual embedded C₄ × C₄ and
the nonembedding theorem for A₉. Thus every proper Sylow two-overgroup has
a nontrivial intrinsic two-core, without additional model hypotheses.

Source/application: Aschbacher--Smith, proof of B.1.13, printed p.74
(PDF p.85), and GLS III, §2.6, with the small-derived convention of §2.2.
The concrete carrier and parabolic embedding use the licensed ATLAS port;
see LICENSES/ATLAS.txt.
-/

public section

namespace Atlas.G2.BinaryProperSylowCore
open Subgroup

/-- The actual binary derived group has no subgroup of index nine. -/
theorem index_ne_nine (H : Subgroup (commutator (Model (ZMod 2)))) :
    H.index ≠ 9 := by
  let : IsSimpleGroup (commutator (Model (ZMod 2))) := isSimple_commutator_binary
  let : Group.IsPerfect (commutator (Model (ZMod 2))) := by
    rw [BinaryParabolicPair.commutator_eq_longRootClosure]
    exact BinaryException.H_isPerfect
  exact BinaryNinePointReduction.index_ne_nine_of_cyclicFourSquare_obstruction
    Theory.SpecificGroups.Alternating.NineCyclicFourSquare.not_injective H

/-- Every proper overgroup of a Sylow two-subgroup of the literal G₂(2)′
has nontrivial two-core. -/
theorem twoCore_ne_bot
    (Q : Sylow 2 (commutator (Model (ZMod 2))))
    (H : Subgroup (commutator (Model (ZMod 2)))) (hH : H ≠ ⊤)
    (hQH : (Q : Subgroup (commutator (Model (ZMod 2)))) ≤ H) :
    pCore 2 H ≠ ⊥ := by
  let : IsSimpleGroup (commutator (Model (ZMod 2))) := isSimple_commutator_binary
  exact BinarySylowCoreReduction.twoCore_ne_bot_of_index_ne_nine Q H hH hQH
    (index_ne_nine H)

end Atlas.G2.BinaryProperSylowCore
