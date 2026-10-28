module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.SourceUniversality
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.Source

/-!
# Unconditional universality of the actual Spin D4 carrier

The proved semisimple-center theorem supplies the sole earlier geometric input
of the incoming-isogeny argument. This is the literal carrier used by the
triality finite modules and tensors. Source: GLS3 1.12.5(b); Borel 13.17.
-/

public section
namespace Triality.SimplyConnected
open Theory.AlgebraicGroup
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

theorem source_universal : IsUniversalVersion (groupVariety k) :=
  source_universal_of_semisimple_centers k (fun _ _ hH _ hT =>
    SemisimpleCenterContainment.center_le_maximalTorus_of_semisimple hH hT)

end Triality.SimplyConnected
