module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi24Centralizer.PackedSource.Checks
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.GeneratorAgreement
public import Theory.GroupAction.PackedPermutation.Chunks
/-!
# Packed tables agree with the literal Fi24 generators

The block certificates are converted to pointwise equations and then composed
with the existing source-cycle interpretation. Thus the new packed tables
refer to the original Fi24 carrier, not an alternate permutation model.
The last modulo is the same one in the original certified lookup maps; the
network comparison later removes it using bijectivity and fixed padding.
-/
public section
namespace Sporadic.Fischer.Fi24Prime.CentralizerSection.PackedSource
open Fi23Lift.Certificate Fi23Lift.Certificate.Ambient
open Theory.GroupAction.PackedPermutation

theorem packedA_lt : packedA < 2^(19*306936) := by decide +kernel
theorem packedB_lt : packedB < 2^(19*306936) := by decide +kernel

theorem packedA_generator (i : Fin 306936) :
    ((packedA >>> (19*i.val)) % 2^19) % 306936 = (generatorA i).val := by
  have h := field_eq_of_chunks packedA 19 306936 aBlocks
    (fun b hb => packedA_block b hb) i.isLt
  have H : ((packedA >>> (19*i.val)) % 2^19) % 306936 = (aMap i).val :=
    congrArg (fun x : Nat => x % 306936) h
  simpa only [aMap_correct] using H

theorem packedB_generator (i : Fin 306936) :
    ((packedB >>> (19*i.val)) % 2^19) % 306936 = (generatorB i).val := by
  have h := field_eq_of_chunks packedB 19 306936 bBlocks
    (fun b hb => packedB_block b hb) i.isLt
  have H : ((packedB >>> (19*i.val)) % 2^19) % 306936 = (bMap i).val :=
    congrArg (fun x : Nat => x % 306936) h
  simpa only [bMap_correct] using H

end Sporadic.Fischer.Fi24Prime.CentralizerSection.PackedSource
