module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi24Centralizer.Networks.A
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi24Centralizer.Networks.B
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi24Centralizer.PackedSource
public import Theory.GroupAction.PackedPermutation.Padding
/-!
# Source comparison for the certified Fi24 generator networks

The final packed tables agree with the original generator blocks below the
source degree and with the identity above it. Bijectivity then identifies the
original segment exactly; no alternate group carrier or action is introduced.
-/
@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.CentralizerSection.Networks
open Theory.GroupAction.PackedPermutation
open PackedSource

noncomputable def permA : Equiv.Perm (Fin 524288) :=
  permutation 19 524288 networkA networkA_valid
noncomputable def permB : Equiv.Perm (Fin 524288) :=
  permutation 19 524288 networkB networkB_valid

private theorem ramp_fields (i : Fin 524288) : get 19 (ramp 19 524288) i = i.val :=
  get_ramp (by decide) (by decide) i.isLt

theorem runA : run 19 networkA (ramp 19 524288) = padded 19 306936 524288 packedA := by
  decide +kernel

theorem runB : run 19 networkB (ramp 19 524288) = padded 19 306936 524288 packedB := by
  decide +kernel

theorem permA_source (i : Fin 306936) :
    permA (Fin.castLE (by decide) i) = Fin.castLE (by decide) (generatorA i) := by
  apply source_intertwining_of_padded_table (by decide) (by decide) (by decide)
    packedA_lt permA generatorA _ packedA_generator i
  intro j
  rw [← runA]
  exact get_run_identity 19 524288 _ networkA networkA_valid ramp_fields j

theorem permB_source (i : Fin 306936) :
    permB (Fin.castLE (by decide) i) = Fin.castLE (by decide) (generatorB i) := by
  apply source_intertwining_of_padded_table (by decide) (by decide) (by decide)
    packedB_lt permB generatorB _ packedB_generator i
  intro j
  rw [← runB]
  exact get_run_identity 19 524288 _ networkB networkB_valid ramp_fields j
end Sporadic.Fischer.Fi24Prime.CentralizerSection.Networks
