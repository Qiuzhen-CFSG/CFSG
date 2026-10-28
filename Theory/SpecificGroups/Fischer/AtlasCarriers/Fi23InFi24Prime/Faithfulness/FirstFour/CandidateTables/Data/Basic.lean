module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.GeneratorData

/-!
# Full-ambient staged candidate witnesses

The entries are obtained from the literal `WordEvaluation` lists using the
inverse-left ATLAS action, on all 306936 ambient labels. These are numerical
witnesses only: no word equality, inverse law, or composition is assumed.
The candidate powers use the addition chains 1,2,3,5,10,15,30 and 1,2,3,6.
`CandidateTables.Reduction` proves how the checked short comparisons assemble.

Reproduce with `CandidateTables/source/generate.py`. Source: the retained
ATLAS F24G1-p306936B0 tables, GLS3 Table 5.3v, and `WordSetup`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.CandidateTables
open Certificate

/-- A total packed witness on the entire ambient set. -/
def ambientMap (t : Ambient.PackedBlocks) (i : Fin 306936) : Fin 306936 :=
  ⟨lookup t.get 19 i.val % 306936, Nat.mod_lt _ (by decide)⟩

end Sporadic.Fischer.Fi24Prime.Fi23Lift.CandidateTables
