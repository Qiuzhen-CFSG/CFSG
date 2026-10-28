module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J2.Placement.Coverage.Ordering

/-!
# Checking every coset key by a linear pass through the witness tables

Each pair consists of a subgroup-word/representative parameter and its claimed
binary image code. A kernel check validates the paired lists in one traversal,
so the computation does not repeatedly index the large tables. `Transversal`
uses list membership to recover the equality for every index.

Source: the fixed ATLAS witnesses documented in `source/README.md`;
Aschbacher–Smith, printed p.511, and GLS3 Table 5.3g.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement.CoverageCertificate

def parameterMap (p : Nat) (x : Fin 100) : Fin 100 :=
  subgroupMap ⟨p % 128, Nat.mod_lt _ (by decide)⟩
    (representativeMap ⟨p / 128 % 72, Nat.mod_lt _ (by decide)⟩ x)

def entryValid (e : Nat × Nat) : Bool := decide (explicitKey (parameterMap e.1) = e.2)

set_option maxRecDepth 1000000 in
theorem parameterTable_size : transversalParams.size = 4725 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem entries_valid :
    (transversalParams.toList.zip keyTable.toList).all entryValid = true := by
  decide +kernel


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement.CoverageCertificate
