module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.ExceptionalBranch.LocalSubgroups
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.ExceptionalBranch.SylowKernel.Reduction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.ExceptionalBranch.SylowKernel.BorelBlocks

/-!
# The exceptional Sylow branch: corank one

In the non-Borel branch the actual intersection L ∩ M equals L ∩ Q.
`BorelBlocks` constructs an A₃ block containing the Borel, using the complete
E.6.7 input and the full Q-orbit even when Q permutes components. `Reduction`
identifies the Borel and component action kernels. E.6.7(2) therefore bounds
the component action corank by one, and escape from M gives positivity.

Only the universal source E.6.7 input remains explicit in this corank result;
no block-placement premise remains. Identifying the original U with C_V(L)
is a separate obligation, so this does not yet assert the full Sylow branch.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch.SylowKernel

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

open InvariantSubspaces.BlockSelection

/-- The non-Borel PSL₂(4) component has action corank one. The concrete
E.6.7 overgroup and its Borel block are constructed from the local subgroup
equality; Q need not normalize L. -/
theorem actionCorank_one
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (input : E67Input T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : ClassicalGroup.IsPSL L 2 4)
    (hLM : L ⊓ M = L ⊓ sylowCentralizer (T : Subgroup G) V) :
    actionCorank V L = 1 := by
  obtain ⟨S, hS⟩ := component_sylow_intersection h hU hL
  obtain ⟨w⟩ := BorelBlocks.nonempty_borelBlockWitness h input hU hL hm hLM S hS
  exact corank_one_of_borelBlockWitness h earlier hU hL hm S hS w

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch.SylowKernel
