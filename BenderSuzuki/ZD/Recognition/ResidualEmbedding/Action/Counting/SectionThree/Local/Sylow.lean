module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionThree.Local
public import Theory.GroupAction.ZStarInvariantSylow.Centralizer

/-!
# The complete local input for distinguished Section 3 counting

A distinguished involution swapping two points acts trivially modulo the
relative odd core of every invariant subgroup of their common stabilizer.
The Z-star argument in `Local` proves this commutator containment. Applying
the invariant Sylow extension and centralizer-Sylow theorems then constructs
both Sylows required in SectionThreeLocal, using the original subgroup maps.
The common stabilizer is allowed to have even order.

Source: GLS, Volume 4, Chapter 2, Propositions 3.5 and 3.7(a,b), pp.29–30.
-/

namespace BenderSuzuki.ZD

open Theory.GroupTheory PFAppendixIII
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Product disconnection supplies the entire local Section 3 input,
including invariant Sylows in possibly even two-point stabilizers. -/
public theorem sectionThreeLocal_of_productDisconnected (h : IsProductDisconnected Z M) :
    SectionThreeLocal Z M := by
  refine ⟨fun t ht beta hb W hW hn =>
    sectionThree_swapping_core h ht beta hb W hW hn, ?_⟩
  intro t ht beta hb p hp hpodd W P hW htW hP hPW htP
  have hcore := sectionThree_swapping_core h ht beta hb W hW htW
  obtain ⟨Q, hPQ, htQ⟩ := ZStarInvariantSylow.exists_invariant_sylow_containing
    (h.involutions t ht) htW hcore hp hpodd hP hPW htP
  obtain ⟨R, hRQ⟩ := ZStarInvariantSylow.exists_centralizer_sylow_le
    (h.involutions t ht) htW hcore hp hpodd Q htQ
  exact ⟨(Q : Subgroup W).map W.subtype, ⟨Q, rfl⟩, hPQ, htQ,
    (R : Subgroup (W ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G)).map
      (W ⊓ Subgroup.centralizer ({t} : Set G)).subtype,
    ⟨R, rfl⟩, hRQ⟩

/-- The local Section 3 input at the minimal-counterexample boundary. -/
public theorem sectionThreeLocal_of_minimalCounterexample
    (h : MinimalCounterexample Z M) (_hs : SimpleReduction Z M) :
    SectionThreeLocal Z M :=
  sectionThreeLocal_of_productDisconnected h.disconnected

end BenderSuzuki.ZD
