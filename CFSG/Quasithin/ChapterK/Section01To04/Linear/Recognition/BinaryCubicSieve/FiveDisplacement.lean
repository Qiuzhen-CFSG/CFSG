module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Branches
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Actors
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph

/-!
# Assembling the inner and graph estimates for binary SL₅

An elementary actor in the full linear normalizer either lies in the action
image or contains a graph actor. In the first case, pullback to the actual SL₅
group preserves the cubic identity, rank and common fixed-space codimension.
In the second case the normalizer geometry improves the rank bound to five.
Thus the two independent estimates suffice for the original multiple-support
contract, without discarding any outer actors. The inner producer excludes all
eleven multiple supports by the end-node sieve and endpoint adjoint estimate;
the graph producer handles the endpoint and higher supports separately.

The unconditional theorem `multiple_support_displacement` discharges both
estimates under finite dimension, faithfulness and irreducibility. The source
degree applications live separately in `FiveDisplacement.Source`, so the core
can be imported by the binary sieve without a cycle.
Source: GM04, author manuscript Propositions 4.7 and 4.8; Aschbacher–Smith
K.3.2, printed pp.454–455 (PDF pp.465–466).
-/

public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement

open Representation Representation.BinaryOffender

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) SL5TenDimensional.Group V)

/-- The precise two-branch reduction, including the actual SL₅ pullback and
the improved graph-actor rank bound, with the estimates explicit. -/
theorem multiple_support_displacement_of_inner_and_graph
    (hf : Function.Injective σ) (hi : IsIrreducible σ)
    (hinner : InnerEstimate σ) (hgraph : GraphEstimate σ) :
    FiveMultipleSupportDisplacement σ := by
  intro J v hv hJ hcard A hA hc hr
  by_cases hin : A ≤ (actionImage σ).subgroupOf (linearNormalizer σ)
  · obtain ⟨B, hB, hBc, hrB, hdB, _⟩ := inner_actor_pullback σ hf A hA hin hc
    rw [← hrB, ← hdB]
    exact hinner J v hv hJ hcard B hB hBc (hrB.trans_le hr)
  · exact hgraph J v hv hJ hcard A hA hc hin (outer_rank_le_five σ hf hi A hA hin)

/-- Every multiple-root highest support of a faithful irreducible binary SL₅
module has common fixed codimension greater than twice the rank of every
nontrivial elementary cubic actor of rank at most six in the full linear
normalizer. Both the inner and graph estimates are discharged. -/
theorem multiple_support_displacement [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective σ) (hi : IsIrreducible σ) :
    FiveMultipleSupportDisplacement σ :=
  multiple_support_displacement_of_inner_and_graph σ hf hi
    (Inner.inner_estimate σ hf hi) (Graph.graph_estimate σ hf hi)

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement
