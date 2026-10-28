module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.Perfectness
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.NormalGeneration
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.CharacterLattice
public import Theory.AlgebraicGroup.Semisimple.Versions

/-!
# Simplicity and universality inputs for the concrete Spin D4 carrier

The point group is perfect, and each nonidentity pinned root element normally
generates it. The actual fundamental characters give the full integral
character lattice; twice every character lies in the simple-root span.
The regular simple-coroot torus isomorphism remains available from the pinning.

The theorem below assembles algebraic simplicity from an explicit root
extraction hypothesis. Producing that hypothesis, and proving the incoming
isogeny comparison for universality, are still separate geometric obligations.
No unconditional simplicity or universality claim is made in this module yet.

Source: GLS3, Sections 1.10-1.12, especially 1.10.1 and 1.12.5(b),
`refs/KGroup/GLS3/Chapter1.tex`.
-/

public section
namespace Triality.SimplyConnected
open Theory.AlgebraicGroup
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- Root extraction is the remaining geometric input for algebraic simplicity.
The conclusion follows from connectedness, the concrete commutator calculation,
and normal generation by each nonidentity root element. -/
theorem isSimple_of_normal_root_extraction
    (extract : ∀ N : ClosedSubgroup (groupVariety k),
      N.toSubgroup.Normal → Variety.dimension N.carrierVariety ≠ 0 →
        ∃ (r : Pinning.RootIndex) (a : k),
          a ≠ 0 ∧ Pinning.rootPoint k r a ∈ N.toSubgroup) :
    IsSimpleAlgebraicGroup (groupVariety k) := by
  refine ⟨isConnected k, derived_ne_bot k, ?_⟩
  intro N hN hproper
  by_contra hdim
  obtain ⟨r, a, ha, hx⟩ := extract N hN hdim
  exact hproper (normal_eq_top_of_rootPoint_mem k N.toSubgroup hN r a ha hx)

end Triality.SimplyConnected
