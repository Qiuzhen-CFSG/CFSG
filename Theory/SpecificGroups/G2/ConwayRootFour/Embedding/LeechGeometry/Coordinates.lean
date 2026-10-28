module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LocalGeometry
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.ScalarFour

/-!
# Concrete coordinate obligations for the local Leech groups

This is a construction contract in the literal Leech lattice modulo two.
The coordinates must map onto C_(Λ/2Λ)(U) for the actual scalar four-group,
and every local generator must centralize the specified tetrahedral I.
Their coordinate equations use the fixed octonion matrices. The short-root
marking remains conjugacy to the prescribed element in the full quotient.

There is no action of the generated group and no faithfulness field here.
`LeechGeometry.LocalCoordinates.representation` constructs that action by
closure induction; `CentralizerFaithful` supplies its injectivity separately.
No inhabitant of this contract is asserted here.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284;
Aschbacher–Smith I.2.2(5), printed p.411/PDF422.
-/

@[expose] public noncomputable section

open Matrix Atlas.Conway Atlas.Codes Atlas.Lattices
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry
open OctonionLocals

/-- Local generators with coordinates in the actual Leech quotient. No faithful
representation or homomorphism from G₂ is included in this data. -/
structure LocalCoordinates where
  long : SL(3,F) →* LeechCentralQuotient
  short : F → LeechCentralQuotient
  swap : LeechCentralQuotient
  long_mem : ∀ A, long A ∈ centralizerI
  short_mem : ∀ a, short a ∈ centralizerI
  swap_mem : swap ∈ centralizerI
  coordinates : Six F →+ LeechModTwo
  coordinates_injective : Function.Injective coordinates
  coordinates_range : ∀ v, v ∈ fixedSpace ↔ ∃ w, coordinates w = v
  on_generators : ∀ (i : Generator F) (v : Six F),
    quotientModTwoRepresentation (localGenerator long short swap i) (coordinates v) =
      coordinates (action (generator i) v)
  marked : IsConj (short 1) markedInvolution

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry
