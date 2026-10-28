module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.Basic

/-!
# The terminal subgroup in the propagation argument

Under failed prescribed-span escape, the source defines R₀ as the commutator
of the transported P-orbit span with the terminal Z-layer. Its first local
calculation places the same subgroup in D_(a'-2) and identifies it with the
edge commutators at a' and a'-4. It also proves that R₀ is not contained in
Z_a. These are intermediate targets, with no constructor asserted here.

The remaining induction propagates this subgroup backward in steps of four.
Its assembly owner must both construct the terminal seed and prove the
contradiction from it; the record is not a proof of (4.4.4).

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), proof of (4.4.4), printed p.894.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation
variable {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}

/-- The actual R₀ used when the prescribed P-orbit span fails to escape. -/
noncomputable def failedSpanCommutator {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (g : FreeAmalgam R) : Subgroup (FreeAmalgam R) :=
  ⁅(prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom, Z R a'⁆

/-- The four assertions at the beginning of the source's backward propagation.
The subgroup is retained literally, with all endpoint indices explicit. -/
structure TerminalPropagationSeed {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (K : Subgroup (FreeAmalgam R)) : Prop where
  not_le_start_Z : ¬ K ≤ Z R a
  terminal_edge : K = edgeCommutator R a' (p.walk.getVert (p.walk.length - 1))
  penultimate_fixed : K ≤ fixedCore R (p.walk.getVert (p.walk.length - 2))
  preceding_edge : K = edgeCommutator R (p.walk.getVert (p.walk.length - 4))
    (p.walk.getVert (p.walk.length - 3))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation
