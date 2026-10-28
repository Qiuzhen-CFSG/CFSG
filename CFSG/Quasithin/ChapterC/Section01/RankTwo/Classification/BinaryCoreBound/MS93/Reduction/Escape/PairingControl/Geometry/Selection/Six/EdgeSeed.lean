module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six.EdgeSeed.Native
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six.EdgeSeed.SmallCommutator

/-!+# Edge seeds from the remaining native-incidence input

The marked flags, zero natural fixed subgroup, native containment and small
commutator are constructed from a genuine nonzero native intersection.
The commutator estimate is proved uniformly at all incident edges, so no
additional displacement or pairing premise is needed in this assembly.

For the six-step contained branch the only remaining input is native
incidence at the actual predecessor c. Its independent source producer is
still required: the conditional theorem below is not a completed proof of
the source branch, nor an unconditional EdgeSeedAt producer.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(3)--(5), pp.883--885.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.EdgeSeed
open TerminalPairing Centralizer.Generation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : MS93.Geometry R}

/-- Construct every field of the geometric seed from native incidence.
The incidence producer remains a separate source obligation. -/
theorem nonempty_at_edge_of_incidence (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t)
    (incidence : NativeIncidence a) : Nonempty (EdgeSeedAt source a t ha) := by
  obtain ⟨o⟩ := facts.opposite a ha
  exact nonempty_of_native_intersection source hb ha hat o
    (native_intersection_at_edge hat incidence)
    (native_intersection_commutator_card source hb modules initial facts p bad ha hat)

/-- Specialization to the actual selected predecessor. The tree geodesic
supplies adjacency without any assumption that the critical distance exceeds six. -/
theorem nonempty_at_choice_of_incidence (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (choice : CentralizerChoice p) (incidence : NativeIncidence p.c) :
    Nonempty (EdgeSeedAt source p.c choice.t p.before_color) := by
  apply nonempty_at_edge_of_incidence source hb modules initial facts p bad p.before_color
    (adjacent_symm R (choice.before.adjacent (geometry := geometry) p.before)) incidence

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.EdgeSeed
