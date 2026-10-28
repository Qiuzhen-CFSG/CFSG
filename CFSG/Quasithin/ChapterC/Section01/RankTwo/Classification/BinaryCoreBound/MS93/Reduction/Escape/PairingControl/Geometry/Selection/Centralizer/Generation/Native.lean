module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.Native.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.Native.Incidence

/-!
# Assembly of native dual lifts from one geometric intersection

An actual neighbor whose radius group meets Vcirc beyond U supplies a
nonzero dual lift. Its annihilator follows from edge fixation and the
common natural/dual marking. Conjugation then realizes all seven nonzero
vectors. The natural section at the predecessor is supplied by translating
the entire initial configuration.

The existence of this geometric intersection remains an explicit premise;
this module does not claim the source-only native realization or the local
generation display. Source: Meierfrankenfeld--Stellmacher (1993), immediately
before (4.3.2)(4), printed p.884.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : MS93.Geometry R}

/-- Uniform native realization entails the genuine nonzero intersection. -/
theorem nativeIncidence_of_lifts {c : Vertex R} (o : OppositeSectionAt c)
    (hC : Vcirc R c ≤ stabilizer R c) (lifts : NativeNeighborLifts o hC) :
    NativeIncidence c := by
  let v : Space := Multiplicative.ofAdd (Pi.single 0 (1 : ZMod 2))
  have hv : v ≠ 1 := by
    intro h
    have hh := congrArg (fun w : Space => w.toAdd 0) h
    simp [v] at hh
  obtain ⟨lift⟩ := lifts v hv
  refine ⟨lift.neighbor, lift.adjacent, ?_⟩
  intro h
  have hx : (lift.vector : FreeAmalgam R) ∈ U R c :=
    h ⟨lift.vector.property, lift.in_neighbor⟩
  have hk : lift.vector ∈ (movingCoordinates o hC).ker := by
    rw [movingCoordinates_kernel]
    exact hx
  exact hv (lift.coordinates.symm.trans (MonoidHom.mem_ker.mp hk))

variable [Finite M]

/-- The remaining geometric intersection suffices; annihilator incidence
and uniformity introduce no further source assumptions. -/
theorem nativeNeighborLifts_of_incidence (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (o : OppositeSectionAt p.c) (hC : Vcirc R p.c ≤ stabilizer R p.c)
    (incidence : NativeIncidence p.c) : NativeNeighborLifts o hC := by
  obtain ⟨q, hq⟩ := Initial.Consequences.counterexample_at_start p p.c p.before_color
  obtain ⟨iq⟩ := initial q
  have s : NaturalSectionAt p.c (V R p.c) (Z R p.c) := by
    simpa only [hq] using iq.natural_section
  obtain ⟨v, hv, ⟨lift⟩⟩ := exists_native_lift_of_incidence source hb modules facts
    p.before_color s o hC incidence
  exact nativeNeighborLifts_of_one o hC hv lift

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation
