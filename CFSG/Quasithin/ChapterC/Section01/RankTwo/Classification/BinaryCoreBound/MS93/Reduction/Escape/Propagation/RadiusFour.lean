module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Stages
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Ball
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Forward
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Kernel

/-!
# The radius-four conclusions and exact orbit witnesses of MS93 (4.3.8)

Centrality fixes the radius commutator under the two actual local
conjugators. The order-four central planes identify both edge displacements
and both natural-layer intersections. Reversing a selected critical pair
proves radius-four commutation, and the local product argument proves the
kernel join and nonmovement of the first conjugate. Characteristic
faithfulness excludes the normal radius-three span that containment would
force; the final xi-conjugate argument gives the intersection bound.

The final theorem constructs ForwardFacts and KernelBounds from the stated
preceding stages and assembles RadiusFourFacts. It retains the exact orbit
witnesses required by the later escape argument. RigidityFacts and
BackwardFacts remain explicit preceding inputs; normalization transfer is
not needed for this step. The earlier conditional assembly is preserved.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.8), printed pp.888--889.
The final contradiction for (4.3) is outside this module.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

/-- Supply the later nonmoving conclusion to the already constructed exact
orbit data. This conversion is not a proof of nonmovement. -/
def CentralOrbitWitnesses.toPropagationWitnesses
    {p : Counterexample geometry} {d t₃ t₅ : Vertex R}
    (w : CentralOrbitWitnesses p d t₃ t₅) (hn : w.mu ∉ movingNeighbors geometry d) :
    PropagationWitnesses p d t₃ t₅ where
  mu := w.mu
  lam := w.lam
  first_conjugator := w.first_conjugator
  second_conjugator := w.second_conjugator
  first_local := w.first_local
  second_local := w.second_local
  first_image := w.first_image
  second_image := w.second_image
  first_adjacent := w.first_adjacent
  second_adjacent := w.second_adjacent
  first_not_moving := hn
  first_displacement := w.first_displacement
  second_displacement := w.second_displacement
  first_intersection := w.first_intersection
  second_intersection := w.second_intersection

/-- Conditional final assembly. The source-theorem owner must still construct
ForwardFacts and KernelBounds from the stated preceding stages. -/
theorem radiusFourFacts_of_stages [Finite M] (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (control : ∀ p : Counterexample geometry, LocalControl p) (edge : EdgeTransfer geometry)
    (backward : BackwardFacts geometry) (forward : ForwardFacts geometry)
    (bounds : KernelBounds geometry) : RadiusFourFacts geometry where
  radius_central_at_two := radius_central_at_two source hb control edge
  witnesses := by
    intro p d t₃ t₅ hd h₃ h₅
    obtain ⟨w⟩ := central_orbit_witnesses source hb modules initial control edge backward
      p d t₃ t₅ hd h₃ h₅
    exact ⟨w.toPropagationWitnesses (forward.nonmoving p d t₃ t₅ hd h₃ h₅ w)⟩
  radius_four := by
    intro p d hd
    exact ⟨bounds.not_le p d hd, bounds.intersection_le p d hd,
      forward.radius_join p d hd⟩

/-- MS93 (4.3.8) from the preceding source stages: centrality at the second
predecessor, both actual local conjugators with all four exact identities
and nonmovement, and the three literal radius-four conclusions. The forward
and kernel-bound stages are constructed here, without additional premises. -/
theorem radiusFourFacts [Finite M] (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (control : ∀ p : Counterexample geometry, LocalControl p) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry) (backward : BackwardFacts geometry) :
    RadiusFourFacts geometry := by
  have forward := Forward.forwardFacts source hb modules initial control edge rigidity backward
  have bounds := kernelBounds source hb modules initial control edge rigidity backward forward
  exact radiusFourFacts_of_stages source hb modules initial control edge backward forward bounds

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour
