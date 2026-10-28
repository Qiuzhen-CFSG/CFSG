module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Rigidity.Moving
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Rigidity.Equality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Rigidity.LocalAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Rigidity.Distance
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Stages

/-!
# Neighboring Z-layer rigidity and the strict distance bound

The noncentral intersection excludes movement. The actual local residual
then normalizes the neighboring displacement; its natural action identifies
that displacement with the original one. This implies equality of the full
Z-layers and uniqueness among moving neighbors. Their existence follows
from the preceding bound on H.

If b = 6, an actual local conjugate of the critical endpoint has the same
Z-layer as the vertex two steps from the start. The critical commutator
would then lie in both its natural group and its disjoint fixed core.
The final assembly discharges the displacement and distance premises using
only the preceding module, initial, local-control and edge-transfer inputs.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.4)--(4.3.5), printed p.886.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Rigidity
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Conditional assembly retaining both remaining mathematical obligations. -/
theorem rigidityFacts_of_displacement_and_bound
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (displacement : ∀ _p : Counterexample geometry, ∀ a t d,
      color R a = false → Adjacent R a t → Adjacent R d t →
      Z R d ≤ B R a (geometry.Z_normal a) →
      ¬ edgeDisplacement d t ≤ localCenter a →
      edgeDisplacement d t = edgeDisplacement a t)
    (bound : ∀ _p : Counterexample geometry, 6 < geometry.b R) :
    RigidityFacts geometry := by
  have equal_Z : ∀ p : Counterexample geometry, ∀ t, Before p.a' p.a t 1 →
      ∀ d e, Adjacent R d t → Adjacent R e t →
        ¬ U R d ⊓ Z R e ≤ localCenter e → Z R d = Z R e := by
    intro p t ht d e hdt het hn
    exact equal_Z_of_nonmoving_displacement hb modules p initial control edge (displacement p)
      e t d (neighbor_color p.color_a ht.endpoint_adjacent het) het hdt hn
  exact ⟨equal_Z, moving_Z_unique_of_equal_Z hb modules initial control equal_Z, bound⟩

/-- MS93 (4.3.4) at every oriented edge, with the literal noncentral
intersection in the center of the whole local stabilizer. -/
theorem neighboring_Z_eq
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R) (p : Counterexample geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (a t d : Vertex R) (ha : color R a = false) (hat : Adjacent R a t)
    (hdt : Adjacent R d t) (hn : ¬ U R d ⊓ Z R a ≤ localCenter a) :
    Z R d = Z R a := by
  exact equal_Z_of_nonmoving_displacement hb modules p initial control edge
    (nonmoving_displacement_eq hb modules transfer p initial control edge) a t d ha hat hdt hn

/-- MS93 (4.3.5), with neighboring rigidity proved from the preceding stages. -/
theorem six_lt
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R) (p : Counterexample geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry) :
    6 < geometry.b R := by
  exact six_lt_of_equal_Z hb modules transfer p initial control edge
    (neighboring_Z_eq hb modules transfer p initial control edge)

/-- All clauses of MS93 (4.3.4)--(4.3.5), including existence and uniqueness
of the moving-neighbor Z-layer over the specified edge. -/
theorem rigidityFacts
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry) :
    RigidityFacts geometry := by
  exact rigidityFacts_of_displacement_and_bound hb modules initial control edge
    (fun p => nonmoving_displacement_eq hb modules transfer p initial control edge)
    (fun p => six_lt hb modules transfer p initial control edge)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Rigidity
