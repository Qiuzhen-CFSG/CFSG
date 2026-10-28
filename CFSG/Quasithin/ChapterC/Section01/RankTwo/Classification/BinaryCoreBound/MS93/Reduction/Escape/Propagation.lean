module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Edges
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Consequences
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Rigidity
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour

/-!
# Propagation of the contrary configuration, MS93 (4.3.3)--(4.3.8)

The two edge indices are proved from the preceding escape stages, using the
literal natural action. Neighboring Z-layer rigidity gives b > 6. Selection
and normalization by the relative normalizer give the backward products and
moving symmetry. These imply centrality, the exact local conjugator witnesses,
and all three radius-four conclusions. The final assembly constructs each
stage from LocalSource, Geometry, b > 2, ModuleFacts, NormalizationTransfer,
and the initial, local-control and edge-transfer inputs.

The original Escape.PropagationFacts interface is preserved, including both
local centers, relative product normality, the reverse moving-neighbor span,
all radius-four conclusions and the actual conjugator witnesses.
Its backward-bound field retains the old edge-stabilizer generating premise.
The stronger `sourcePropagationFacts` also supplies the literal (4.3.6) bound
with the relative normalizer `G_a ∩ N(Q_t)` defined on printed p.881.

Source: Meierfrankenfeld--Stellmacher (1993), notation on p.881 and
(4.3.3)--(4.3.8), printed pp.886--889. The final contradiction on pp.889--890
and the discharge of the preceding stages belong to the parent escape proof.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Conditional assembly only: the three remaining source stages must all
be constructed before this gives the requested propagation theorem. -/
theorem propagationFacts_of_stages (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (control : ∀ p : Counterexample geometry, LocalControl p) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry) (backward : BackwardFacts geometry)
    (radius : RadiusFourFacts geometry) : PropagationFacts geometry where
  edge_indices p t ht := edge_indices hb modules p initial control edge
    p.a t p.color_a ht.endpoint_adjacent
  equal_Z := rigidity.equal_Z
  moving_Z_unique := rigidity.moving_Z_unique
  six_lt := rigidity.six_lt
  backward_bound := backward.backward_bound
  product_normal := backward.product_normal
  moving_symmetric := backward.moving_symmetric
  far_not_moving := backward.far_not_moving
  moving_radius_bound := backward.moving_radius_bound
  radius_central p d hd := le_inf (radius.radius_central_at_two p)
    (radius_central_at_four (by omega) backward p d hd)
  witnesses := radius.witnesses
  radius_four := radius.radius_four

/-- MS93 (4.3.3)--(4.3.8) from the preceding stages, including the literal
relative-normalizer version of (4.3.6). All rigidity, backward and radius-four
premises of the conditional assembly are constructed here. -/
theorem sourcePropagationFacts (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (transfer : NormalizationTransfer R)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (control : ∀ p : Counterexample geometry, LocalControl p) (edge : EdgeTransfer geometry) :
    PropagationFacts geometry ∧ Backward.Products.Selection.RelativeBoundFacts geometry := by
  have rigidity := Rigidity.rigidityFacts hb modules transfer initial control edge
  have backward := Backward.backwardFacts source hb modules transfer initial control edge rigidity
  have radius := RadiusFour.radiusFourFacts source hb modules initial control edge rigidity backward
  exact ⟨propagationFacts_of_stages hb modules initial control edge rigidity backward radius,
    Backward.relativeBoundFacts source hb modules initial control edge rigidity⟩

/-- The original propagation interface, with every intermediate stage proved
from the authorized preceding inputs. `sourcePropagationFacts` additionally
retains the backward bound with the source relative-normalizer premise. -/
theorem propagationFacts (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (transfer : NormalizationTransfer R)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (control : ∀ p : Counterexample geometry, LocalControl p) (edge : EdgeTransfer geometry) :
    PropagationFacts geometry :=
  (sourcePropagationFacts source hb modules transfer initial control edge).1

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation
