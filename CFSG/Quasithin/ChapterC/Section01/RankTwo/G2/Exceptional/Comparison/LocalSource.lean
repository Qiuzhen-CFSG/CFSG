module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.Geometry
public import Theory.Representation.G2BinaryPointFlagDisplacement
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
Adapted from the checked Chapter15 MarkedMS.G2Reconstruction proof to the
exceptional MS2(b) input. Only the two-group and core-containment consequences
of MS2 are used; the original SmallMSPair interface is unchanged.

# The literal local inputs to the G₂ critical comparison

At distance two the starting kernel is in the common edge kernel and
centralizes the critical commutator. The missing G₂ module calculation has
two parts: identify the whole endpoint seed modulo its residual fixed part,
then place that fixed kernel and the critical image. The natural section of
the moved omega-center alone supplies neither assertion.

These are explicit prerequisite contracts, not proofs of MS93 (3.2)(vii)
or (3.3). `Comparison.Source` proves their application to the requested
commutator bound and the original Frattini containment.
Source: Meierfrankenfeld--Stellmacher (1993), pp.863--868,870--871.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.G2Exceptional
open ChapterC BinaryMS.MS93
namespace Reconstruction.Comparison
universe u
variable {M : Type u} [Group M] [Finite M] (T : Subgroup M)

/-- The six coordinates of the actual binary octonion natural quotient. -/
abbrev NaturalSpace := Fin 6 → ZMod 2

/-- A marking of the whole endpoint seed and its actual stabilizer action.
The kernel is the residual fixed subgroup, not an arbitrary central section. -/
structure EndpointModel (z : Vertex T) where
  projection : Z T z →* Multiplicative NaturalSpace
  projection_surjective : Function.Surjective projection
  actor : stabilizer T z →* Atlas.G2.Model (ZMod 2)
  actor_kernel : actor.ker.map (stabilizer T z).subtype = Q T z
  actor_residual : ((Ltilde T z).subgroupOf (stabilizer T z)).map actor =
    commutator (Atlas.G2.Model (ZMod 2))
  projection_kernel : projection.ker.map (Z T z).subtype =
    Z T z ⊓ centralizer (Ltilde T z : Set (FreeAmalgam T))
  intertwines : ∀ (g : stabilizer T z) (v : Z T z),
    projection ⟨g.val * v.val * g.val⁻¹,
      (mem_normalizer_iff.mp (Z_normalized T z g.property) v.val).mp v.property⟩ =
      Multiplicative.ofAdd
        (Atlas.G2.Restricted.NaturalCoordinates.action (ZMod 2) (actor g)
          (projection v).toAdd)

/-- The two geometric placements used by the comparison. The critical
commutator covers a self-orthogonal subspace in the literal natural quotient;
the full fixed kernel lies in the starting omega-center. -/
def EndpointPlacement (a z : Vertex T) (d : EndpointModel T z) : Prop :=
  d.projection.ker.map (Z T z).subtype ≤ X T a ∧
    ∃ W : Submodule (ZMod 2) NaturalSpace,
      LinearMap.BilinForm.orthogonal Atlas.G2.Natural.BinaryPointFlag.pairing W = W ∧
      ∀ w ∈ W, Multiplicative.ofAdd w ∈
        ((⁅Z T a,Z T z⁆).subgroupOf (Z T z)).map d.projection

variable {T}

omit [Finite M] in
/-- The actual critical commutator lies in the endpoint seed. -/
theorem critical_image_le_endpoint (g : Geometry T) (a z : Vertex T)
    (ha : color T a = false) (hc : CriticalPair T a z (g.exists_critical a ha)) :
    ⁅Z T a,Z T z⁆ ≤ Z T z := by
  apply le_normalizer_iff_commutator_le_right.mp
  exact (Z_le_stabilizer_of_dist_le a (g.exists_critical a ha) hc.1.le).trans
    (Z_normalized T z)

/-- The actual critical commutator lies in the starting seed as well. -/
theorem critical_image_le_start (g : Geometry T) (a z : Vertex T)
    (ha : color T a = false) (hc : CriticalPair T a z (g.exists_critical a ha)) :
    ⁅Z T a,Z T z⁆ ≤ Z T a := by
  have hz := critical_endpoint_color T a ha _ hc
  rw [commutator_comm]
  apply le_normalizer_iff_commutator_le_right.mp
  apply (Z_le_stabilizer_of_dist_le z (g.exists_critical z hz) ?_).trans
    (Z_normalized T a)
  rw [SimpleGraph.dist_comm,hc.1,g.distance_constant a ha,g.distance_constant z hz]

/-- Source (3.3)'s actor hypothesis for Y = Q_a, with the common neighbor
and the centralizer taken in the actual free amalgam. -/
theorem distance_two_source_actor (g : Geometry T) (a z : Vertex T)
    (ha : color T a = false) (hb : g.b T = 2)
    (hc : CriticalPair T a z (g.exists_critical a ha)) :
    ∃ t, Adjacent T a t ∧ Adjacent T z t ∧
      Q T a ≤ Q T t ⊓ centralizer
        ((⁅Z T a,Z T z⁆ : Subgroup (FreeAmalgam T)) : Set (FreeAmalgam T)) := by
  have hd : (cosetGraph T).dist a z = 2 :=
    hc.1.trans ((g.distance_constant a ha).trans hb)
  obtain ⟨t,hat,hzt⟩ := exists_common_neighbor_of_dist_two T a z hd
  have ht : color T t = true := by
    have hn := adjacent_color_ne T hat
    cases he : color T t <;> simp_all
  refine ⟨t,hat,hzt,le_inf (Q_le_adjacent_h T ht hat) ?_⟩
  exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
    (g.centralizes a ha))).trans (centralizer_le (critical_image_le_start g a z ha hc))

omit [Finite M] in
/-- At distance two the auxiliary term [X_a ∩ Q_z,Q_a] in (3.3) vanishes. -/
theorem source_auxiliary_eq_bot (a z : Vertex T) :
    ⁅X T a ⊓ Q T z,Q T a⁆ = ⊥ :=
  commutator_eq_bot_iff_le_centralizer.mpr
    (inf_le_left.trans (le_centralizer_iff.mp (Q_le_centralizer_X T a)))

/-- Earlier-source construction of the full marked endpoint module. -/
def EndpointModelInput : Prop :=
  ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J)
    (h : Pair KnownSimple.IsKnownSimple L R),
    ((L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) →
    (geometry h).b (R.subgroupOf (L ⊔ R)) = 2 →
    ∀ z : Vertex (R.subgroupOf (L ⊔ R)),
    CriticalPair (R.subgroupOf (L ⊔ R)) (alpha (R.subgroupOf (L ⊔ R))) z
      ((geometry h).exists_critical _ rfl) →
    Nonempty (EndpointModel (R.subgroupOf (L ⊔ R)) z)

/-- Independent reciprocal critical-image calculation, conditional on a
literal endpoint marking. Its producer need not wait for the marking producer. -/
def EndpointPlacementInput : Prop :=
  ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J)
    (h : Pair KnownSimple.IsKnownSimple L R),
    ((L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) →
    (geometry h).b (R.subgroupOf (L ⊔ R)) = 2 →
    ∀ z : Vertex (R.subgroupOf (L ⊔ R)),
    CriticalPair (R.subgroupOf (L ⊔ R)) (alpha (R.subgroupOf (L ⊔ R))) z
      ((geometry h).exists_critical _ rfl) →
    ∀ d : EndpointModel (R.subgroupOf (L ⊔ R)) z,
      EndpointPlacement (R.subgroupOf (L ⊔ R)) (alpha (R.subgroupOf (L ⊔ R))) z d

end Reconstruction.Comparison
end CFSG.Quasithin.ChapterC.G2Exceptional
