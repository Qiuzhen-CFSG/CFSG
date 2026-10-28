module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.InitialModule
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.QuasisimpleCriticalComparison

/-!
Adapted from the checked Chapter15 MarkedMS.G2Reconstruction proof to the
exceptional MS2(b) input. Only the two-group and core-containment consequences
of MS2 are used; the original SmallMSPair interface is unchanged.

# Critical-pair contracts for the small G₂ reconstruction

The arbitrary MS-pair has positive even free-holomorph critical distance and
the actual edge-centralizer identity. At a critical endpoint, the source
commutator comparison gives the ambient Frattini containment by the proved
quasisimple action-kernel argument.

Two independent earlier-source assertions remain explicit: the G₂ case of
MS93 (3.8) excludes distance greater than two, and its (3.3) comparison at
distance two excludes the G₂ row. The downstream assembly discharges neither
assertion by defining these contracts.
Source: MS93 (3.3), (3.6), (3.8), pp.866--868,870--872,877--879.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.G2Exceptional
open ChapterC BinaryMS.MS93
namespace Reconstruction
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}

local notation "H" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "T" => R.subgroupOf (L ⊔ R)

/-- The exact remaining ambient commutator containment from MS93 (3.6). -/
def FrattiniSmall (L R : Subgroup G) : Prop :=
  ⁅pCore 2 (L ⊔ R : Subgroup G),L.subgroupOf (L ⊔ R)⁆ ≤
    (frattini (pCore 2 (L ⊔ R : Subgroup G))).map
      (pCore 2 (L ⊔ R : Subgroup G)).subtype ⊔
      omegaCenterIn (pCore 2 (L ⊔ R : Subgroup G))

variable (h : Pair KnownSimple.IsKnownSimple L R)
  (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2)))

include h

theorem geometry : Geometry T :=
  BinaryMS.MS93.geometry T (edge_two_group h) (edge_ne_bot h) (edge_characteristic h)

include e

theorem positive_even : 0 < (geometry h).b T ∧ Even ((geometry h).b T) := by
  obtain ⟨g,hp,he⟩ := MSCentralOrbit.exists_positive_even_geometry T
    (edge_two_group h) (edge_ne_bot h) (edge_characteristic h) (core_le_edge h)
    (core_self_centralizing h) (initial_orbit_centralizer h e)
  exact ⟨hp,he⟩

theorem distance_ge_two : 2 ≤ (geometry h).b T := by
  obtain ⟨hp,⟨n,hn⟩⟩ := positive_even h e
  omega

theorem edgeCentralizer : EdgeCentralizerCondition T :=
  MSCentralOrbit.edgeCentralizerCondition T (edge_two_group h) (core_le_edge h)
    (initial_orbit_centralizer h e)

/-- A local comparison at one actual critical pair controls the whole core. -/
theorem frattini_small_of_critical_comparison
    (z : Vertex T) (hc : CriticalPair T (alpha T) z ((geometry h).exists_critical _ rfl))
    (hcomm : ⁅Q T (alpha T),Z T z⁆ ≤
      (frattini (Q T (alpha T))).map (Q T (alpha T)).subtype ⊔ X T (alpha T)) :
    FrattiniSmall L R := by
  let := relative_normal h
  let := Atlas.G2.isSimple_commutator_binary
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.core_quasisimple_of_centralCore e
  have hq : IsQuasisimple (K ⧸ pCore 2 K) :=
    IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr _ _ (show K ≃* L from subgroupOfEquivOfLe le_sup_left)
        (pCore_map_iso 2 (show K ≃* L from subgroupOfEquivOfLe le_sup_left))).symm
  let := hq
  apply MSCentralOrbit.original_frattini_of_critical_comparison K T h.component
    (edge_two_group h) _ (core_le_edge h) (geometry h) (positive_even h e).1
    (edgeCentralizer h e) z hc hcomm
  rw [← subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]

/-- Independent G₂ critical-distance bound from MS93 (3.8). -/
def DistanceTwoInput : Prop :=
  ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J)
    (h : Pair KnownSimple.IsKnownSimple L R),
    ((L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) →
    (geometry h).b (R.subgroupOf (L ⊔ R)) = 2

/-- Independent G₂ local comparison from MS93 (3.3), allowed to assume
the distance-two conclusion whose proof has a separate owner. -/
def DistanceTwoComparisonInput : Prop :=
  ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J)
    (h : Pair KnownSimple.IsKnownSimple L R),
    ((L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) →
    (geometry h).b (R.subgroupOf (L ⊔ R)) = 2 →
    ∀ z : Vertex (R.subgroupOf (L ⊔ R)),
    CriticalPair (R.subgroupOf (L ⊔ R)) (alpha (R.subgroupOf (L ⊔ R))) z
      ((geometry h).exists_critical _ rfl) →
    ⁅Q (R.subgroupOf (L ⊔ R)) (alpha (R.subgroupOf (L ⊔ R))),
      Z (R.subgroupOf (L ⊔ R)) z⁆ ≤
      (frattini (Q (R.subgroupOf (L ⊔ R)) (alpha (R.subgroupOf (L ⊔ R))))).map
        (Q (R.subgroupOf (L ⊔ R)) (alpha (R.subgroupOf (L ⊔ R)))).subtype ⊔
        X (R.subgroupOf (L ⊔ R)) (alpha (R.subgroupOf (L ⊔ R)))

theorem frattini_small_of_distance_inputs
    (hd : DistanceTwoInput.{u}) (hc : DistanceTwoComparisonInput.{u}) : FrattiniSmall L R := by
  obtain ⟨z,hz⟩ := criticalPair_exists T (alpha T) ((geometry h).exists_critical _ rfl)
  exact frattini_small_of_critical_comparison h e z hz (hc G L R h e (hd G L R h e) z hz)

end Reconstruction
end CFSG.Quasithin.ChapterC.G2Exceptional
