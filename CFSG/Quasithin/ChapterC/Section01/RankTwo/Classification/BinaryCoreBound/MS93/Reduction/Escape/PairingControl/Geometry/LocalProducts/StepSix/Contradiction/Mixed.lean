module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Contradiction.Intersections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Contradiction.Mixed.Generation

/-!
# The mixed commutator in the trivial R_mu branch

For R_mu = 1, the literal actor Z_mu Z_(alpha'-2) lies in Q_(alpha-2).
Its commutator with Z_(alpha-4) is the natural intersection at alpha-2
and alpha-4. The order-four calculation uses their own intervening edge,
before the later comparison with U_alpha. Containment in V_(alpha'-4)
and b > 6 give centralization of Z_alpha'.

The opposite commutator noncontainment is an explicit input discharged by
the parent argument. No final natural-intersection equality or step-(6)
bound is used here.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank
two* (1993), (4.3.2)(6), printed p.885.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}
namespace EscapingWitness
variable {p : Counterexample geometry} {d : Vertex R} (w : EscapingWitness p d)

/-- The displayed equality uses the original predecessor p.c, not the backward vertex. -/
theorem mixed_commutator_eq_fourth_intersection (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hd : Before p.a p.a' d 4) (hzero : w.Rmu = ⊥)
    (hnon : ¬ ⁅Z R w.mu, Z R w.fourth⁆ ≤ Z R d) :
    ⁅Z R w.fourth, Z R w.mu ⊔ Z R p.c⁆ = U R w.choice.back ⊓ U R w.fourth := by
  apply le_antisymm
    (w.mixed_commutator_le_fourth_intersection source hb modules facts initial bad hd hzero)
  rw [← w.mu_commutator_eq_fourth_intersection source hb modules facts initial bad hd hzero hnon]
  exact commutator_mono le_rfl le_sup_left

/-- The mixed equality and the original strict radius bound give the printed centralization. -/
theorem fourth_natural_intersection_centralizes_endpoint (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hlarge : 6 < geometry.b R) (hd : Before p.a p.a' d 4) (hzero : w.Rmu = ⊥)
    (hnon : ¬ ⁅Z R w.mu, Z R w.fourth⁆ ≤ Z R d) :
    U R w.choice.back ⊓ U R w.fourth ≤ centralizer (Z R p.a' : Set (FreeAmalgam R)) := by
  rw [← w.mixed_commutator_eq_fourth_intersection source hb modules facts initial bad hd hzero hnon]
  exact w.mixed_commutator_centralizes_endpoint source hlarge hd

/-- The three inputs needed by the parent's separate support calculation. -/
theorem mixed_calculation (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hlarge : 6 < geometry.b R) (hd : Before p.a p.a' d 4) (hzero : w.Rmu = ⊥)
    (hnon : ¬ ⁅Z R w.mu, Z R w.fourth⁆ ≤ Z R d) :
    ⁅Z R w.fourth, Z R w.mu ⊔ Z R p.c⁆ = U R w.choice.back ⊓ U R w.fourth ∧
    Nat.card (U R w.choice.back ⊓ U R w.fourth : Subgroup (FreeAmalgam R)) = 4 ∧
    U R w.choice.back ⊓ U R w.fourth ≤ centralizer (Z R p.a' : Set (FreeAmalgam R)) :=
  ⟨w.mixed_commutator_eq_fourth_intersection source hb modules facts initial bad hd hzero hnon,
    w.fourth_natural_intersection_card source hb modules facts initial bad hd,
    w.fourth_natural_intersection_centralizes_endpoint source hb modules facts initial bad
      hlarge hd hzero hnon⟩

end EscapingWitness
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
