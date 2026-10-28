module

public import Stellmacher.PushingUp.DistanceFourInitialRelations
public import Theory.ElementaryAbelian.Join
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The elementary quotient in the distance-four configuration

For the original pushing-up hypotheses and a critical-distance-four
configuration, the literal subgroup `Ubar` of `G_a/Z(G_a)` is elementary
abelian. This is the barred assertion in Stellmacher, *Pushing up* (1986),
(3.3)(2), journal p.15; it does not assert elementarity of the ambient `U`.

The critical-pair action inputs put all three factors of `U` in their
respective elementary omega centers. The initial relations place `U` in
`Q_a`, show that `Z_a` centralizes `U`, and put `[Z_u,Z_c]` in `Z(G_a)`.
Consequently the three images in the central quotient are elementary and
commute pairwise, so the elementary-abelian join theorem applies twice.
All transport helpers remain private; the public theorem uses exactly the
production configuration and quotient subgroup.
-/

namespace Stellmacher.PushingUp

private theorem image_commutator_bot_of_le_ker
    {G H : Type*} [Group G] [Group H] (f : G →* H)
    (A B : Subgroup G) (h : ⁅A, B⁆ ≤ f.ker) :
    ⁅A.map f, B.map f⁆ = ⊥ := by
  rw [← Subgroup.map_commutator]
  exact (Subgroup.map_eq_bot_iff ⁅A, B⁆).mpr h

private theorem three_join_image_elementary
    {G H : Type*} [Group G] [Group H] (f : G →* H)
    (A B C : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    [IsElementaryAbelian 2 C]
    (hAB : ⁅A, B⁆ ≤ f.ker) (hAC : ⁅A, C⁆ ≤ f.ker)
    (hBC : ⁅B, C⁆ ≤ f.ker) :
    IsElementaryAbelian 2 ((A ⊔ B ⊔ C).map f) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map (A := A) f
  let _ : IsElementaryAbelian 2 (B.map f) := IsElementaryAbelian.map (A := B) f
  let _ : IsElementaryAbelian 2 (C.map f) := IsElementaryAbelian.map (A := C) f
  have hBA : B.map f ≤ Subgroup.centralizer (A.map f) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    rw [Subgroup.commutator_comm]
    exact image_commutator_bot_of_le_ker f A B hAB
  let _ : IsElementaryAbelian 2 ↥(A.map f ⊔ B.map f : Subgroup H) :=
    IsElementaryAbelian.sup_of_le_centralizer hBA
  have hCA : C.map f ≤ Subgroup.centralizer (A.map f) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    rw [Subgroup.commutator_comm]
    exact image_commutator_bot_of_le_ker f A C hAC
  have hCB : C.map f ≤ Subgroup.centralizer (B.map f) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    rw [Subgroup.commutator_comm]
    exact image_commutator_bot_of_le_ker f B C hBC
  have hCAB : C.map f ≤ Subgroup.centralizer ((A.map f ⊔ B.map f : Subgroup H) : Set H) := by
    apply Subgroup.le_centralizer_iff.mp
    exact sup_le (Subgroup.le_centralizer_iff.mp hCA)
      (Subgroup.le_centralizer_iff.mp hCB)
  rw [Subgroup.map_sup, Subgroup.map_sup]
  exact IsElementaryAbelian.sup_of_le_centralizer hCAB

private theorem elementary_of_omega_bound
    {G : Type*} [Group G] (A Q : Subgroup G)
    (h : A ≤ omegaOneCenterAmbient Q) : IsElementaryAbelian 2 A := by
  refine { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext ?_⟩⟩, exponent_dvd_p := ?_ }
  · exact (((mem_omegaOneCenterAmbient_iff Q (x : G)).mp (h x.property)).2.2
      y (((mem_omegaOneCenterAmbient_iff Q (y : G)).mp (h y.property)).1)).symm
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Subtype.ext
    exact ((mem_omegaOneCenterAmbient_iff Q (x : G)).mp (h x.property)).2.1

private theorem internal_commutator_le_center
    {G : Type*} [Group G] (A B H : Subgroup G) (hA : A ≤ H) (hB : B ≤ H)
    (h : ⁅A, B⁆ ≤ (Subgroup.center H).map H.subtype) :
    ⁅A.subgroupOf H, B.subgroupOf H⁆ ≤ Subgroup.center H := by
  apply (Subgroup.map_le_map_iff_of_injective H.subtype_injective).mp
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le hB]
  exact h

open AmalgamGraph
universe u
variable {M : Type u} [Group M]

set_option maxHeartbeats 600000 in
public theorem distanceFour_Ubar_elementary [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' c u v : Vertex S) (hb4 : criticalDistance S = 4)
    (cfg : DistanceFour.Configuration S a a' c u v) :
    IsElementaryAbelian 2 (DistanceFour.Ubar S a c u) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb : 0 < criticalDistance S := by omega
  have hi := distanceFour_initialRelations S T hTS hP hSne hA a a' c u v hb4 cfg
  obtain ⟨_, _, ha⟩ := criticalPair_actionInputs S T hTS hP hSne hA
    a a' cfg.critical hb
  obtain ⟨_, _, huc⟩ := criticalPair_actionInputs S T hTS hP hSne hA
    u c cfg.first_shift.shifted_critical hb
  let _ : IsElementaryAbelian 2 (vertexZ S a) :=
    elementary_of_omega_bound _ _ ha.left_Z_le_coreOmega
  let _ : IsElementaryAbelian 2 (vertexZ S c) :=
    elementary_of_omega_bound _ _ huc.right_Z_le_coreOmega
  let _ : IsElementaryAbelian 2 (vertexZ S u) :=
    elementary_of_omega_bound _ _ huc.left_Z_le_coreOmega
  have hUG : DistanceFour.U S a c u ≤ stabilizer S a :=
    hi.U_le_core.trans (Subgroup.map_subtype_le _)
  have haU : vertexZ S a ≤ DistanceFour.U S a c u := le_sup_left.trans le_sup_left
  have hcU : vertexZ S c ≤ DistanceFour.U S a c u := le_sup_right.trans le_sup_left
  have huU : vertexZ S u ≤ DistanceFour.U S a c u := le_sup_right
  have haG := haU.trans hUG
  have hcG := hcU.trans hUG
  have huG := huU.trans hUG
  let _ : IsElementaryAbelian 2 ((vertexZ S a).subgroupOf (stabilizer S a)) :=
    IsElementaryAbelian.subgroupOf haG
  let _ : IsElementaryAbelian 2 ((vertexZ S c).subgroupOf (stabilizer S a)) :=
    IsElementaryAbelian.subgroupOf hcG
  let _ : IsElementaryAbelian 2 ((vertexZ S u).subgroupOf (stabilizer S a)) :=
    IsElementaryAbelian.subgroupOf huG
  have hac : ⁅vertexZ S a, vertexZ S c⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    intro z hz
    exact Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (hi.Z_centralizes_U z hz w (hcU hw)).symm
  have hau : ⁅vertexZ S a, vertexZ S u⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    intro z hz
    exact Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (hi.Z_centralizes_U z hz w (huU hw)).symm
  have hcu : ⁅vertexZ S c, vertexZ S u⁆ ≤
      (Subgroup.center (stabilizer S a)).map (stabilizer S a).subtype := by
    rw [Subgroup.commutator_comm]
    exact hi.Y_le_center
  change IsElementaryAbelian 2 (((vertexZ S a ⊔ vertexZ S c ⊔ vertexZ S u).subgroupOf (stabilizer S a)).map (QuotientGroup.mk' (Subgroup.center (stabilizer S a))))
  rw [Subgroup.subgroupOf_sup (sup_le haG hcG) huG, Subgroup.subgroupOf_sup haG hcG]
  apply three_join_image_elementary
  all_goals rw [QuotientGroup.ker_mk']
  · exact internal_commutator_le_center _ _ _ haG hcG (by rw [hac]; exact bot_le)
  · exact internal_commutator_le_center _ _ _ haG huG (by rw [hau]; exact bot_le)
  · exact internal_commutator_le_center _ _ _ hcG huG hcu

end Stellmacher.PushingUp
