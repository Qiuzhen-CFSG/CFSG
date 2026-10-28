module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Witness
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Continuation.Triple

/-!
# The two edge planes in the R_mu argument

The moving-neighbor intersection from step (3) identifies the original
escaping edge with U_back intersected with U_start. Critical minimality
puts Z_mu in Q_start and Z_back in Q_d. Thus R_mu lies in both edge planes.
The plane at d centralizes the original endpoint. The original escaping
plane does not, so its intersection with that centralizer has order at
most two. Any nontrivial R_mu is exactly this intersection.

All transported edge identities use complete counterexamples. No initial
facts are applied to the new critical pair without a trapped radius.
Source: MS93 (4.3.2)(6), printed p.885.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

namespace EscapingWitness
variable {p : Counterexample geometry} {d : Vertex R} (w : EscapingWitness p d)

/-- The literal R_mu in the two printed branches. -/
noncomputable def Rmu : Subgroup (FreeAmalgam R) := ⁅Z R w.choice.back, Z R w.mu⁆

theorem endpoint_color (hd : Before p.a p.a' d 4) : color R d = false :=
  (hd.color (by decide)).trans p.end_color

theorem mu_color (hd : Before p.a p.a' d 4) : color R w.mu = false :=
  moving_color (endpoint_color hd) w.mu_moving

omit [Finite M] in
theorem back_endpoint_distance (hd : Before p.a p.a' d 4) :
    (cosetGraph R).dist w.choice.back d + 2 = geometry.b R := by
  have h := (w.toRadiusWitness.back_before hd).1
  have hpath := hd.2
  rw [p.distance_eq_b] at hpath
  omega

omit [Finite M] in
theorem mu_start_distance (hd : Before p.a p.a' d 4) :
    (cosetGraph R).dist w.mu p.a + 2 ≤ geometry.b R := by
  have h := (cosetGraph_connected R).dist_triangle (u := w.mu) (v := d) (w := p.a)
  have hpath := hd.2
  rw [p.distance_eq_b] at hpath
  rw [SimpleGraph.dist_comm (u := w.mu) (v := d), w.mu_moving.1,
    SimpleGraph.dist_comm (u := d) (v := p.a)] at h
  omega

omit [Finite M] in
theorem back_mu_distance (hd : Before p.a p.a' d 4) :
    (cosetGraph R).dist w.choice.back w.mu ≤ geometry.b R := by
  have h := (cosetGraph_connected R).dist_triangle
    (u := w.choice.back) (v := d) (w := w.mu)
  have hb := w.back_endpoint_distance hd
  rw [w.mu_moving.1] at h
  omega

theorem mu_Z_le_start_kernel (hd : Before p.a p.a' d 4) : Z R w.mu ≤ Q R p.a := by
  apply Z_le_Q_of_dist_lt R w.mu (geometry.exists_critical _ (w.mu_color hd))
  rw [geometry.distance_constant _ (w.mu_color hd)]
  have h := w.mu_start_distance hd
  change _ < geometry.b R
  omega

omit [Finite M] in
theorem back_Z_le_endpoint_kernel (hd : Before p.a p.a' d 4) :
    Z R w.choice.back ≤ Q R d := by
  apply Z_le_Q_of_dist_lt R w.choice.back
    (geometry.exists_critical _ w.toRadiusWitness.back_color)
  rw [geometry.distance_constant _ w.toRadiusWitness.back_color]
  have h := w.back_endpoint_distance hd
  change _ < geometry.b R
  omega

/-- The original common edge plane, using only step (3). -/
theorem back_natural_inf_start_Z (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) :
    U R w.choice.back ⊓ Z R p.a = edgeDisplacement p.a w.choice.edge :=
  Continuation.moving_natural_intersection source hb modules facts p initial bad
    p.color_a w.choice.adjacent_start w.choice.adjacent_back w.choice.moving

theorem back_natural_inf_start_natural (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) :
    U R w.choice.back ⊓ U R p.a = edgeDisplacement p.a w.choice.edge := by
  have h := w.back_natural_inf_start_Z source hb modules facts initial bad
  apply le_antisymm ((inf_le_inf_left _ (U_le_Z p.a)).trans h.le)
  exact le_inf (h.ge.trans inf_le_left)
    (Initial.edge_le_natural source p.a w.choice.edge p.color_a w.choice.adjacent_start)

theorem Rmu_le_start_edge (hb : 0 < geometry.b R)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hd : Before p.a p.a' d 4) : w.Rmu ≤ edgeDisplacement p.a w.choice.edge := by
  rw [← facts.edge_eq p.a w.choice.edge w.choice.back p.color_a
    w.choice.adjacent_start w.choice.adjacent_back w.choice.moving,
    ← FirstPairing.StepThree.moving_commutator_eq_edge_at p hb initial bad
      p.a w.choice.edge w.choice.back p.color_a w.choice.adjacent_start
      w.choice.adjacent_back w.choice.moving]
  exact commutator_mono le_rfl (w.mu_Z_le_start_kernel hd)

theorem Rmu_le_chosen_edge (hb : 0 < geometry.b R)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hd : Before p.a p.a' d 4) : w.Rmu ≤ edgeDisplacement d w.lam := by
  rw [← facts.edge_eq d w.lam w.mu (endpoint_color hd)
    w.lam_adjacent w.mu_adjacent w.mu_moving,
    ← FirstPairing.StepThree.moving_commutator_eq_edge_at p hb initial bad
      d w.lam w.mu (endpoint_color hd) w.lam_adjacent w.mu_adjacent w.mu_moving]
  rw [Rmu, commutator_comm]
  exact commutator_mono le_rfl (w.back_Z_le_endpoint_kernel hd)

theorem chosen_edge_centralizes_endpoint (source : LocalSource L R)
    (hlarge : 6 < geometry.b R) (hd : Before p.a p.a' d 4) :
    edgeDisplacement d w.lam ≤ centralizer (Z R p.a' : Set (FreeAmalgam R)) := by
  have hQ : Z R d ≤ Q R p.a' := by
    apply Z_le_Q_of_dist_lt R d (geometry.exists_critical _ (endpoint_color hd))
    rw [geometry.distance_constant _ (endpoint_color hd), hd.1]
    change 4 < geometry.b R
    omega
  exact ((Initial.edge_le_natural source d w.lam (endpoint_color hd) w.lam_adjacent).trans
    ((U_le_Z d).trans hQ)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes p.a' p.end_color)))

/-- In the trivial branch faithfulness gives the actual kernel containment. -/
theorem mu_Z_le_back_kernel_of_Rmu_eq_bot (source : LocalSource L R)
    (modules : ModuleFacts source geometry) (hd : Before p.a p.a' d 4)
    (hzero : w.Rmu = ⊥) : Z R w.mu ≤ Q R w.choice.back := by
  rw [← modules.natural.centralizer _ w.toRadiusWitness.back_color]
  apply le_inf
  · apply geometry.Z_le_stabilizer_of_dist_le_b _ (w.mu_color hd)
    rw [SimpleGraph.dist_comm]
    exact w.back_mu_distance hd
  · exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)).trans
      (centralizer_le (U_le_Z w.choice.back))

/-- The original trapped radius supplies this kernel containment; no new
counterexample at the backward vertex is assumed. -/
theorem predecessor_Z_le_back_kernel (source : LocalSource L R)
    (modules : ModuleFacts source geometry) : Z R p.c ≤ Q R w.choice.back := by
  rw [← modules.natural.centralizer _ w.toRadiusWitness.back_color]
  apply le_inf
  · apply geometry.Z_le_stabilizer_of_dist_le_b _ p.before_color
    have h := (cosetGraph_connected R).dist_triangle
      (u := p.c) (v := p.a) (w := w.choice.back)
    have hp := p.before.2
    rw [p.distance_eq_b] at hp
    rw [SimpleGraph.dist_comm (u := p.c) (v := p.a), w.choice.moving.1] at h
    omega
  · have hback : Z R w.choice.back ≤ Q R p.c :=
      (moving_Z_le_V w.choice.moving).trans p.trapped
    exact (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes p.c p.before_color)).trans
        (centralizer_le ((U_le_Z w.choice.back).trans hback))

/-- Both factors in the printed mixed commutator really lie in Q_back. -/
theorem mixed_actors_le_back_kernel (source : LocalSource L R)
    (modules : ModuleFacts source geometry) (hd : Before p.a p.a' d 4)
    (hzero : w.Rmu = ⊥) : Z R w.mu ⊔ Z R p.c ≤ Q R w.choice.back :=
  sup_le (w.mu_Z_le_back_kernel_of_Rmu_eq_bot source modules hd hzero)
    (w.predecessor_Z_le_back_kernel source modules)

/-- The strict b > 6 bound controls the literal mu and alpha'-2 factors. -/
theorem mixed_actors_le_endpoint_kernel (hlarge : 6 < geometry.b R)
    (hd : Before p.a p.a' d 4) : Z R w.mu ⊔ Z R p.c ≤ Q R p.a' := by
  apply sup_le
  · apply Z_le_Q_of_dist_lt R w.mu (geometry.exists_critical _ (w.mu_color hd))
    rw [geometry.distance_constant _ (w.mu_color hd)]
    have h := (cosetGraph_connected R).dist_triangle (u := w.mu) (v := d) (w := p.a')
    rw [SimpleGraph.dist_comm (u := w.mu) (v := d), w.mu_moving.1, hd.1] at h
    change _ < geometry.b R
    omega
  · apply Z_le_Q_of_dist_lt R p.c (geometry.exists_critical _ p.before_color)
    rw [geometry.distance_constant _ p.before_color, p.before.1]
    change 2 < geometry.b R
    omega

private theorem card_le_two_of_proper_four {G : Type*} [Group G]
    (A E : Subgroup G) [Finite E] (hAE : A ≤ E)
    (hfour : Nat.card E = 4) (hne : A ≠ E) : Nat.card A ≤ 2 := by
  let : Finite A := Finite.of_injective (inclusion hAE) (inclusion_injective _)
  have hdvd : Nat.card A ∣ 4 := hfour ▸ card_dvd_of_le hAE
  have hn : Nat.card A ≠ 4 := by
    intro h
    exact hne (eq_of_le_of_card_ge hAE (by omega))
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 4 ≠ 0)⟩
  rw [show Nat.divisors 4 = ({1, 2, 4} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  omega

/-- The nontrivial R_mu is the literal step-(3) intersection on p.885. -/
theorem Rmu_eq_intersection (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hlarge : 6 < geometry.b R) (hd : Before p.a p.a' d 4) (hne : w.Rmu ≠ ⊥) :
    w.Rmu = (U R w.choice.back ⊓ U R p.a) ⊓
      centralizer (Z R p.a' : Set (FreeAmalgam R)) := by
  rw [w.back_natural_inf_start_natural source hb modules facts initial bad]
  let E := edgeDisplacement p.a w.choice.edge
  let C := E ⊓ centralizer (Z R p.a' : Set (FreeAmalgam R))
  have hE : E ≤ U R p.a :=
    Initial.edge_le_natural source p.a w.choice.edge p.color_a w.choice.adjacent_start
  let : Finite (U R p.a) := Nat.finite_of_card_ne_zero (by
    rw [modules.natural.card_at p.a p.color_a]; decide)
  let : Finite E := Finite.of_injective (inclusion hE) (inclusion_injective _)
  let : Finite C := Finite.of_injective (inclusion (show C ≤ E from inf_le_left))
    (inclusion_injective _)
  have hproper : C ≠ E := by
    intro he
    apply w.choice.escapes
    rw [← modules.natural.centralizer p.a' p.end_color]
    refine le_inf (hE.trans ((U_le_Z p.a).trans
      (source.critical_Z_le_stabilizer geometry p.a p.color_a p.a' p.critical).1)) ?_
    exact (he ▸ (show C ≤ centralizer (Z R p.a' : Set (FreeAmalgam R)) from inf_le_right)).trans
      (centralizer_le (U_le_Z p.a'))
  have hsmall : Nat.card C ≤ 2 := card_le_two_of_proper_four C E inf_le_left
    (FirstPairing.StepThree.edge_card p (by omega) initial
      p.a w.choice.edge p.color_a w.choice.adjacent_start) hproper
  have hle : w.Rmu ≤ C := le_inf (w.Rmu_le_start_edge (by omega) facts initial bad hd)
    ((w.Rmu_le_chosen_edge (by omega) facts initial bad hd).trans
      (w.chosen_edge_centralizes_endpoint source hlarge hd))
  let : Finite w.Rmu := Finite.of_injective (inclusion hle) (inclusion_injective _)
  have hlarge' := (one_lt_card_iff_ne_bot _).mpr hne
  change w.Rmu = C
  exact eq_of_le_of_card_ge hle (by omega)

/-- The nontrivial branch finishes once its module argument places R_4 in Z_start. -/
theorem false_of_Rmu_ne_bot_of_Rfour_le_Z (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hlarge : 6 < geometry.b R) (hd : Before p.a p.a' d 4)
    (hne : w.Rmu ≠ ⊥) (hZ : w.toRadiusWitness.Rfour ≤ Z R p.a) : False := by
  apply w.escapes
  apply le_trans _ (w.Rmu_le_chosen_edge (by omega) facts initial bad hd)
  rw [w.Rmu_eq_intersection source hb modules facts initial bad hlarge hd hne,
    w.back_natural_inf_start_natural source hb modules facts initial bad,
    ← w.back_natural_inf_start_Z source hb modules facts initial bad]
  exact le_inf (le_inf (w.toRadiusWitness.Rfour_le_backward_natural source facts hd) hZ)
    (w.toRadiusWitness.Rfour_centralizes_endpoint source modules hlarge hd)

end EscapingWitness
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
