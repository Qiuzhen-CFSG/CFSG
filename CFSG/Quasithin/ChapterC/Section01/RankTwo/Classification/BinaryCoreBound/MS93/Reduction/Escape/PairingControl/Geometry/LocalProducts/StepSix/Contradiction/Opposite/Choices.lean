module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Choice
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.LocalAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.FiniteGeometry.Planes
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Backward choices and the critical commutator line

The original `BackwardChoice` requires its edge plane to escape the endpoint
kernel. There are such choices both avoiding and containing the critical
commutator line. Avoidance is obtained from the intersection of all edge
planes. For containment, join the critical line to a line outside the
endpoint kernel, then realize this plane by an actual incident edge using
the natural SL(3,2) action. In each case local transitivity supplies an actual
moving backward vertex.

These statements use only the earlier source inputs. In particular, the
local model and its plane orbit use the actual natural-module coordinates;
none of the later local-control or generation assumptions are used.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the choice of alpha - 1 preceding (4.3.2)(6), printed p.885.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

/-- The backward choice can be made to avoid the critical commutator line.
This strengthens its existing kernel-escape condition without adding a premise. -/
theorem exists_backwardChoice_critical_avoidance (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R) (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) :
    ∃ choice : BackwardChoice p,
      ¬ criticalCommutator p.a p.a' ≤ edgeDisplacement p.a choice.edge := by
  obtain ⟨hi⟩ := initial p
  obtain ⟨t, ht, havoid⟩ := exists_avoiding_edge source hb modules facts p.color_a
    (criticalCommutator p.a p.a') (source.critical_noncommutation geometry p.a p.color_a p.critical)
  have hEU : edgeDisplacement p.a t ≤ U R p.a := Initial.edge_le_natural source p.a t p.color_a ht
  have hescape : ¬ edgeDisplacement p.a t ≤ Q R p.a' := by
    intro hEQ
    let C := U R p.a ⊓ Q R p.a'
    have hEC : edgeDisplacement p.a t ≤ C := le_inf hEU hEQ
    let s : BinaryNaturalStructure source :=
      ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
    have hindex : (Q R p.a').relIndex (U R p.a) = 2 := by
      rw [← s.critical_Z_index_eq_U geometry p.a p.color_a p.a' p.critical]
      exact hi.critical_index
    have hCcard : Nat.card C = 4 := by
      have hh := ((Q R p.a').subgroupOf (U R p.a)).index_mul_card
      rw [show ((Q R p.a').subgroupOf (U R p.a)).index = 2 from hindex,
        modules.natural.card_at p.a p.color_a] at hh
      have he := Nat.card_congr (subgroupOfEquivOfLe
        (show C ≤ U R p.a from inf_le_left)).toEquiv
      rw [inf_subgroupOf_left] at he
      omega
    let : Finite C := Nat.finite_of_card_ne_zero (by rw [hCcard]; decide)
    have heq : edgeDisplacement p.a t = C := eq_of_le_of_card_ge hEC (by
      rw [hCcard, FirstPairing.StepThree.edge_card p (by omega) initial p.a t p.color_a ht])
    apply havoid
    rw [heq]
    apply le_inf
    · change ⁅Z R p.a, Z R p.a'⁆ ≤ U R p.a
      exact (commutator_mono le_rfl p.end_Z_le_start_stabilizer).trans
        (Initial.Z_commutator_stabilizer source p.a p.color_a).le
    · exact (p.critical_le_radius_inf_start.trans inf_le_left).trans
        (p.radius_le_end.trans ((Z_le_VBall R p.a' 2).trans
          (geometry.V_le_Q hb p.a' p.end_color)))
  obtain ⟨d, hd, hm⟩ := exists_moving_at_edge hb transfer p bad p.color_a ht
  exact ⟨⟨t, d, ht, hd, hm, hescape⟩, havoid⟩

open Propagation.Backward.Products.Selection.Choices in
/-- Every plane of the natural group occurs as an actual incident displacement. -/
theorem exists_edge_with_natural_plane (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (p : Counterexample geometry) (E : Subgroup (FreeAmalgam R))
    (hEU : E ≤ U R p.a) (hcard : Nat.card E = 4) :
    ∃ t, Adjacent R p.a t ∧ edgeDisplacement p.a t = E := by
  obtain ⟨model⟩ := localModel_nonempty source modules p.a p.color_a
  obtain ⟨t, ht, _⟩ := exists_adjacent_dist_sub_one R p.a p.a'
    (p.distance_eq_b.symm ▸ (show 0 < geometry.b R by omega))
  have hU := Initial.edge_le_natural source p.a t p.color_a ht
  have hAcard : Nat.card (model.coordinates (edgeDisplacement p.a t)) = 4 := by
    rw [model.coordinates_card _ hU]
    exact FirstPairing.StepThree.edge_card p (by omega) initial p.a t p.color_a ht
  obtain ⟨a, ha⟩ := FiniteGeometry.plane_transitive _ hAcard
  obtain ⟨b, hb'⟩ := FiniteGeometry.plane_transitive _
    ((model.coordinates_card _ hEU).trans hcard)
  obtain ⟨s, hs, he⟩ := model.realizes_plane source p.color_a ht (b * a⁻¹)
  refine ⟨s, hs, model.coordinates_injective
    (Initial.edge_le_natural source p.a s p.color_a hs) hEU ?_⟩
  rw [he]
  change FiniteGeometry.move (b * a⁻¹) (model.coordinates (edgeDisplacement p.a t)) = _
  rw [← ha, ← FiniteGeometry.move_mul, FiniteGeometry.move_cancel]
  exact hb'

/-- The original kernel-escape condition also permits a plane containing
the critical line. Thus that condition alone is not critical avoidance. -/
theorem exists_backwardChoice_critical_containment (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) :
    ∃ choice : BackwardChoice p,
      criticalCommutator p.a p.a' ≤ edgeDisplacement p.a choice.edge := by
  classical
  obtain ⟨hi⟩ := initial p
  obtain ⟨u, huU, huQ⟩ := SetLike.not_le_iff_exists.mp
    (natural_not_le_endpoint_kernel source modules p)
  let C := criticalCommutator p.a p.a'
  have hCU : C ≤ U R p.a :=
    (commutator_mono le_rfl p.end_Z_le_start_stabilizer).trans
      (Initial.Z_commutator_stabilizer source p.a p.color_a).le
  have hCQ : C ≤ Q R p.a' :=
    (p.critical_le_radius_inf_start.trans inf_le_left).trans
      (p.radius_le_end.trans ((Z_le_VBall R p.a' 2).trans
        (geometry.V_le_Q hb p.a' p.end_color)))
  let := geometry.Z_elementary (by omega) p.a p.color_a
  have hu2 : u ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian u (U_le_Z p.a huU)
  have hu1 : u ≠ 1 := fun h => huQ (h ▸ (Q R p.a').one_mem)
  have huorder : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  have huF : IsOfFinOrder u := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hu2⟩
  have hzU : zpowers u ≤ U R p.a := zpowers_le.mpr huU
  have hzC : zpowers u ≤ centralizer (C : Set (FreeAmalgam R)) := by
    exact (hzU.trans (U_le_Z p.a)).trans
      ((commutator_eq_bot_iff_le_centralizer.mp
        (commutator_self_eq_bot_iff.mpr inferInstance)).trans
          (centralizer_le (hCU.trans (U_le_Z p.a))))
  have hd : Disjoint C (zpowers u) := by
    apply Subgroup.disjoint_def.mpr
    intro x hxC hxu
    have hx : x = 1 ∨ x = u := by
      obtain ⟨n, hn, hnx⟩ := Finset.mem_image.mp
        (huF.mem_zpowers_iff_mem_range_orderOf.mp hxu)
      have hn2 : n < 2 := by simpa only [Finset.mem_range, huorder] using hn
      interval_cases n <;> simp_all
    rcases hx with rfl | rfl
    · rfl
    · exact (huQ (hCQ hxC)).elim
  let E := C ⊔ zpowers u
  have hEU : E ≤ U R p.a := sup_le hCU hzU
  have hEcard : Nat.card E = 4 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint C (zpowers u)
      (hzC.trans (centralizer_le_normalizer C)) hd, Nat.card_zpowers, huorder]
    change Nat.card (criticalCommutator p.a p.a') * 2 = 4
    rw [hi.critical_card]
  obtain ⟨t, ht, he⟩ := exists_edge_with_natural_plane source hb modules initial p E hEU hEcard
  obtain ⟨d, hd, hm⟩ := exists_moving_at_edge hb transfer p bad p.color_a ht
  have hescape : ¬ edgeDisplacement p.a t ≤ Q R p.a' := by
    rw [he]
    exact fun h => huQ (h (mem_sup_right (mem_zpowers u)))
  let choice : BackwardChoice p := ⟨t, d, ht, hd, hm, hescape⟩
  refine ⟨choice, ?_⟩
  change C ≤ edgeDisplacement p.a t
  rw [he]
  exact le_sup_left

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
