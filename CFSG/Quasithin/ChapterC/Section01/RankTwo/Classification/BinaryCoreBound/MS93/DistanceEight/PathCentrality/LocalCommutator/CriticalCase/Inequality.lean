module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Geometry

/-!
# The binary containment in MS93 (4.4.1), claim (3)

For a backward witness from claim (2), put d = alpha-2 and v = alpha'-2.
The source asserts [Z_d,V_v cap Q_c] <= [Z_d,Z_v]. We prove equality in
the binary specialization. The right side has order two. The middle group
lies between it and [Z_d,Q_c], which has order at most four. It also lies
in V_v, so the witness's nontrivial triple commutator prevents it from
being the entire displacement. Lagrange's theorem forces equality.

The order-two calculation uses the actual marked natural U and the proved
elementary-eight pairing, as in CriticalModules. The conclusion for a
neighboring lambda is the containment used just before (2.1)(vi) on p.892.
Existence of the backward witness and the terminal contradiction remain
separate obligations; no later conclusion of (4.4) is used.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.5)(ii), pp.869--870, and (4.4.1), claim (3), p.892.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
variable {M : Type*} [Group M] {L R : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R}

private theorem middle_eq_of_small_overgroup {G : Type*} [Group G]
    (D H E : Subgroup G) [Finite E]
    (hDH : D ≤ H) (hHE : H ≤ E) (hD : Nat.card D = 2)
    (hE : Nat.card E ≤ 4) (hne : H ≠ E) : H = D := by
  let : Finite H := Finite.of_injective (inclusion hHE) (inclusion_injective hHE)
  have hlt : Nat.card H < Nat.card E := by
    by_contra h
    exact hne (eq_of_le_of_card_ge hHE (by omega))
  have hdvd : 2 ∣ Nat.card H := hD ▸ card_dvd_of_le hDH
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hcard : Nat.card H = 2 := by omega
  exact (eq_of_le_of_card_ge hDH (by omega)).symm

/-- The actual binary natural marking forces every critical Z-commutator to have order two. -/
theorem critical_commutator_card [Finite M] (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') :
    Nat.card (⁅Z R a, Z R a'⁆ : Subgroup (FreeAmalgam R)) = 2 := by
  let s := naturalStructure common
  rw [s.critical_commutator_eq geometry a p.start_color a' p.critical]
  let : Finite (U R a) := Nat.finite_of_card_ne_zero
    (by rw [s.natural.card_at a p.start_color]; decide)
  let : Finite (U R a') := Nat.finite_of_card_ne_zero
    (by rw [s.natural.card_at a' p.end_color]; decide)
  let := geometry.U_elementary (by have := common.large_distance; omega) a p.start_color
  let := geometry.U_elementary (by have := common.large_distance; omega) a' p.end_color
  obtain ⟨hn, hn'⟩ := source.critical_U_mutually_normalize geometry a p.start_color a' p.critical
  exact card_commutator_eq_two_of_elementary_eight _ _
    (s.natural.card_at a p.start_color) (s.natural.card_at a' p.end_color) hn hn'
    (s.critical_U_noncommutation geometry a p.start_color a' p.critical)

/-- Claim (3), strengthened to equality in the binary case; the claim (2) witness remains explicit. -/
theorem source_claim_three [Finite M] (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c) :
    ⁅Z R w.backward, V R w.predecessor ⊓ Q R c⁆ =
      ⁅Z R w.backward, Z R w.predecessor⁆ := by
  let D := ⁅Z R w.backward, Z R w.predecessor⁆
  let H := ⁅Z R w.backward, V R w.predecessor ⊓ Q R c⁆
  let E := ⁅Z R w.backward, Q R c⁆
  have hHE : H ≤ E := commutator_mono le_rfl inf_le_right
  have hDH : D ≤ H := commutator_mono le_rfl
    (le_inf (Z_le_VBall R w.predecessor 2) (w.predecessor_Z_le_center_kernel (by omega)))
  have hD : Nat.card D = 2 := critical_commutator_card common (w.shifted ha (by omega))
  have hE : Nat.card E ≤ 4 := displacement_card_le_four common
    (w.backward_color ha) (w.backward_distance hd)
  have hEStab : E ≤ stabilizer R w.backward :=
    (displacement_le_U common (w.backward_color ha) (w.backward_distance hd)).trans
      ((U_le_Z R _).trans (Z_le_stabilizer R _))
  let := finite_stabilizer R w.backward
  let : Finite E := Finite.of_injective (inclusion hEStab) (inclusion_injective hEStab)
  have hHV : H ≤ V R w.predecessor := by
    apply (commutator_mono le_rfl inf_le_left).trans
    apply le_normalizer_iff_commutator_le_right.mp
    exact ((w.shifted ha (by omega)).reverse common).endpoint_Z_le_start_stabilizer
      (by omega) |>.trans (DistanceEight.V_normalized R _)
  exact middle_eq_of_small_overgroup D H E hDH hHE hD hE (by
    intro h
    exact w.displacement_not_le_predecessor_V hb (h.ge.trans hHV))

/-- The neighboring intersection bound used immediately before (2.1)(vi) on p.892. -/
theorem neighboring_intersection_commutator_le [Finite M]
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    {lam : Vertex R} (hlam : (cosetGraph R).dist lam w.predecessor ≤ 2) :
    ⁅Z R lam ⊓ Q R c, Z R w.backward⁆ ≤ Z R w.predecessor := by
  rw [commutator_comm]
  have hZV : Z R lam ≤ V R w.predecessor :=
    le_iSup_of_le lam (le_iSup_of_le hlam le_rfl)
  apply (commutator_mono le_rfl (inf_le_inf_right _ hZV)).trans
  rw [source_claim_three common hb ha hd w]
  exact le_normalizer_iff_commutator_le_right.mp
    (((w.shifted ha (by omega)).reverse common).endpoint_Z_le_start_stabilizer
      (by omega) |>.trans (Z_normalized R _))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
