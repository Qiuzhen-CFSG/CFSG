module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Basic

/-!
# Geometry and the small actor in transported flag generation

For a distance-two vertex t, the common edge puts Z_t intersect Z_alpha at
index at most two in Z_t. The seed bound gives [Z_t,V₀] in U_t intersect
U_alpha. The contrary commutator bound makes this displacement a proper
subgroup of the edge displacement of order four. Evaluation outside the
fixed subgroup of Z_t therefore bounds the actual image of V₀ in G_t/Q_t
by two. All indices and centralizers retain their ambient embeddings.

These are the geometric and index steps of MS93 (4.6.8), claim (2),
printed p.906. Selecting a conjugate with displacement outside Z_alpha
still needs the source's non-single-section argument.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

/-- The two ends of a length-two path have the same vertex color. -/
theorem color_of_distance_two (a t : Vertex R) (ha : color R a = false)
    (ht : (cosetGraph R).dist t a = 2) : color R t = false := by
  obtain ⟨w, hw⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist t a
  exact ((walk_even_iff_color_eq R w).mp (by rw [hw, ht]; decide)).trans ha

/-- A common edge vertex, in the actual coset graph. -/
theorem common_edge (a t : Vertex R) (ht : (cosetGraph R).dist t a = 2) :
    ∃ b, Adjacent R t b ∧ Adjacent R a b := by
  have hd : (cosetGraph R).edist t a = 2 := by
    rw [← ((cosetGraph_connected R) t a).coe_dist_eq_edist, ht]
    rfl
  obtain ⟨b, htb, hab⟩ := (SimpleGraph.edist_eq_two_iff.mp hd).2.2
  exact ⟨b, (cosetGraph_adj R _ _).mp htb, (cosetGraph_adj R _ _).mp hab⟩

/-- Transport to t is effected by an element of the original amalgam. -/
theorem exists_base_transport (t : Vertex R) (ht : nu R geometry (alpha R) t) :
    ∃ g : FreeAmalgam R, act R g (alpha R) = t := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R
    (color_of_distance_two (alpha R) t rfl ht.1)
  exact ⟨g, by simp only [alpha, act_mVertex, one_mul]⟩

/-- Transporting the base and midpoint together preserves the ordered pair's distance. -/
theorem transported_distance (p : FlagCriticalData source geometry i)
    (g : FreeAmalgam R) (t : Vertex R) (hg : act R g (alpha R) = t) :
    (cosetGraph R).dist (act R g p.middle) t = 2 := by
  rw [← hg, dist_act, SimpleGraph.dist_comm]
  exact p.first_distance

/-- The common edge bounds the intersection index, with no equality assumed. -/
theorem intersection_index_le_two [Finite M] (early : EarlyFacts R geometry)
    (a t : Vertex R) (ha : color R a = false)
    (ht : (cosetGraph R).dist t a = 2) : (Z R a).relIndex (Z R t) ≤ 2 := by
  obtain ⟨b, htb, hab⟩ := common_edge a t ht
  have hi := early.edge_Z_index t b (color_of_distance_two a t ha ht) htb
  have hh := relIndex_le_of_le_left (Early.edge_Z_le a b ha hab)
    (show (Z R b).relIndex (Z R t) ≠ 0 by rw [hi]; decide)
  exact hh.trans_eq hi

/-- Every local displacement of Z lies in its genuine natural summand. -/
theorem local_commutator_le_U [Finite M] (common : CommonFacts R source geometry)
    (a : Vertex R) (ha : color R a = false) :
    ⁅Z R a, stabilizer R a⁆ ≤ U R a := by
  let s : BinaryNaturalStructure source :=
    ⟨common.X_eq_Z, common.natural, common.decomposition, common.disjoint⟩
  have hs := s.decomposition_at a ha
  have hh := commutator_eq_of_centralizing_sup
    ((sup_comm _ _).trans hs.symm) inf_le_right
    ((U_le_Z a).trans ((Z_le_stabilizer R a).trans (stabilizer R a).le_normalizer))
  rw [commutator_comm, ← hh]
  exact le_normalizer_iff_commutator_le_right.mp (U_normalized a)

/-- The early source seed bound controls the crossing commutator on both sides. -/
theorem crossing_commutator_le [Finite M] (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i)
    (hseed : ⁅Z R p.middle, Q R (alpha R)⁆ ≤ U R (alpha R))
    (t : Vertex R) (ht : nu R geometry (alpha R) t) :
    ⁅Z R t, midpointSpan p⁆ ≤ U R t ⊓ U R (alpha R) := by
  have htc := color_of_distance_two (alpha R) t rfl ht.1
  have hSQ := (span_le_radius p).trans (V_le_Q geometry common.large_distance _ rfl)
  have hQt : Q R (alpha R) ≤ stabilizer R t :=
    Q_le_stabilizer_of_dist_le_two (alpha R) t rfl htc
      (by rw [SimpleGraph.dist_comm]; exact ht.1.le)
  refine le_inf ((commutator_mono le_rfl (hSQ.trans hQt)).trans
    (local_commutator_le_U common t htc)) ?_
  rw [commutator_comm]
  have htQ : Z R t ≤ Q R (alpha R) :=
    (show Z R t ≤ V R (alpha R) from le_iSup_of_le t
      (le_iSup_of_le ht.1.le le_rfl)).trans (V_le_Q geometry common.large_distance _ rfl)
  exact (commutator_mono le_rfl htQ).trans (span_commutator_le_U common p hseed)

/-- The bad bound makes the crossing displacement a proper subgroup of an edge four-group. -/
theorem crossing_commutator_card_le_two [Finite M]
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (p : FlagCriticalData source geometry i)
    (hseed : ⁅Z R p.middle, Q R (alpha R)⁆ ≤ U R (alpha R))
    (t : Vertex R) (ht : nu R geometry (alpha R) t)
    (hbad : ¬ ⁅Z R t, Q R (alpha R)⁆ ≤ U R (alpha R)) :
    Nat.card (⁅Z R t, midpointSpan p⁆ : Subgroup (FreeAmalgam R)) ≤ 2 := by
  obtain ⟨b, htb, hab⟩ := common_edge (alpha R) t ht.1
  let E := ⁅Z R t, Q R b⁆
  let D := ⁅Z R t, midpointSpan p⁆
  have hE : Nat.card E = 4 :=
    early.edge_commutator_card t b (color_of_distance_two (alpha R) t rfl ht.1) htb
  let : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; decide)
  have hSQ := (span_le_radius p).trans (V_le_Q geometry common.large_distance _ rfl)
  have hQ := Q_le_adjacent_h R (by
    have h := adjacent_color_ne R hab
    cases hb : color R b <;> simp_all [show color R (alpha R) = false from rfl]) hab
  have hDE : D ≤ E := commutator_mono le_rfl (hSQ.trans hQ)
  let : Finite D := Finite.of_injective (inclusion hDE) (inclusion_injective _)
  have hDU : D ≤ U R (alpha R) := (crossing_commutator_le common p hseed t ht).trans inf_le_right
  have hne : D ≠ E := by
    intro he
    have hEU : E ≤ U R (alpha R) := by rw [← he]; exact hDU
    exact hbad ((commutator_mono le_rfl hQ).trans hEU)
  have hlt : Nat.card D < 4 := by
    by_contra! hn
    exact hne (eq_of_le_of_card_ge hDE (by rw [hE]; exact hn))
  have hd := Nat.mem_divisors.mpr ⟨hE ▸ card_dvd_of_le hDE, (by decide : 4 ≠ 0)⟩
  rw [show Nat.divisors 4 = ({1, 2, 4} : Finset ℕ) by decide] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  change Nat.card D ≤ 2
  omega

/-- The literal source index bound |V₀ Q_t / Q_t| ≤ 2. -/
theorem span_actor_index_le_two [Finite M]
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (p : FlagCriticalData source geometry i)
    (hseed : ⁅Z R p.middle, Q R (alpha R)⁆ ≤ U R (alpha R))
    (t : Vertex R) (ht : nu R geometry (alpha R) t)
    (hbad : ¬ ⁅Z R t, Q R (alpha R)⁆ ≤ U R (alpha R)) :
    (Q R t).relIndex (midpointSpan p) ≤ 2 := by
  let S := midpointSpan p
  let C := centralizer (Z R t : Set (FreeAmalgam R))
  have htc := color_of_distance_two (alpha R) t rfl ht.1
  obtain ⟨b, htb, hab⟩ := common_edge (alpha R) t ht.1
  have hSQ := (span_le_radius p).trans (V_le_Q geometry common.large_distance _ rfl)
  have hSb : S ≤ Q R b := hSQ.trans (Q_le_adjacent_h R (by
    have h := adjacent_color_ne R hab
    cases hb : color R b <;> simp_all [show color R (alpha R) = false from rfl]) hab)
  have hSC : (Q R t).subgroupOf S = C.subgroupOf S := by
    ext x
    change (x : FreeAmalgam R) ∈ Q R t ↔ (x : FreeAmalgam R) ∈ C
    rw [← common.centralizer t b htc htb]
    exact and_iff_right (hSb x.property)
  have hindex : (Q R t).relIndex S = C.relIndex S := congrArg Subgroup.index hSC
  rw [hindex]
  by_cases hz : ⁅Z R t, S⁆ = ⊥
  · have hSC' : S ≤ C := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)
    rw [relIndex_eq_one.mpr hSC']
    decide
  let := geometry.Z_elementary (lt_trans (by decide : 0 < 2) common.large_distance) t htc
  have hn : S ≤ normalizer (Z R t) :=
    (hSb.trans (fun _ hx => hx.2 t (adjacent_symm R htb))).trans (Z_normalized R t)
  have hc : ⁅Z R t, S⁆ ≤ centralizer (S : Set (FreeAmalgam R)) :=
    ((crossing_commutator_le common p hseed t ht).trans inf_le_right).trans
      ((U_le_Z (alpha R)).trans
        ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes _ rfl)).trans
          (centralizer_le hSQ)))
  have hZb : Z R b ≤ Z R t ⊓ centralizer (S : Set (FreeAmalgam R)) := by
    rw [Early.edge_Z_eq_fixed common t b htc htb]
    exact inf_le_inf_left _ (centralizer_le hSb)
  have hi := early.edge_Z_index t b htc htb
  have hle : (Z R t ⊓ centralizer (S : Set (FreeAmalgam R))).relIndex (Z R t) ≤ 2 :=
    (relIndex_le_of_le_left hZb (by rw [hi]; decide)).trans_eq hi
  have hnzero : (Z R t ⊓ centralizer (S : Set (FreeAmalgam R))).relIndex (Z R t) ≠ 0 := by
    intro h
    have hd := relIndex_dvd_of_le_left (Z R t) hZb
    rw [h, hi] at hd
    norm_num at hd
  have hneone : (Z R t ⊓ centralizer (S : Set (FreeAmalgam R))).relIndex (Z R t) ≠ 1 := by
    intro h
    exact hz (commutator_eq_bot_iff_le_centralizer.mpr ((relIndex_eq_one.mp h).trans inf_le_right))
  have htwo : (Z R t ⊓ centralizer (S : Set (FreeAmalgam R))).relIndex (Z R t) = 2 := by omega
  rw [Early.actor_index_eq_displacement_card_of_fixed_index_two (Z R t) S hn hc htwo]
  exact crossing_commutator_card_le_two common early p hseed t ht hbad

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation
