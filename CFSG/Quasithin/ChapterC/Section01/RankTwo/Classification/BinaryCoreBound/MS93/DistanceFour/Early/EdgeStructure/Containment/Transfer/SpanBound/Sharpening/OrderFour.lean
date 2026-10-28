module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.OrderTwo
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.Transfer.SpanBound.Geometry

/-!
# The order-four edge displacement before the containment theorem

The sharpening on printed p.882 uses an order-four equality, whereas the
unconditional early estimate supplies only an upper bound. In the authorized
distance-four specialization, we derive the equality from the initial facts.

Suppose the displacement has order two. It is normal in the finite edge
kernel, hence central there. Edge transitivity and radius-two generation now
give [V_alpha,Q_alpha] <= Z_alpha directly in this contrary branch. The
critical-midpoint argument from (2.3) places V_alpha' in D_alpha. Two opposite
radius groups supply an actual quotient offender, with its intrinsic Frattini
containment; the initial factorization implication contradicts the nonabelian
radius group. Nontriviality and the order-four upper bound finish the proof.

The opposite-radius calculations specialize OrderTwo.OffenderConstruction
using the order-two bound just proved here. They do not assume universal edge
containment, apply the final order-two exclusion, or use the characteristic
centralizer transfer. All finiteness remains local to vertex stabilizers.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (2.3), pp.857--859, and the argument for (4.6.5), p.903; used to justify
the edge-action step in (4.2)(i), p.882.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.Transfer.SpanBound.Sharpening
open OrderTwo

private theorem frattini_le_of_involution_generation {G : Type*} [Group G]
    (A D : Subgroup G) [Finite A] (hA : IsPGroup 2 A)
    (hgen : omegaOneAmbient A = A) (hcomm : ⁅A, A⁆ ≤ D) :
    (frattini A).map A.subtype ≤ D := by
  let N := D.subgroupOf A
  have hderived : _root_.commutator A ≤ N := by
    change _root_.commutator A ≤ D.comap A.subtype
    rw [← map_le_iff_le_comap, map_subtype_commutator]
    exact hcomm
  let : N.Normal := Subgroup.Normal.of_commutator_le A hderived
  let : IsMulCommutative (A ⧸ N) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hderived
  let q := QuotientGroup.mk' N
  let f : A →* A ⧸ N := (powMonoidHom 2).comp q
  have hker : A ≤ f.ker.map A.subtype := by
    apply hgen.ge.trans
    apply (omegaOneAmbient_le_iff _ _).mpr
    intro x hx hs
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    change q (⟨x, hx⟩ : A) ^ 2 = 1
    rw [← map_pow]
    have hs' : (⟨x, hx⟩ : A) ^ 2 = 1 := Subtype.ext hs
    rw [hs', map_one]
  have hsquare (x : A) : x ^ 2 ∈ N := by
    obtain ⟨y, hy, he⟩ := hker x.property
    have he' : y = x := Subtype.ext he
    subst y
    apply (QuotientGroup.eq_one_iff (N := N) (x := x ^ 2)).mp
    change q x ^ 2 = 1 at hy
    change q (x ^ 2) = 1
    rwa [map_pow]
  let : Fact (IsPGroup 2 A) := ⟨hA⟩
  rw [map_le_iff_le_comap, frattini_eq_closure_commutator_union_powers (p := 2)]
  apply (closure_le _).mpr
  rintro x (hx | ⟨y, rfl⟩)
  · exact hderived hx
  · exact hsquare y

private theorem commutator_join_le {G : Type*} [Group G] {ι : Sort*}
    (A : ι → Subgroup G) (Y D : Subgroup G)
    (hn : (⨆ i, A i) ≤ normalizer (D : Set G)) (hc : ∀ i, ⁅A i, Y⁆ ≤ D) :
    ⁅⨆ i, A i, Y⁆ ≤ D := by
  apply commutator_le.mpr
  intro x hx y hy
  revert y
  induction hx using iSup_induction' with
  | hp i x hx =>
      intro y hy
      exact hc i (commutator_mem_commutator hx hy)
  | h1 =>
      intro y hy
      simpa only [commutatorElement_one_left] using D.one_mem
  | hmul x z hx _ ihx ihz =>
      intro y hy
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact D.mul_mem ((mem_normalizer_iff.mp (hn hx) _).mp (ihz y hy)) (ihx y hy)

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry)

include common

private theorem radius_in_opposite_stabilizer (a c : Vertex R)
    (ha : color R a = false) (hc : color R c = false)
    (hac : (cosetGraph R).dist a c = 2) : V R c ≤ stabilizer R a := by
  obtain ⟨b, hab, hcb⟩ := exists_common_neighbor_of_dist_two R a c hac
  have hb : color R b = true := by
    have hh := adjacent_color_ne R hab
    cases hh' : color R b <;> simp_all
  exact ((radius_le_Q common c hc).trans (Q_le_adjacent_h R hb hcb)).trans
    (fun _ hx => hx.2 a (adjacent_symm R hab))

/-- In the order-two branch, relative normality alone gives centrality in
that edge kernel. This does not use the source edge-containment theorem. -/
private theorem edge_central_of_order_two
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (hcard : Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) = 2) :
    ⁅Z R a, Q R b⁆ ≤ centralizer (Q R b : Set (FreeAmalgam R)) := by
  let A := ⁅Z R a, Q R b⁆
  have hAT : A ≤ Q R b := (edge_commutator_le_natural common a b ha hab).trans
    ((U_le_Z a).trans (edge_Z_le_Q common a b ha hab))
  let : (A.subgroupOf (Q R b)).Normal := edge_normal_in_kernel a b hab
  have hc := central_of_normal_card_two (A.subgroupOf (Q R b))
    ((Nat.card_congr (subgroupOfEquivOfLe hAT).toEquiv).trans hcard)
  intro x hx t ht
  exact congrArg Subtype.val ((mem_center_iff.mp
    (hc (show (⟨x, hAT hx⟩ : Q R b) ∈ A.subgroupOf (Q R b) from hx))) ⟨t, ht⟩)

/-- The contrary order-two assumption supplies the radius-kernel bound
locally, before any use of (4.6.4). -/
private theorem radius_commutator_of_order_two
    (a₀ b₀ : Vertex R) (ha₀ : color R a₀ = false) (he₀ : Adjacent R a₀ b₀)
    (hcard : Nat.card (⁅Z R a₀, Q R b₀⁆ : Subgroup (FreeAmalgam R)) = 2)
    (a : Vertex R) (ha : color R a = false) : ⁅V R a, Q R a⁆ ≤ Z R a := by
  have hgen (t : Vertex R) (ht : (cosetGraph R).dist t a ≤ 2) :
      ⁅Z R t, Q R a⁆ ≤ Z R a := by
    have hta : (cosetGraph R).dist t a = 0 ∨
        (cosetGraph R).dist t a = 1 ∨ (cosetGraph R).dist t a = 2 := by omega
    rcases hta with hzero | hone | htwo
    · have heq : t = a := ((cosetGraph_connected R t a).dist_eq_zero_iff).mp hzero
      subst t
      rw [geometry.centralizes a ha]
      exact bot_le
    · have hat := adjacent_symm R
        ((cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp hone))
      exact (commutator_mono (edge_Z_le a t ha hat) le_rfl).trans
        (by rw [geometry.centralizes a ha]; exact bot_le)
    · obtain ⟨b, htb, hab⟩ := exists_common_neighbor_of_dist_two R t a htwo
      have hb : color R b = true := by
        have hh := adjacent_color_ne R hab
        cases hc : color R b <;> simp_all
      have htcol := neighbor_color a b t ha hab htb
      have hcardt : Nat.card (⁅Z R t, Q R b⁆ : Subgroup (FreeAmalgam R)) = 2 :=
        (edge_card_eq a₀ b₀ t b ha₀ htcol he₀ htb).symm.trans hcard
      have hfixed : ⁅Z R t, Q R b⁆ ≤ Z R b := by
        rw [edge_Z_eq_fixed common t b htcol htb]
        exact le_inf ((edge_commutator_le_natural common t b htcol htb).trans (U_le_Z t))
          (edge_central_of_order_two common t b htcol htb hcardt)
      exact (commutator_mono le_rfl (Q_le_adjacent_h R hb hab)).trans
        (hfixed.trans (edge_Z_le a b ha hab))
  have hle (t : Vertex R) : (⨆ (_ : (cosetGraph R).dist t a ≤ 2), Z R t) ≤ Q R a :=
    (le_iSup (fun t => ⨆ (_ : (cosetGraph R).dist t a ≤ 2), Z R t) t).trans
      (radius_le_Q common a ha)
  change ⁅⨆ t, ⨆ (_ : (cosetGraph R).dist t a ≤ 2), Z R t, Q R a⁆ ≤ Z R a
  rw [commutator_iSup_of_le _ _ hle]
  apply iSup_le
  intro t
  rw [commutator_iSup_of_le _ _ (fun ht =>
    (le_iSup (fun _ : (cosetGraph R).dist t a ≤ 2 => Z R t) ht).trans (hle t))]
  exact iSup_le fun ht => hgen t ht

/-- The intrinsic Frattini subgroup of a radius group is contained in its Z-layer. -/
private theorem radius_frattini_of_order_two
    (a₀ b₀ : Vertex R) (ha₀ : color R a₀ = false) (he₀ : Adjacent R a₀ b₀)
    (hcard : Nat.card (⁅Z R a₀, Q R b₀⁆ : Subgroup (FreeAmalgam R)) = 2)
    (a : Vertex R) (ha : color R a = false) :
    (frattini (V R a)).map (V R a).subtype ≤ Z R a := by
  let := finite_radius common a ha
  apply frattini_le_of_involution_generation
  · exact (Q_isPGroup R source.two_group source.core_le a ha).of_injective
      (inclusion (radius_le_Q common a ha)) (inclusion_injective _)
  · exact DistanceEight.VBall_omegaOne R a 2
  · exact (commutator_mono le_rfl (radius_le_Q common a ha)).trans
      (radius_commutator_of_order_two common a₀ b₀ ha₀ he₀ hcard a ha)

/-- The kernel intersection centralizes the opposite radius group modulo Z.
Critical generators use the genuine predecessor kernel; all other generators
use the already proved radius-kernel commutator containment. -/
private theorem crossing_commutator_of_order_two (hb : geometry.b R = 4)
    (a₀ b₀ : Vertex R) (ha₀ : color R a₀ = false) (he₀ : Adjacent R a₀ b₀)
    (hcard : Nat.card (⁅Z R a₀, Q R b₀⁆ : Subgroup (FreeAmalgam R)) = 2)
    (a c : Vertex R) (ha : color R a = false) (hc : color R c = false)
    (hac : (cosetGraph R).dist a c = 2) :
    ⁅V R a ⊓ Q R c, V R c⁆ ≤ Z R a := by
  have hVG := radius_in_opposite_stabilizer common a c ha hc hac
  have hnorm := hVG.trans (Z_normalized R a)
  have hZc : Z R c ≤ Q R a := by
    apply Z_le_Q_of_dist_lt R c (geometry.exists_critical c hc)
    rw [geometry.distance_constant c hc, SimpleGraph.dist_comm, hac]
    exact common.large_distance
  have hgen (d : Vertex R) (hd : (cosetGraph R).dist d c ≤ 2) :
      ⁅Z R d, V R a ⊓ Q R c⁆ ≤ Z R a := by
    have hdV : Z R d ≤ V R c := le_iSup_of_le d (le_iSup_of_le hd le_rfl)
    by_cases hle : Z R d ≤ Q R a
    · rw [commutator_comm]
      exact (commutator_mono inf_le_left hle).trans
        (radius_commutator_of_order_two common a₀ b₀ ha₀ he₀ hcard a ha)
    have hdcol : color R d = false := by
      by_contra hh
      have hdcol : color R d = true := by cases hh' : color R d <;> simp_all
      obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist d c
      have hodd : ¬ Even p.length := by rw [walk_even_iff_color_eq, hdcol, hc]; decide
      rw [Nat.even_iff] at hodd
      have hlen : p.length = 1 := by omega
      have hcd := adjacent_symm R ((cosetGraph_adj R _ _).mp (p.adj_of_length_eq_one hlen))
      exact hle ((edge_Z_le c d hc hcd).trans hZc)
    have hlower := criticalDistance_le R d (geometry.exists_critical d hdcol) hle
    rw [geometry.distance_constant d hdcol] at hlower
    change geometry.b R ≤ _ at hlower
    have hupper := (cosetGraph_connected R).dist_triangle (u := d) (v := c) (w := a)
    have hca : (cosetGraph R).dist c a = 2 := by simpa only [SimpleGraph.dist_comm] using hac
    have hda : (cosetGraph R).dist d a = 4 := by omega
    have hdc : (cosetGraph R).dist d c = 2 := by omega
    have hcrit : CriticalPair R d a (geometry.exists_critical d hdcol) := by
      refine ⟨?_, hle⟩
      rw [geometry.distance_constant d hdcol]
      exact hda.trans hb.symm
    have hrev := common.critical_reverse d hdcol a ha hcrit
    obtain ⟨t, hdt, hct⟩ := exists_common_neighbor_of_dist_two R d c hdc
    have ht : color R t = true := by
      have hh := adjacent_color_ne R hct
      cases hh' : color R t <;> simp_all
    have hpath : (cosetGraph R).dist a t + 1 = (cosetGraph R).dist a d := by
      have htd : (cosetGraph R).dist t d = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj R _ _).mpr (adjacent_symm R hdt))
      have hctd : (cosetGraph R).dist c t = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj R _ _).mpr hct)
      have htri := (cosetGraph_connected R).dist_triangle (u := a) (v := c) (w := t)
      have htri' := (cosetGraph_connected R).dist_triangle (u := a) (v := t) (w := d)
      have had : (cosetGraph R).dist a d = 4 := by simpa only [SimpleGraph.dist_comm] using hda
      omega
    rw [commutator_comm]
    exact (critical_predecessor_commutator_le common a₀ b₀ ha₀ he₀ hcard a d ha hrev
      t hdt hpath (V R a ⊓ Q R c) (inf_le_right.trans (Q_le_adjacent_h R ht hct))).trans
      (le_normalizer_iff_commutator_le_left.mp ((hdV.trans hVG).trans (Z_normalized R a)))
  rw [commutator_comm]
  change ⁅⨆ d, ⨆ (_ : (cosetGraph R).dist d c ≤ 2), Z R d, V R a ⊓ Q R c⁆ ≤ _
  apply commutator_join_le _ _ _ hnorm
  intro d
  apply commutator_join_le
  · exact (le_iSup (fun d => ⨆ (_ : (cosetGraph R).dist d c ≤ 2), Z R d) d).trans hnorm
  · exact hgen d

/-- The source offender is an actual opposite radius group. Comparing the two
image indices selects the orientation of the common edge. All commutator
and Frattini premises have been obtained from the contrary order-two assumption. -/
private theorem exists_offender_of_order_two (hb : geometry.b R = 4)
    (a₀ b₀ : Vertex R) (ha₀ : color R a₀ = false) (he₀ : Adjacent R a₀ b₀)
    (hcard : Nat.card (⁅Z R a₀, Q R b₀⁆ : Subgroup (FreeAmalgam R)) = 2) :
    ∃ (a b : Vertex R) (A : Subgroup (FreeAmalgam R)),
      color R a = false ∧ Adjacent R a b ∧ A ≤ Q R b ∧ ¬ A ≤ Q R a ∧
      (frattini A).map A.subtype ≤ Q R a ∧
      (radiusFixed geometry a A).relIndex (V R a) ≤ (Q R a).relIndex A := by
  obtain ⟨d, hcrit⟩ := criticalPair_exists R a₀ (geometry.exists_critical a₀ ha₀)
  have hdcol := critical_endpoint_color R a₀ ha₀ _ hcrit
  have hd : (cosetGraph R).dist a₀ d = 4 := by
    rw [hcrit.1, geometry.distance_constant a₀ ha₀]
    exact hb
  obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist a₀ d
  let c := p.getVert 2
  have hleft := SimpleGraph.dist_le (p.take 2)
  have hright := SimpleGraph.dist_le (p.drop 2)
  have hsum := (cosetGraph_connected R).dist_triangle (u := a₀) (v := c) (w := d)
  have hlen : p.length = 4 := hp.trans hd
  simp only [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length, hlen] at hleft hright
  change (cosetGraph R).dist a₀ c ≤ 2 at hleft
  change (cosetGraph R).dist c d ≤ 2 at hright
  have hac : (cosetGraph R).dist a₀ c = 2 := by omega
  have hcd : (cosetGraph R).dist c d = 2 := by omega
  obtain ⟨b, hab, hcb⟩ := exists_common_neighbor_of_dist_two R a₀ c hac
  have hbcol : color R b = true := by
    have hh := adjacent_color_ne R hab
    cases hh' : color R b <;> simp_all
  have hc : color R c = false := by
    have hh := adjacent_color_ne R hcb
    cases hh' : color R c <;> simp_all
  have hca : (cosetGraph R).dist c a₀ = 2 := by simpa only [SimpleGraph.dist_comm] using hac
  have hescape_a : ¬ V R a₀ ≤ Q R c := common.escape a₀ ha₀ d hcrit c hcd (by omega)
  have hescape_c : ¬ V R c ≤ Q R a₀ := by
    intro hh
    apply (common.critical_reverse a₀ ha₀ d hdcol hcrit).2
    have hdV : Z R d ≤ V R c :=
      le_iSup_of_le d (le_iSup_of_le
        (show (cosetGraph R).dist d c ≤ 2 by rw [SimpleGraph.dist_comm, hcd]) le_rfl)
    exact hdV.trans hh
  have hZa : Z R a₀ ≤ Q R c := by
    apply Z_le_Q_of_dist_lt R a₀ (geometry.exists_critical a₀ ha₀)
    rw [geometry.distance_constant a₀ ha₀, hac]
    exact common.large_distance
  have hZc : Z R c ≤ Q R a₀ := by
    apply Z_le_Q_of_dist_lt R c (geometry.exists_critical c hc)
    rw [geometry.distance_constant c hc, hca]
    exact common.large_distance
  rcases le_total ((Q R c).relIndex (V R a₀)) ((Q R a₀).relIndex (V R c)) with hi | hi
  · refine ⟨a₀, b, V R c, ha₀, hab,
      (radius_le_Q common c hc).trans (Q_le_adjacent_h R hbcol hcb), hescape_c,
      (radius_frattini_of_order_two common a₀ b₀ ha₀ he₀ hcard c hc).trans hZc, ?_⟩
    exact (fixed_index_le_of_commutator common a₀ c ha₀ (V R c)
      (radius_in_opposite_stabilizer common a₀ c ha₀ hc hac)
      (crossing_commutator_of_order_two common hb a₀ b₀ ha₀ he₀ hcard a₀ c ha₀ hc hac)).trans hi
  · refine ⟨c, b, V R a₀, hc, hcb,
      (radius_le_Q common a₀ ha₀).trans (Q_le_adjacent_h R hbcol hab), hescape_a,
      (radius_frattini_of_order_two common a₀ b₀ ha₀ he₀ hcard a₀ ha₀).trans hZa, ?_⟩
    exact (fixed_index_le_of_commutator common c a₀ hc (V R a₀)
      (radius_in_opposite_stabilizer common c a₀ hc ha₀ hca)
      (crossing_commutator_of_order_two common hb a₀ b₀ ha₀ he₀ hcard c a₀ hc ha₀ hca)).trans hi

/-- The source order-four equality follows from the initial distance-four
facts. In the order-two branch normality supplies centrality directly; the
critical-midpoint and opposite-radius offender argument gives a contradiction.
No universal edge-containment premise or final order-two exclusion is used. -/
theorem edge_displacement_card_four (hb : geometry.b R = 4)
    (initial : InitialFacts R geometry)
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b) :
    Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) = 4 := by
  have htwo : Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) ≠ 2 := by
    intro hcard
    have hfixed := derived_le_fixedCore_of_order_two common hb a b ha hab hcard
    obtain ⟨c, d, A, hc, hcd, hA, hnot, hPhi, hi⟩ :=
      exists_offender_of_order_two common hb a b ha hab hcard
    exact not_offender_of_derived_fixed common hb initial c d hc hcd (hfixed c hc)
      A hA hnot hPhi hi
  let : Finite (U R a) := Nat.finite_of_card_ne_zero
    (by rw [common.natural.card_at a ha]; decide)
  have hU := edge_commutator_le_natural common a b ha hab
  let : Finite (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hU) (inclusion_injective _)
  have hdvd := card_dvd_of_le hU
  rw [common.natural.card_at a ha] at hdvd
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have hsmall := edge_displacement_card_le_four common a b ha hab
  have hlarge := (one_lt_card_iff_ne_bot _).mpr (edge_commutator_ne_bot common a b ha hab)
  omega
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.Transfer.SpanBound.Sharpening
