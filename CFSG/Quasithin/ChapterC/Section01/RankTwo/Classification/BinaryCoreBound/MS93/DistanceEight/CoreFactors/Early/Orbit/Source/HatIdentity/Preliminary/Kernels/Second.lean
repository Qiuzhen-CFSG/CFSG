module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Algebra

/-!
# The second D containment in MS93 (4.5.3)(i)

At a moving pair, the intersection of one natural eight-group with the
other Z-layer has order at most four and contains the other's H of order
four. Its intersection with the other natural group is therefore trivial,
since H is locally central and the natural group has no fixed vectors.
Along the supplied path this gives H_b ∩ H_d = 1. The span commutator
estimate and D ≤ Q_d then make D centralize Z_e; the literal edge
centralizer equality gives D ≤ Q_e. Both forward and reflected applications
retain the original path. The first D containment remains an explicit input.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), claim (2), p.897.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Kernels
open PathCentrality NormalizerTransfer
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- At a moving pair the two natural subgroups have trivial intersection. -/
theorem moving_U_inf_eq_bot
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hmove : a ∈ Escape.movingNeighbors geometry c) :
    U R a ⊓ U R c = ⊥ := by
  let K := U R a ⊓ Z R c
  have hHU : H R c ≤ U R a := Orbit.H_le_neighbor_U common earlier hc hmove
  have hHZ := H_le_Z_of_central common hc (earlier.centrality c hc)
  have hHK : H R c ≤ K := le_inf hHU hHZ
  let : Finite (U R a) := Nat.finite_of_card_ne_zero (by rw [common.natural.card_at a ha]; decide)
  let : Finite K := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hproper : K ≠ U R a := by
    intro heq
    have hUZ : U R a ≤ Z R c := heq ▸ (show K ≤ Z R c from inf_le_right)
    have hQa : Q R c ≤ stabilizer R a := Q_le_stabilizer_of_dist_two R c a hc hmove.1
    have hcent : Z R a ≤ centralizer (Q R c : Set (FreeAmalgam R)) := by
      rw [(LocalCommutator.naturalStructure common).decomposition_at a ha]
      exact sup_le
        (hUZ.trans (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R c hc)))
        (inf_le_right.trans (centralizer_le hQa))
    have hzero : H R c = ⊥ := le_bot_iff.mp
      ((Orbit.H_le_displacement common earlier hc hmove).trans
        (commutator_eq_bot_iff_le_centralizer.mpr hcent).le)
    have hfour := First.Layer.H_card_lower common earlier c hc
    rw [hzero, card_bot] at hfour
    omega
  have hKcard : Nat.card K ≤ 4 := by
    have hlt : Nat.card K < 8 := by
      by_contra! h
      exact hproper (eq_of_le_of_card_ge inf_le_left (by rwa [common.natural.card_at a ha]))
    have hdiv := Nat.mem_divisors.mpr
      ⟨(common.natural.card_at a ha) ▸ card_dvd_of_le (show K ≤ U R a from inf_le_left),
        (by decide : 8 ≠ 0)⟩
    rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
    omega
  have hKH : K = H R c :=
    (eq_of_le_of_card_ge hHK (hKcard.trans (First.Layer.H_card_lower common earlier c hc))).symm
  apply le_bot_iff.mp
  rw [← Escape.EdgeTransfer.U_fixed_eq_bot (LocalCommutator.moduleFacts common) c hc]
  apply le_inf inf_le_right
  have hH : U R a ⊓ U R c ≤ H R c := by
    rw [← hKH]
    exact inf_le_inf_left _ (U_le_Z R c)
  intro x hx l hl
  obtain ⟨z, hz, rfl⟩ := H_le_localCenter_of_central R c (earlier.centrality c hc) (hH hx)
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨l, Ltilde_le_stabilizer c hl⟩)

/-- The two H-layers in claim (2) have trivial intersection along the moving chain. -/
theorem H_inf_eq_bot_of_moving_chain
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b c d : Vertex R} (ha : color R a = false) (hb : color R b = false)
    (hc : color R c = false) (hd : color R d = false)
    (hba : a ∈ Escape.movingNeighbors geometry b)
    (hca : a ∈ Escape.movingNeighbors geometry c)
    (hdc : c ∈ Escape.movingNeighbors geometry d) : H R b ⊓ H R d = ⊥ := by
  apply le_bot_iff.mp
  rw [← moving_U_inf_eq_bot common earlier ha hc hca]
  exact inf_le_inf (Orbit.H_le_neighbor_U common earlier hb hba)
    (Orbit.H_le_neighbor_U common earlier hd hdc)

/-- Claim (2): the first kernel bound and the printed span commutator force
centralization of the endpoint Z-layer, and the literal edge detects its kernel. -/
theorem span_le_six_of_le_four
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b c d e t s : Vertex R}
    (ha : color R a = false) (hb : color R b = false) (hc : color R c = false)
    (hd : color R d = false) (he : color R e = false)
    (hba : a ∈ Escape.movingNeighbors geometry b)
    (hca : a ∈ Escape.movingNeighbors geometry c)
    (hdc : c ∈ Escape.movingNeighbors geometry d)
    (hde : e ∈ Escape.movingNeighbors geometry d)
    (hds : Adjacent R d s) (hes : Adjacent R e s)
    (hZe : Z R e ≤ Q R a)
    (hsmall : ⁅normalizerSpan R a b t, Q R a⁆ ≤ H R b)
    (hfour : normalizerSpan R a b t ≤ Q R d) :
    normalizerSpan R a b t ≤ Q R e := by
  have hs : color R s = true := by
    have hn := adjacent_color_ne R hds
    cases h : color R s <;> simp_all
  have hedge := moving_edge_displacement_eq_H common earlier he hd hes hds hde
  have hzero : ⁅normalizerSpan R a b t, Z R e⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← H_inf_eq_bot_of_moving_chain common earlier ha hb hc hd hba hca hdc]
    refine le_inf ((commutator_mono le_rfl hZe).trans hsmall) ?_
    rw [commutator_comm]
    exact (commutator_mono le_rfl (hfour.trans (Q_le_adjacent_h R hs hds))).trans hedge.le
  rw [← common.centralizer e s he hes]
  exact le_inf (hfour.trans (Q_le_adjacent_h R hs hds))
    (commutator_eq_bot_iff_le_centralizer.mp hzero)

/-- Claim (2) at both forward configurations of the supplied source path. -/
theorem forward_six_of_four
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ} (hi : Even i) (hi4 : 4 ≤ i) (hi6 : i ≤ 6)
    (seed : SeedEstimates R (p.walk.getVert i) (p.walk.getVert (i - 2))
      (p.walk.getVert (i - 1)))
    (hfour : normalizerSpan R (p.walk.getVert i) (p.walk.getVert (i - 2))
      (p.walk.getVert (i - 1)) ≤ Q R (p.walk.getVert (i + 4))) :
    normalizerSpan R (p.walk.getVert i) (p.walk.getVert (i - 2))
      (p.walk.getVert (i - 1)) ≤ Q R (p.walk.getVert (i + 6)) := by
  have hib : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
  have hic : Even (i + 2) := hi.add (by decide)
  have hid : Even (i + 4) := hi.add (by decide)
  have hie : Even (i + 6) := hi.add (by decide)
  apply span_le_six_of_le_four common earlier
    (c := p.walk.getVert (i + 2)) (s := p.walk.getVert (i + 5))
    (p.even_color hi (by omega)) (p.even_color hib (by omega))
    (p.even_color hic (by omega)) (p.even_color hid (by omega))
    (p.even_color hie (by omega))
  · simpa only [Nat.sub_add_cancel (by omega : 2 ≤ i)] using
      (p.moving_neighbors source common earlier hib (by omega) (by omega)).2
  · simpa only [Nat.add_sub_cancel] using
      (p.moving_neighbors source common earlier hic (by omega) (by omega)).1
  · simpa only [show i + 4 - 2 = i + 2 by omega] using
      (p.moving_neighbors source common earlier hid (by omega) (by omega)).1
  · simpa only [Nat.add_assoc] using
      (p.moving_neighbors source common earlier hid (by omega) (by omega)).2
  · simpa only [Nat.add_assoc] using p.adjacent (i := i + 4) (by omega)
  · exact adjacent_symm R (by
      simpa only [Nat.add_assoc] using p.adjacent (i := i + 5) (by omega))
  · apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ (p.even_color hie (by omega)))
    rw [geometry.distance_constant _ (p.even_color hie (by omega))]
    change _ < geometry.b R
    rw [earlier.distance, SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]
    omega
  · exact seed.span_commutator
  · exact hfour

/-- Claim (2) at both reflected configurations, on the original walk. -/
theorem backward_six_of_four
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ} (hi : Even i) (hi8 : 8 ≤ i) (hi10 : i ≤ 10)
    (seed : SeedEstimates R (p.walk.getVert i) (p.walk.getVert (i + 2))
      (p.walk.getVert (i + 1)))
    (hfour : normalizerSpan R (p.walk.getVert i) (p.walk.getVert (i + 2))
      (p.walk.getVert (i + 1)) ≤ Q R (p.walk.getVert (i - 4))) :
    normalizerSpan R (p.walk.getVert i) (p.walk.getVert (i + 2))
      (p.walk.getVert (i + 1)) ≤ Q R (p.walk.getVert (i - 6)) := by
  have hib : Even (i + 2) := hi.add (by decide)
  have hic : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
  have hid : Even (i - 4) := by rw [Nat.even_iff] at hi ⊢; omega
  have hie : Even (i - 6) := by rw [Nat.even_iff] at hi ⊢; omega
  apply span_le_six_of_le_four common earlier
    (c := p.walk.getVert (i - 2)) (s := p.walk.getVert (i - 5))
    (p.even_color hi (by omega)) (p.even_color hib (by omega))
    (p.even_color hic (by omega)) (p.even_color hid (by omega))
    (p.even_color hie (by omega))
  · simpa only [Nat.add_sub_cancel] using
      (p.moving_neighbors source common earlier hib (by omega) (by omega)).1
  · simpa only [Nat.sub_add_cancel (by omega : 2 ≤ i)] using
      (p.moving_neighbors source common earlier hic (by omega) (by omega)).2
  · simpa only [show i - 4 + 2 = i - 2 by omega] using
      (p.moving_neighbors source common earlier hid (by omega) (by omega)).2
  · simpa only [Nat.sub_sub] using
      (p.moving_neighbors source common earlier hid (by omega) (by omega)).1
  · exact adjacent_symm R (by
      simpa only [show i - 5 + 1 = i - 4 by omega] using p.adjacent (i := i - 5) (by omega))
  · simpa only [show i - 6 + 1 = i - 5 by omega] using
      p.adjacent (i := i - 6) (by omega)
  · apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ (p.even_color hie (by omega)))
    rw [geometry.distance_constant _ (p.even_color hie (by omega))]
    change _ < geometry.b R
    rw [earlier.distance, p.distance (geometry := geometry) (by omega) (by omega)]
    omega
  · exact seed.span_commutator
  · exact hfour

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Kernels
