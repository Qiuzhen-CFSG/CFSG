module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Kernel.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Ball
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.IndexTwo

/-!
# The six literal product bounds in MS93 (4.5.1)(ii)

Write K = V_a ∩ Q_e and R₂ = [K,Z_f], where d,e,f are four, six
and eight steps from a. The turn at e gives Z_f ≤ Vcirc_e Z_d,
so R₂ ≤ H_e. Moving generation from the genuine section in `Earlier`
puts H_e in U_d, and centrality puts it in the intervening edge Z-layer.

The radius-four group W at a centralizes V_a and lies in the preceding
edge kernel Q_s, but W is not contained in Q_d. Since Z_s has index two
in Z_d, this nontrivial subaction has fixed subgroup exactly Z_s.
Consequently R₂ lies in both distinct edge Z-layers at d. Their intersection
in U_d has order at most two. This is the contrapositive form of the
printed displacement-plane/radius-four contradiction.

At f, evaluation outside the edge fixed hyperplane identifies the faithful
K-action with R₂. Thus K/(K ∩ Q_f) has at most two elements. The critical
Z_a lies in K and escapes Q_f, so its elements represent every coset.
This gives the literal setwise product Z_a Q_f, without replacing it by a
subgroup join. The argument applies to all six requested path centers.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.5.1)(ii), printed pp.895--896.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First.Kernel.Product
open PathCentrality PathCentrality.LocalCommutator
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem eq_of_index_two {G : Type*} [Group G] {N F U : Subgroup G}
    (hNF : N ≤ F) (hFU : F ≤ U) (hi : N.relIndex U = 2) (hne : F ≠ U) : F = N := by
  have hm := relIndex_mul_relIndex N F U hNF hFU
  rw [hi] at hm
  have hdiv : F.relIndex U ∣ 2 := ⟨N.relIndex F, by simpa only [Nat.mul_comm] using hm.symm⟩
  have hidx : F.relIndex U = 2 := ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left
    (fun h => hne (le_antisymm hFU (relIndex_eq_one.mp h)))
  rw [hidx] at hm
  exact le_antisymm (relIndex_eq_one.mp (by omega)) hNF

private theorem product_of_small_index {G : Type*} [Group G] {Z K Q : Subgroup G}
    [Finite K] (hZK : Z ≤ K) (hn : ¬ Z ≤ Q) (hi : Q.relIndex K ≤ 2) :
    (K : Set G) ⊆ (Z : Set G) * (Q : Set G) := by
  have hpos : 0 < Q.relIndex K := Nat.pos_of_ne_zero (index_ne_zero_of_finite (H := Q.subgroupOf K))
  have hone : Q.relIndex K ≠ 1 := fun h => hn (hZK.trans (relIndex_eq_one.mp h))
  have htwo : Q.relIndex K = 2 := by omega
  obtain ⟨z, hz, hzQ⟩ := SetLike.not_le_iff_exists.mp hn
  intro x hx
  by_cases hxQ : x ∈ Q
  · exact ⟨1, Z.one_mem, x, hxQ, one_mul x⟩
  have hmem : z⁻¹ * x ∈ Q := by
    exact (Q.subgroupOf K).mul_mem_iff_of_index_two htwo
      (a := ⟨z⁻¹, K.inv_mem (hZK hz)⟩) (b := ⟨x, hx⟩) |>.mpr
      (by change z⁻¹ ∈ Q ↔ x ∈ Q; simp only [Q.inv_mem_iff, hzQ, hxQ])
  exact ⟨z, hz, z⁻¹ * x, hmem, mul_inv_cancel_left z x⟩

omit [Finite M] in
private theorem H_normalized (a : Vertex R) :
    stabilizer R a ≤ normalizer (H R a : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (⁅Vcirc R a, Q R a⁆ : Subgroup (FreeAmalgam R)).map _ = _
  rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (Vcirc_normalized a hg),
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized R a hg)]
  rfl

/-- The orbit of a two-step Z-layer lies in its product with the moving radius group. -/
private theorem span_le_moving_sup (source : LocalSource L R) {d e : Vertex R}
    (he : color R e = false) (hde : (cosetGraph R).dist d e = 2) :
    hatV R e d ≤ Vcirc R e ⊔ Z R d := by
  let C := Vcirc R e ⊔ Z R d
  have hn : stabilizer R e ≤ normalizer (C : Set (FreeAmalgam R)) := by
    rw [← source.local_generation e he]
    refine sup_le ?_ ?_
    · exact Escape.Initial.Consequences.normalizes_sup_of_commutator_le _ _ _
        ((Ltilde_le_stabilizer e).trans (Vcirc_normalized e))
        (commutator_mono (le_iSup_of_le d (le_iSup_of_le hde.le le_rfl)) le_rfl)
    · exact (le_inf
        ((show Q R e ≤ stabilizer R e from fun _ hx => hx.1).trans (Vcirc_normalized e))
        ((Q_le_stabilizer_of_dist_two R e d he (by rwa [SimpleGraph.dist_comm])).trans
          (Z_normalized R d))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  change localZSpan R d e ≤ C
  rw [localZSpan_eq_conjugates]
  apply iSup_le
  intro g
  exact (map_mono (show Z R d ≤ C from le_sup_right)).trans
    (mem_normalizer_iff_map_conj_eq.mp (hn ((stabilizer R e).inv_mem g.property))).le

/-- The turn identifies the source endpoint with a conjugate in the preceding span. -/
private theorem endpoint_le_moving_sup (source : LocalSource L R) {d e f : Vertex R}
    (he : color R e = false) (hde : (cosetGraph R).dist d e = 2)
    (hturn : ∃ g ∈ stabilizer R e, act R g f = d) : Z R f ≤ Vcirc R e ⊔ Z R d := by
  obtain ⟨g, hg, hgf⟩ := hturn
  have hf : f = act R g⁻¹ d := by rw [← hgf, ← act_mul, mul_inv_cancel, act_one]
  have hspan : Z R f ≤ localZSpan R d e := by
    rw [hf, Z_act, localZSpan_eq_conjugates]
    simpa only [inv_inv] using
      (le_iSup (fun h : stabilizer R e => (Z R d).map (MulAut.conj (h : FreeAmalgam R)⁻¹).toMonoidHom)
        ⟨g⁻¹, (stabilizer R e).inv_mem hg⟩)
  exact hspan.trans (span_le_moving_sup source he hde)

/-- The printed R₂ estimate uses the actual turn and the preceding kernel. -/
private theorem commutator_le_H (source : LocalSource L R) (earlier : Earlier R geometry)
    {a d e f : Vertex R} (ha : color R a = false) (hd : color R d = false)
    (he : color R e = false) (hda : (cosetGraph R).dist d a = 4)
    (hde : (cosetGraph R).dist d e = 2)
    (hturn : ∃ g ∈ stabilizer R e, act R g f = d) :
    ⁅V R a ⊓ Q R e, Z R f⁆ ≤ H R e := by
  have hVQ : V R a ≤ Q R d := V_le_Q_of_dist_add_two_lt R ha
    (by rw [SimpleGraph.dist_comm, hda, earlier.distance]; decide)
  have hZQ : Z R d ≤ Q R e := by
    apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hd)
    rw [geometry.distance_constant d hd, hde]
    change 2 < geometry.b R
    rw [earlier.distance]
    decide
  have hc : ⁅Z R d, V R a ⊓ Q R e⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes d hd)).trans
        (centralizer_le (inf_le_left.trans hVQ)))
  have hpre : Vcirc R e ⊔ Z R d ≤ commutatorPreimage (Q R e) (V R a ⊓ Q R e) (H R e) :=
    sup_le
      (le_commutatorPreimage ((DistanceEight.Vcirc_le_V R e).trans
        (geometry.V_le_Q (by rw [earlier.distance]; decide) e he))
        (commutator_mono le_rfl inf_le_right))
      (le_commutatorPreimage hZQ (hc.le.trans bot_le))
  rw [commutator_comm]
  exact (commutator_mono ((endpoint_le_moving_sup source he hde hturn).trans hpre) le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _
      ((show Q R e ≤ stabilizer R e from fun _ hx => hx.1).trans (H_normalized e)))

omit [Finite M] in
/-- The radius-two and radius-four groups at the same center commute when b=8. -/
private theorem radius_centralizes_ball (earlier : Earlier R geometry) {a : Vertex R}
    (ha : color R a = false) : V R a ≤ centralizer (VBall R a 4 : Set (FreeAmalgam R)) := by
  apply le_centralizer_iff.mp
  apply (Escape.Propagation.RadiusFour.Forward.VBall_le_iff ha _).mpr
  intro d hd hda
  apply (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes d hd)).trans
  apply centralizer_le
  apply V_le_Q_of_dist_add_two_lt R ha
  rw [SimpleGraph.dist_comm]
  rw [earlier.distance]
  omega

/-- A nontrivial subaction of an edge kernel has exactly its fixed hyperplane. -/
private theorem fixed_eq_edge (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {d s : Vertex R} (hd : color R d = false) (hds : Adjacent R d s)
    {P : Subgroup (FreeAmalgam R)} (hP : P ≤ Q R s) (hn : ¬ P ≤ Q R d) :
    Z R d ⊓ centralizer (P : Set (FreeAmalgam R)) = Z R s := by
  have heq := Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance (moduleFacts common) d s hd hds
  apply eq_of_index_two
    (show Z R s ≤ Z R d ⊓ centralizer (P : Set (FreeAmalgam R)) from
      heq ▸ le_inf inf_le_left (inf_le_right.trans (centralizer_le hP))) inf_le_left
    (earlier.edge_Z_index d s hd hds)
  intro h
  apply hn
  rw [← common.centralizer d s hd hds]
  refine le_inf hP (le_centralizer_iff.mp ?_)
  exact (show Z R d ≤ Z R d ⊓ centralizer (P : Set (FreeAmalgam R)) from h.ge).trans inf_le_right

/-- The intervening H lies in two distinct edge planes, so R₂ has order at most two. -/
private theorem commutator_card_le_two (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a d e f s t : Vertex R} (ha : color R a = false) (hd : color R d = false)
    (he : color R e = false) (hf : color R f = false)
    (hda : (cosetGraph R).dist d a = 4) (hde : (cosetGraph R).dist d e = 2)
    (has : (cosetGraph R).dist a s = 3) (hfa : (cosetGraph R).dist f a = 8)
    (hds : Adjacent R d s) (hdt : Adjacent R d t) (het : Adjacent R e t)
    (hturn : ∃ g ∈ stabilizer R e, act R g f = d)
    (hspan : Vcirc R e ≤ hatV R e d) (hne : Z R s ≠ Z R t)
    (hball : ¬ VBall R a 4 ≤ Q R d) :
    Nat.card (⁅V R a ⊓ Q R e, Z R f⁆ : Subgroup (FreeAmalgam R)) ≤ 2 := by
  let D := ⁅V R a ⊓ Q R e, Z R f⁆
  have hDH : D ≤ H R e := commutator_le_H source earlier ha hd he hda hde hturn
  have hDU : D ≤ U R d := hDH.trans (H_le_neighbor_U common earlier he hde hspan)
  have hWQ : VBall R a 4 ≤ Q R s := by
    apply (Escape.Propagation.RadiusFour.Forward.VBall_le_iff ha _).mpr
    intro x hx hxa
    apply Z_le_Q_of_dist_lt R x (geometry.exists_critical x hx)
    rw [geometry.distance_constant x hx]
    change (cosetGraph R).dist x s < geometry.b R
    have ht := (cosetGraph_connected R).dist_triangle (u := x) (v := a) (w := s)
    rw [earlier.distance]
    omega
  have hDV : D ≤ V R a := by
    apply (commutator_mono inf_le_left le_rfl).trans
    apply le_normalizer_iff_commutator_le_left.mp
    apply (geometry.Z_le_stabilizer_of_dist_le_b f hf a ?_).trans (V_normalized R a)
    rw [hfa, earlier.distance]
  have hDs : D ≤ Z R s := by
    rw [← fixed_eq_edge common earlier hd hds hWQ hball]
    exact le_inf (hDU.trans (U_le_Z R d)) (hDV.trans (radius_centralizes_ball earlier ha))
  have hDt : D ≤ Z R t := hDH.trans (H_le_edge_Z common earlier he het)
  let E := U R d ⊓ Z R s ⊓ Z R t
  have hDE : D ≤ E := le_inf (le_inf hDU hDs) hDt
  let : Finite (U R d) := Nat.finite_of_card_ne_zero (by rw [common.natural.card_at d hd]; decide)
  let : Finite E := Finite.of_injective (inclusion (show E ≤ U R d from inf_le_left.trans inf_le_left))
    (inclusion_injective _)
  exact (card_le_of_le hDE).trans (edge_natural_intersection_card_le_two common earlier hd hds hdt hne)

/-- A small R₂ image gives the literal product, using the actual endpoint kernel. -/
private theorem product_of_small_commutator (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a e f u : Vertex R}
    (ha : color R a = false) (hf : color R f = false) (hfu : Adjacent R f u)
    (hae : (cosetGraph R).dist a e = 6)
    (hKQ : V R a ⊓ Q R e ≤ Q R u) (hcrit : ¬ Z R a ≤ Q R f)
    (hsmall : Nat.card (⁅V R a ⊓ Q R e, Z R f⁆ : Subgroup (FreeAmalgam R)) ≤ 2) :
    (V R a ⊓ Q R e : Set (FreeAmalgam R)) ⊆
      (Z R a : Set (FreeAmalgam R)) * (Q R f : Set (FreeAmalgam R)) := by
  let K := V R a ⊓ Q R e
  have hZK : Z R a ≤ K := by
    apply le_inf (Z_le_VBall R a 2)
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a ha)
    rw [geometry.distance_constant a ha, hae]
    change 6 < geometry.b R
    rw [earlier.distance]
    decide
  have hn : ¬ K ≤ Q R f := fun h => hcrit (hZK.trans h)
  have hfix := fixed_eq_edge common earlier hf hfu hKQ hn
  have hi : (Z R f ⊓ centralizer (K : Set (FreeAmalgam R))).relIndex (Z R f) = 2 := by
    rw [hfix]
    exact earlier.edge_Z_index f u hf hfu
  have hnorm : K ≤ normalizer (Z R f : Set (FreeAmalgam R)) :=
    (hKQ.trans (show Q R u ≤ stabilizer R f from fun _ hx => hx.2 f (adjacent_symm R hfu))).trans
      (Z_normalized R f)
  have hF : K ≤ normalizer (Z R f ⊓ centralizer (K : Set (FreeAmalgam R)) : Set (FreeAmalgam R)) :=
    (le_centralizer_iff.mp (show Z R f ⊓ centralizer (K : Set (FreeAmalgam R)) ≤
      centralizer (K : Set (FreeAmalgam R)) from inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)
  have hcomm := commutator_le_of_normalized_index_two _ _ K inf_le_left hi hnorm hF
  let := geometry.Z_elementary (by rw [earlier.distance]; decide) f hf
  have hindex := DistanceFour.Early.actor_index_eq_displacement_card_of_fixed_index_two
    (Z R f) K hnorm (hcomm.trans inf_le_right) hi
  have hker : (centralizer (Z R f : Set (FreeAmalgam R))).subgroupOf K = (Q R f).subgroupOf K := by
    ext x
    change (x : FreeAmalgam R) ∈ centralizer (Z R f : Set (FreeAmalgam R)) ↔ (x : FreeAmalgam R) ∈ Q R f
    constructor
    · intro hx
      rw [← common.centralizer f u hf hfu]
      exact ⟨hKQ x.property, hx⟩
    · intro hx
      exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes f hf)) hx
  have hidx : (Q R f).relIndex K ≤ 2 := by
    change ((Q R f).subgroupOf K).index ≤ 2
    rw [← hker]
    change (centralizer (Z R f : Set (FreeAmalgam R))).relIndex K ≤ 2
    rw [hindex, commutator_comm]
    exact hsmall
  let := finite_stabilizer R a
  let : Finite K := Finite.of_injective (inclusion (inf_le_left.trans
    ((geometry.V_le_Q (by rw [earlier.distance]; decide) a ha).trans (fun _ hx => hx.1))))
    (inclusion_injective _)
  exact product_of_small_index hZK hcrit hidx

private theorem forward_product (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ}
    (hi : Even i) (hi2 : 2 ≤ i) (hi6 : i ≤ 6) :
    (V R (p.walk.getVert i) ⊓ Q R (p.walk.getVert (i + 6)) : Set (FreeAmalgam R)) ⊆
      (Z R (p.walk.getVert i) : Set (FreeAmalgam R)) *
        (Q R (p.walk.getVert (i + 8)) : Set (FreeAmalgam R)) := by
  have hc := p.even_color hi (by omega)
  have hd := p.even_color (hi.add (by decide : Even 4)) (by omega)
  have he := p.even_color (hi.add (by decide : Even 6)) (by omega)
  have hf := p.even_color (hi.add (by decide : Even 8)) (by omega)
  have heu : Adjacent R (p.walk.getVert (i + 6)) (p.walk.getVert (i + 7)) := by
    simpa only [Nat.add_assoc] using p.adjacent (i := i + 6) (by omega)
  have hfu : Adjacent R (p.walk.getVert (i + 8)) (p.walk.getVert (i + 7)) := by
    exact adjacent_symm R (by simpa only [Nat.add_assoc] using p.adjacent (i := i + 7) (by omega))
  have hu : color R (p.walk.getVert (i + 7)) = true := by
    have hn := adjacent_color_ne R heu
    cases h : color R (p.walk.getVert (i + 7)) <;> simp_all
  apply product_of_small_commutator common earlier hc hf hfu
    (by rw [p.distance (geometry := geometry) (by omega) (by omega)]; omega)
    (inf_le_right.trans (Q_le_adjacent_h R hu heu)) (p.critical i hi hi6).2
  apply commutator_card_le_two source common earlier (d := p.walk.getVert (i + 4))
    (s := p.walk.getVert (i + 3)) (t := p.walk.getVert (i + 5)) hc hd he hf
  · rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]
    omega
  · rw [p.distance (geometry := geometry) (by omega) (by omega)]
    omega
  · rw [p.distance (geometry := geometry) (by omega) (by omega)]
    omega
  · rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]
    omega
  · exact adjacent_symm R (by simpa only [Nat.add_assoc] using p.adjacent (i := i + 3) (by omega))
  · simpa only [Nat.add_assoc] using p.adjacent (i := i + 4) (by omega)
  · exact adjacent_symm R (by simpa only [Nat.add_assoc] using p.adjacent (i := i + 5) (by omega))
  · simpa only [Nat.add_assoc, show i + 6 - 2 = i + 4 by omega] using
      p.turns (i + 6) (hi.add (by decide : Even 6)) (by omega) (by omega)
  · simpa only [show i + 6 - 2 = i + 4 by omega] using
      (p.moving_spans source common earlier (hi.add (by decide : Even 6)) (by omega) (by omega)).1
  · simpa only [Nat.add_assoc, show i + 4 - 1 = i + 3 by omega] using
      p.edge_Z_ne (i + 4) (hi.add (by decide : Even 4)) (by omega) (by omega)
  · exact radius_four_not_le_forward common earlier p hi hi2 hi6

private theorem backward_product (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ}
    (hi : Even i) (hi8 : 8 ≤ i) (hi12 : i ≤ 12) :
    (V R (p.walk.getVert i) ⊓ Q R (p.walk.getVert (i - 6)) : Set (FreeAmalgam R)) ⊆
      (Z R (p.walk.getVert i) : Set (FreeAmalgam R)) *
        (Q R (p.walk.getVert (i - 8)) : Set (FreeAmalgam R)) := by
  have hi4 : Even (i - 4) := by rw [Nat.even_iff] at hi ⊢; omega
  have hi6 : Even (i - 6) := by rw [Nat.even_iff] at hi ⊢; omega
  have hi8' : Even (i - 8) := by rw [Nat.even_iff] at hi ⊢; omega
  have hc := p.even_color hi (by omega)
  have hd := p.even_color hi4 (by omega)
  have he := p.even_color hi6 (by omega)
  have hf := p.even_color hi8' (by omega)
  have heu : Adjacent R (p.walk.getVert (i - 6)) (p.walk.getVert (i - 7)) := by
    exact adjacent_symm R (by
      simpa only [show i - 7 + 1 = i - 6 by omega] using p.adjacent (i := i - 7) (by omega))
  have hfu : Adjacent R (p.walk.getVert (i - 8)) (p.walk.getVert (i - 7)) := by
    simpa only [show i - 8 + 1 = i - 7 by omega] using p.adjacent (i := i - 8) (by omega)
  have hu : color R (p.walk.getVert (i - 7)) = true := by
    have hn := adjacent_color_ne R heu
    cases h : color R (p.walk.getVert (i - 7)) <;> simp_all
  have hp := p.critical_pair earlier hi8' (by omega)
  rw [show i - 8 + 8 = i by omega] at hp
  have hr := common.critical_reverse _ hf _ hc hp
  apply product_of_small_commutator common earlier hc hf hfu
    (by rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]; omega)
    (inf_le_right.trans (Q_le_adjacent_h R hu heu)) hr.2
  apply commutator_card_le_two source common earlier (d := p.walk.getVert (i - 4))
    (s := p.walk.getVert (i - 3)) (t := p.walk.getVert (i - 5)) hc hd he hf
  · rw [p.distance (geometry := geometry) (by omega) (by omega)]
    omega
  · rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]
    omega
  · rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]
    omega
  · rw [p.distance (geometry := geometry) (by omega) (by omega)]
    omega
  · simpa only [show i - 4 + 1 = i - 3 by omega] using p.adjacent (i := i - 4) (by omega)
  · exact adjacent_symm R (by
      simpa only [show i - 5 + 1 = i - 4 by omega] using p.adjacent (i := i - 5) (by omega))
  · simpa only [show i - 6 + 1 = i - 5 by omega] using p.adjacent (i := i - 6) (by omega)
  · obtain ⟨g, hg, hgf⟩ := p.turns (i - 6) hi6 (by omega) (by omega)
    rw [show i - 6 + 2 = i - 4 by omega, show i - 6 - 2 = i - 8 by omega] at hgf
    refine ⟨g⁻¹, (stabilizer R _).inv_mem hg, ?_⟩
    rw [← hgf, ← act_mul, mul_inv_cancel, act_one]
  · simpa only [show i - 6 + 2 = i - 4 by omega] using
      (p.moving_spans source common earlier hi6 (by omega) (by omega)).2
  · simpa only [show i - 4 - 1 = i - 5 by omega, show i - 4 + 1 = i - 3 by omega] using
      (p.edge_Z_ne (i - 4) hi4 (by omega) (by omega)).symm
  · exact radius_four_not_le_backward common earlier p hi hi8 hi12

/-- All six literal setwise product containments in MS93 (4.5.1)(ii). -/
theorem productBoundsOnPath (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) : ProductBoundsOnPath R p :=
  ⟨fun _ hi h2 h6 => forward_product source common earlier p hi h2 h6,
    fun _ hi h8 h12 => backward_product source common earlier p hi h8 h12⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First.Kernel.Product
