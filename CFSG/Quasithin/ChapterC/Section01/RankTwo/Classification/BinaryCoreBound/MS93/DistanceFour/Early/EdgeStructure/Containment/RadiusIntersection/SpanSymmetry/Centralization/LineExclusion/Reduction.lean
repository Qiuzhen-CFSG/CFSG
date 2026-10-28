module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.RadiusIntersection.SpanSymmetry.Centralization.Reduction

/-!
# The midpoint span in the radius-line branch

Put W = ⟨Z_e^{G_a}⟩ for the actual paired midpoint. A seed element in
B_a commutes with W: its conjugates differ by elements centralizing the
radius, and the seed Z_e is abelian. This only asserts centralization of
W, not centralization of the entire radius.

Critical nonnormality and simultaneous escape show W is nonabelian.
The index-two B-intersection therefore gives a fixed plane for W on U_e.
Evaluation outside that plane bounds the image of W in G_e/Q_e by the
radius displacement. In the order-two case this image has order at most
two, and W' is exactly the original central displacement [Z_d,Q_a].
These are the inputs to the separate self-dual quotient obstruction.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (2.1)(vi--vii), (2.2)(iv), and (4.6.4), printed pp.855--857, 902.
All normality and finiteness remain relative to actual local stabilizers.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanSymmetry

private theorem seed_fixed_centralizes_span {G : Type*} [Group G]
    (S H K V : Subgroup G) [IsMulCommutative S]
    (hKS : K ≤ S) (hSV : S ≤ V)
    (hc : ⁅K,H⁆ ≤ centralizer (V : Set G)) :
    K ≤ centralizer ((⨆ g : H, S.map (MulAut.conj (g : G)).toMonoidHom : Subgroup G) : Set G) := by
  apply le_centralizer_iff.mp
  apply iSup_le
  intro g
  rintro _ ⟨s,hs,rfl⟩ k hk
  have hconj : (MulAut.conj (g : G)⁻¹) k ∈ centralizer (S : Set G) := by
    simp only [MulAut.conj_apply, inv_inv]
    rw [show (g : G)⁻¹ * k * (g : G) = ⁅(g : G)⁻¹,k⁆ * k by
      simp [commutatorElement_def, mul_assoc]]
    apply (centralizer (S : Set G)).mul_mem
    · apply centralizer_le hSV
      apply hc
      rw [commutator_comm]
      exact commutator_mem_commutator (H.inv_mem g.property) hk
    · intro t ht
      exact setLike_mul_comm ht (hKS hk)
  have hh := congrArg (MulAut.conj (g : G)) (hconj s hs)
  have hundo : (MulAut.conj (g : G)) ((MulAut.conj (g : G)⁻¹) k) = k := by
    simp [MulAut.conj_apply, mul_assoc]
  simpa only [map_mul, hundo, MulEquiv.coe_toMonoidHom] using hh.symm

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry)

include common in
/-- The quotient-fixed part of an abelian seed centralizes its own stabilizer span. -/
theorem fixed_centralizes_neighborSpan
    (initial : InitialFacts R geometry) (a e : Vertex R)
    (ha : color R a = false) (he : color R e = false)
    (hnear : (cosetGraph R).dist a e = 2) :
    Z R e ⊓ B R a (geometry.Z_normal a) ≤
      centralizer (neighborSpan a e : Set (FreeAmalgam R)) := by
  let K := Z R e ⊓ B R a (geometry.Z_normal a)
  let C := centralizer (V R a : Set (FreeAmalgam R))
  have hVQ := radius_le_Q common a ha
  have hVG : V R a ≤ stabilizer R a := hVQ.trans (fun _ hx => hx.1)
  have hZC : Z R a ≤ C :=
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha)).trans
      (centralizer_le hVQ)
  have hQC : ⁅Q R a,K⁆ ≤ C := by
    rw [commutator_comm]
    intro x hx
    obtain ⟨z,hz,rfl⟩ := initial.commutator_central a ha
      (commutator_mono (inf_le_right.trans (B_le_radius common a ha)) le_rfl hx)
    intro v hv
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨v,hv⟩)
  have hLC : ⁅Ltilde R a,K⁆ ≤ C := by
    rw [commutator_comm]
    exact ((commutator_mono inf_le_right le_rfl).trans
      (Flags.B_commutator_le_Z geometry a hVG)).trans hZC
  have hKC : ⁅K,stabilizer R a⁆ ≤ C := by
    rw [commutator_comm]
    have hh : stabilizer R a ≤ commutatorPreimage (stabilizer R a) K C := by
      exact (source.local_generation a ha).ge.trans
        (sup_le (le_commutatorPreimage (Ltilde_le_stabilizer a) hLC)
          (le_commutatorPreimage (fun _ hx => hx.1) hQC))
    exact (commutator_mono hh le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _
        ((V_normalized a).trans (normalizer_le_normalizer_centralizer (V R a))))
  let := geometry.Z_elementary (lt_trans (by decide : 0 < 2) common.large_distance) e he
  exact seed_fixed_centralizes_span (Z R e) (stabilizer R a) K (V R a)
    inf_le_left (le_iSup_of_le e (le_iSup_of_le
      (by rw [SimpleGraph.dist_comm]; exact hnear.le) le_rfl)) hKC

include common in
/-- Bilateral escape makes the midpoint join nonnormal in the initial stabilizer. -/
theorem paired_midpoint_join_not_normal
    (hb : geometry.b R = 4) (a b d : Vertex R) (ha : color R a = false)
    (p : SpanOffender.PairedSpans geometry a b d ha) :
    ¬ ((Z R p.e ⊔ Z R a).subgroupOf (stabilizer R a)).Normal := by
  classical
  have hd : color R d = false := by
    have hh := p.hr
    rw [← p.transport_seed, action_preserves_color] at hh
    exact hh
  have hda : (cosetGraph R).dist d a = 2 := by
    have hh := p.far
    rw [← p.transport_seed, ← p.transport_vertex, dist_act, SimpleGraph.dist_comm] at hh
    exact hh
  obtain ⟨g,hg⟩ : ∃ g : stabilizer R a,
      ¬ (Z R d).map (MulAut.conj (g : FreeAmalgam R)).toMonoidHom ≤ Q R p.e := by
    by_contra! h
    exact p.escape_left (iSup_le h)
  let t := act R (g : FreeAmalgam R)⁻¹ d
  have ht : color R t = false := by simpa only [t, action_preserves_color] using hd
  have hfix : act R (g : FreeAmalgam R)⁻¹ a = a := (stabilizer R a).inv_mem g.property
  have hta : (cosetGraph R).dist t a = 2 := by
    have hh := dist_act R (g : FreeAmalgam R)⁻¹ d a
    simpa only [hfix, hda, t] using hh
  have hesc : ¬ Z R t ≤ Q R p.e := by simpa only [t, Z_act, inv_inv] using hg
  have hte : (cosetGraph R).dist t p.e = 4 := by
    have hlo := criticalDistance_le R t (geometry.exists_critical t ht) hesc
    rw [geometry.distance_constant t ht] at hlo
    change geometry.b R ≤ _ at hlo
    have hhi := (cosetGraph_connected R).dist_triangle (u := t) (v := a) (w := p.e)
    have hn := p.near
    omega
  have hcrit : CriticalPair R t p.e (geometry.exists_critical t ht) :=
    ⟨by rw [geometry.distance_constant t ht]; exact hte.trans hb.symm, hesc⟩
  have hnon := (critical_nonnormal_forward R geometry common.centralizer p.e p.he
    (by rw [geometry.distance_constant p.e p.he]; exact lt_trans (by decide) common.large_distance)
    t (common.critical_reverse t ht p.e p.he hcrit) a
    (by rw [SimpleGraph.dist_comm]; exact p.near) (by
      rw [SimpleGraph.dist_comm (u := a), hta, SimpleGraph.dist_comm (u := p.e), hte])).2
  simpa only [common.X_eq_Z a ha] using hnon

include common in
/-- Simultaneous escape prevents the midpoint span from lying in its own midpoint kernel. -/
theorem paired_midpoint_span_not_le_kernel
    (hb : geometry.b R = 4) (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (p : SpanOffender.PairedSpans geometry a b d ha) :
    ¬ neighborSpan a p.e ≤ Q R p.e := by
  have hcolb : color R b = true := by
    have hh := adjacent_color_ne R hab
    cases hc : color R b <;> simp_all
  have hQbGa : Q R b ≤ stabilizer R a := by
    rw [Q_h_eq_edge R hcolb hab]; exact inf_le_left
  have hQbGe : Q R b ≤ stabilizer R p.e := by
    rw [Q_h_eq_edge R hcolb p.edge]; exact inf_le_left
  have hSN : Q R b ≤ normalizer (Z R p.e ⊔ Z R a : Subgroup (FreeAmalgam R)) :=
    (le_inf (hQbGe.trans (Z_normalized R p.e)) (hQbGa.trans (Z_normalized R a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hSnonnormal := paired_midpoint_join_not_normal common hb a b d ha p
  have hgen := OrderTwo.edge_conjugate_generation source a b ha hab (Z R p.r) p.seed_edge
    (common.critical_reverse a ha p.r p.hr p.critical).2
  have hSQb : Z R p.e ⊔ Z R a ≤ Q R b :=
    sup_le (edge_Z_le_Q common p.e b p.he p.edge) (edge_Z_le_Q common a b ha hab)
  obtain ⟨g,hga,hn,_⟩ := source_2_1_vii R a p.r b ha hab
    (Z R p.e ⊔ Z R a) (Z R p.e ⊔ Z R a) hSQb hSQb
    (normal_subgroupOf_of_le_normalizer hSN) (normal_subgroupOf_of_le_normalizer hSN)
    hSnonnormal hSnonnormal hgen
  intro hle
  have hfix : act R g a = a := hga
  have hseed : Z R (act R g p.e) ≤ neighborSpan a p.e := by
    rw [Z_act]
    exact le_iSup_of_le (⟨g⁻¹,(stabilizer R a).inv_mem hga⟩ : stabilizer R a) le_rfl
  have hdist : (cosetGraph R).dist a (act R g p.e) = 2 := by
    have hh := dist_act R g a p.e
    simpa only [hfix, p.near] using hh
  have hcomm : ⁅Z R (act R g p.e), Z R p.r⁆ ≤ Z R a := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl (hseed.trans hle)).trans (p.layer_right.trans inf_le_left)
  apply hn
  rw [Subgroup.map_sup, ← Z_act, ← Z_act, hfix]
  exact (source_2_1_vi R source geometry a ha
    (by rw [geometry.distance_constant a ha]; exact lt_trans (by decide) common.large_distance)
    p.critical (act R g p.e) hdist
    (hseed.trans ((neighborSpan_le_radius a p.e (by
      rw [SimpleGraph.dist_comm]; exact p.near.le)).trans (radius_le_Q common a ha)))
    (hcomm.trans le_sup_right)).1

include common in
/-- The actual midpoint span is nonabelian, independently of any displacement cardinality. -/
theorem paired_midpoint_span_noncommutative
    (hb : geometry.b R = 4) (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (p : SpanOffender.PairedSpans geometry a b d ha) :
    ¬ IsMulCommutative (neighborSpan a p.e) := by
  intro hc
  apply paired_midpoint_span_not_le_kernel common hb a b d ha hab p
  rw [← common.centralizer p.e b p.he p.edge]
  have hcolb : color R b = true := by
    have hh := adjacent_color_ne R hab
    cases h : color R b <;> simp_all
  refine le_inf ((neighborSpan_le_radius a p.e (by
    rw [SimpleGraph.dist_comm]; exact p.near.le)).trans
    ((radius_le_Q common a ha).trans (Q_le_adjacent_h R hcolb hab))) ?_
  exact (le_centralizer_iff_isMulCommutative.mpr hc).trans
    (centralizer_le (Z_le_neighborSpan a p.e))

include common in
/-- A radius displacement of order two forces a midpoint-span image of order at most two. -/
theorem paired_radius_line_span_image_le_two
    (initial : InitialFacts R geometry) (hb : geometry.b R = 4)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d,Q R b⁆ ≤ B R a (geometry.Z_normal a))
    (p : SpanOffender.PairedSpans geometry a b d ha)
    (hcard : Nat.card (⁅U R p.e,V R a⁆ : Subgroup (FreeAmalgam R)) = 2) :
    (Q R p.e).relIndex (neighborSpan a p.e) ≤ 2 := by
  let W := neighborSpan a p.e
  let F := U R p.e ⊓ centralizer (W : Set (FreeAmalgam R))
  have hWV : W ≤ V R a := neighborSpan_le_radius a p.e (by
    rw [SimpleGraph.dist_comm]; exact p.near.le)
  have hWGe : W ≤ stabilizer R p.e :=
    (hWV.trans (radius_le_Q common a ha)).trans
      (Q_le_stabilizer_of_dist_two R a p.e ha p.near)
  have hfixed := fixed_centralizes_neighborSpan common initial a p.e ha p.he p.near
  have hsmall := paired_span_index_le_two common initial hb a b d ha hab hdb hbad p
  let : Finite (Z R p.e) := by
    let := finite_stabilizer R p.e
    exact Finite.of_injective (inclusion (Z_le_stabilizer R p.e)) (inclusion_injective _)
  let : Finite (U R p.e) := Finite.of_injective (inclusion (U_le_Z p.e)) (inclusion_injective _)
  let := geometry.U_elementary (lt_trans (by decide : 0 < 2) common.large_distance) p.e p.he
  have hsmall' : (centralizer (W : Set (FreeAmalgam R))).relIndex (Z R p.e) ≤ 2 := by
    have hh := relIndex_le_of_le_left hfixed
      (show (Z R p.e ⊓ B R a (geometry.Z_normal a)).relIndex (Z R p.e) ≠ 0 from
        index_ne_zero_of_finite)
    rw [inf_relIndex_left] at hh
    exact hh.trans hsmall
  have hFi : F.relIndex (U R p.e) = 2 := by
    have hlo : F.relIndex (U R p.e) ≠ 0 := index_ne_zero_of_finite
    have hhi : F.relIndex (U R p.e) ≤ 2 := by
      rw [show F = U R p.e ⊓ centralizer (W : Set (FreeAmalgam R)) from rfl,
        inf_relIndex_left]
      exact (relIndex_le_of_le_right (U_le_Z p.e) index_ne_zero_of_finite).trans hsmall'
    have hne : F.relIndex (U R p.e) ≠ 1 := by
      intro heq
      have hc : W ≤ centralizer (U R p.e : Set (FreeAmalgam R)) :=
        le_centralizer_iff.mp ((relIndex_eq_one.mp heq).trans inf_le_right)
      apply paired_midpoint_span_not_le_kernel common hb a b d ha hab p
      rw [← common.natural.centralizer p.e p.he]
      exact le_inf hWGe hc
    omega
  have hD := (paired_radius_displacement_structure common initial a b d ha p).2.2
  have hle : ⁅U R p.e,W⁆ ≤ ⁅U R p.e,V R a⁆ := commutator_mono le_rfl hWV
  have hindex := actor_index_eq_displacement_card_of_fixed_index_two (U R p.e) W
    (hWGe.trans (U_normalized p.e)) (hle.trans (hD.trans (centralizer_le hWV))) hFi
  have hkernel : (Q R p.e).subgroupOf W =
      (centralizer (U R p.e : Set (FreeAmalgam R))).subgroupOf W := by
    ext x
    change (x : FreeAmalgam R) ∈ Q R p.e ↔
      (x : FreeAmalgam R) ∈ centralizer (U R p.e : Set (FreeAmalgam R))
    rw [← common.natural.centralizer p.e p.he, mem_inf]
    exact and_iff_right (hWGe x.property)
  change ((Q R p.e).subgroupOf W).index ≤ 2
  rw [hkernel]
  change (centralizer (U R p.e : Set (FreeAmalgam R))).relIndex W ≤ 2
  rw [hindex]
  let : Finite (⁅U R p.e,V R a⁆ : Subgroup (FreeAmalgam R)) :=
    Nat.finite_of_card_ne_zero (by omega)
  exact (card_le_of_le hle).trans_eq hcard

include common in
/-- In the line branch, the nonabelian midpoint span has the original central derived line. -/
theorem paired_radius_line_span_derived
    (hb : geometry.b R = 4)
    (a b d : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (p : SpanOffender.PairedSpans geometry a b d ha)
    (hcard : Nat.card (⁅U R p.e,V R a⁆ : Subgroup (FreeAmalgam R)) = 2) :
    ⁅neighborSpan a p.e,neighborSpan a p.e⁆ = ⁅Z R d,Q R a⁆ := by
  let D := ⁅Z R d,Q R a⁆
  let W := neighborSpan a p.e
  have hWV : W ≤ V R a := neighborSpan_le_radius a p.e (by
    rw [SimpleGraph.dist_comm]; exact p.near.le)
  have hZeV : Z R p.e ≤ V R a := (Z_le_neighborSpan a p.e).trans hWV
  have hVGe : V R a ≤ stabilizer R p.e := (radius_le_Q common a ha).trans
    (Q_le_stabilizer_of_dist_two R a p.e ha p.near)
  have hseed : ⁅Z R p.e,V R a⁆ = D := by
    let C := Z R p.e ⊓ centralizer (stabilizer R p.e : Set (FreeAmalgam R))
    have hsplit : Z R p.e = U R p.e ⊔ C :=
      (show BinaryNaturalStructure source from
        ⟨common.X_eq_Z,common.natural,common.decomposition,common.disjoint⟩).decomposition_at p.e p.he
    have hh := commutator_eq_of_centralizing_sup ((sup_comm _ _).trans hsplit.symm)
      (show C ≤ centralizer (V R a : Set (FreeAmalgam R)) from
        inf_le_right.trans (centralizer_le hVGe))
      ((U_le_Z p.e).trans (hZeV.trans (V R a).le_normalizer))
    rw [commutator_comm, ← hh, commutator_comm]
    exact paired_radius_line_eq_original_displacement common a b d ha p hcard
  have hWD : ⁅W,V R a⁆ ≤ D := by
    rw [show W = ⨆ g : stabilizer R a,
      (Z R p.e).map (MulAut.conj (g : FreeAmalgam R)).toMonoidHom from rfl,
      commutator_iSup_conjugates _ _ _ hZeV (V_normalized a), hseed]
    apply iSup_le
    intro g
    rintro _ ⟨x,hx,rfl⟩
    change (g : FreeAmalgam R) * x * (g : FreeAmalgam R)⁻¹ ∈ D
    rw [p.central_left hx g g.property, mul_inv_cancel_right]
    exact hx
  have hder : ⁅W,W⁆ ≤ D := (commutator_mono le_rfl hWV).trans hWD
  have hnon : ⁅W,W⁆ ≠ ⊥ := by
    intro hz
    exact paired_midpoint_span_noncommutative common hb a b d ha hab p
      (commutator_self_eq_bot_iff.mp hz)
  let : Finite D := Nat.finite_of_card_ne_zero (by
    have hh : Nat.card D = 2 := p.card_left
    omega)
  let : Finite (⁅W,W⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hder) (inclusion_injective _)
  apply eq_of_le_of_card_ge hder
  have hh := (one_lt_card_iff_ne_bot _).mpr hnon
  have hDcard : Nat.card D = 2 := p.card_left
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanSymmetry
