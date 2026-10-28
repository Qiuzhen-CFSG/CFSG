module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.OrbitSpan
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.NormalizerTransfer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Factorization.Forward
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.DisjointConjugateCenter
/-!
# Local centrality of an escaping neighbor's order-two displacement

A bad neighbor supplies a critical pair through the original vertex. We
conjugate that pair so that its opposite endpoint becomes the original
vertex, retaining the actual midpoint and the order-two displacement.
Critical noncommutation identifies the transported displacement with the
commutator of the endpoint layers. This implements the WLOG step on p.902.

Simplicity of the actual marked SL₃(2) quotient proves the conjugate-generation
premise in (2.1)(vii). If the seed displacement were not central in the local
stabilizer, its order two would make it nonnormal there. Apply simultaneous
escape to it and to Z_delta Z_alpha, whose nonnormality follows from (2.2)(iv).
Clause (2.1)(vi) forces the selected conjugate to escape the midpoint kernel.
A second critical-pair commutator then identifies its displacement with a
subgroup of the endpoint kernel, contradicting simultaneous escape.

This proves only the first centrality conclusion in (4.6.4). Abelianness of
the conjugate span and the terminal edge-containment contradiction remain
separate arguments. All normality is relative to the stated local group.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (2.1)(vi--vii), (2.2)(iv), and (4.6.4), printed pp.855--856, 902.
The local projection construction follows the checked construction in
Reduction/SectionThree/NormalizationTransfer.lean.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry)

private theorem eq_of_nontrivial_le_two {G : Type*} [Group G]
    {A D : Subgroup G} (hAD : A ≤ D) (hne : A ≠ ⊥) (hc : Nat.card D = 2) : A = D := by
  let : Finite D := Nat.finite_of_card_ne_zero (by omega)
  let : Finite A := Finite.of_injective (inclusion hAD) (inclusion_injective hAD)
  apply eq_of_le_of_card_ge hAD
  have hh := (one_lt_card_iff_ne_bot A).mpr hne
  omega

private theorem normalizes_commutator {G : Type*} [Group G] (T A D : Subgroup G)
    (hA : T ≤ normalizer A) (hD : T ≤ normalizer D) : T ≤ normalizer (⁅A,D⁆ : Subgroup G) := by
  intro t ht
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hA ht), mem_normalizer_iff_map_conj_eq.mp (hD ht)]

include source in
private theorem local_projection (a : Vertex R) (ha : color R a = false) :
    ∃ π : stabilizer R a →* SL, Function.Surjective π ∧
      π.ker = (Q R a).subgroupOf (stabilizer R a) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R ha
  let S := stabilizer R (mVertex R g)
  let f := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R)
  have hf : Function.Injective f := (MulAut.conj g⁻¹).injective.comp (embedM_injective R)
  have hrange : f.range = S := by
    rw [MonoidHom.range_comp]
    exact (stabilizer_mVertex R g).symm
  let e : M ≃* S := (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)
  have he : S.subtype.comp e.toMonoidHom = f := by ext x; rfl
  have hQ : (pCore 2 M).map e.toMonoidHom =
      (Q R (mVertex R g)).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [map_map, he, map_subgroupOf_eq_of_le (show Q R (mVertex R g) ≤ S from fun _ hx => hx.1)]
    rw [show f = (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R) from rfl, ← map_map,
      ← Q_alpha R source.two_group source.core_le]
    have hh := Q_act R g (alpha R)
    simpa only [alpha, act_mVertex, one_mul] using hh.symm
  refine ⟨source.projection.comp e.symm.toMonoidHom,
    source.projection_surjective.comp e.symm.surjective, ?_⟩
  rw [← MonoidHom.comap_ker, source.projection_kernel, ← hQ]
  ext x
  constructor
  · intro hx
    exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  · rintro ⟨y,hy,rfl⟩
    change e.symm (e y) ∈ pCore 2 M
    rw [MulEquiv.symm_apply_apply]
    exact hy

include common in
private theorem critical_generation (a r b : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hcrit : CriticalPair R a r (geometry.exists_critical a ha)) :
    NormalizerTransfer.conjugatesIn (Z R r) (stabilizer R a) ⊔ Q R b = stabilizer R a := by
  let F := stabilizer R a
  let N := NormalizerTransfer.conjugatesIn (Z R r) F
  have hr := critical_endpoint_color R a ha _ hcrit
  have hrev := common.critical_reverse a ha r hr hcrit
  have hpos : 0 < criticalDistance R a (geometry.exists_critical a ha) := by
    rw [geometry.distance_constant a ha]
    exact lt_trans (by decide : 0 < 2) common.large_distance
  have hZF : Z R r ≤ F := critical_Z_le_stabilizer R geometry a ha hpos hcrit
  have hNF : N ≤ F := NormalizerTransfer.conjugatesIn_le _ _ hZF
  have hZN : Z R r ≤ N := by
    intro z hz
    apply le_iSup (fun g : F => NormalizerTransfer.rightConjugate (Z R r) g) 1
    exact ⟨z, hz, by simp⟩
  obtain ⟨π,hπ,hker⟩ := local_projection (source := source) a ha
  let N₀ := N.subgroupOf F
  let : N₀.Normal := normal_subgroupOf_of_le_normalizer
    (NormalizerTransfer.conjugatesIn_normalized (Z R r) F)
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  have hNπ : (N₀.map π).Normal := (inferInstance : N₀.Normal).map π hπ
  have him : N₀.map π = ⊤ := by
    rcases hNπ.eq_bot_or_eq_top with h | h
    · have hle := (Subgroup.map_eq_bot_iff _).mp h
      rw [hker] at hle
      exact (hrev.2 (fun z hz => hle (show (⟨z, hZF hz⟩ : F) ∈ N₀ from hZN hz))).elim
    · exact h
  have hjoin : N₀ ⊔ (Q R a).subgroupOf F = ⊤ := by
    have hh := congrArg (Subgroup.comap π) him
    simpa only [comap_map_eq, hker, comap_top] using hh
  have hamb : N ⊔ Q R a = F := by
    have hh := congrArg (Subgroup.map F.subtype) hjoin
    simpa only [N₀, Subgroup.map_sup, map_subgroupOf_eq_of_le hNF,
      map_subgroupOf_eq_of_le (show Q R a ≤ F from fun _ hx => hx.1),
      ← MonoidHom.range_eq_map, range_subtype] using hh
  have hb : color R b = true := by
    have hh := adjacent_color_ne R hab
    cases h : color R b <;> simp_all
  apply le_antisymm
  · exact sup_le hNF (by rw [Q_h_eq_edge R hb hab]; exact inf_le_left)
  · change F ≤ N ⊔ Q R b
    rw [← hamb]
    exact sup_le le_sup_left ((Q_le_adjacent_h R hb hab).trans le_sup_right)

include common in
/-- The source WLOG step as an actual conjugation of a critical segment.
The order-two displacement at its far end lies in the starting Z-layer. -/
theorem escaping_neighbor_segment (initial : InitialFacts R geometry)
    (hb : geometry.b R = 4) (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    ∃ (f : FreeAmalgam R) (r e : Vertex R) (_hr : color R r = false)
      (_he : color R e = false),
      act R f d = r ∧ act R f a = e ∧
      CriticalPair R a r (geometry.exists_critical a ha) ∧
      (cosetGraph R).dist a e = 2 ∧ (cosetGraph R).dist e r = 2 ∧
      Nat.card (⁅Z R r, Q R e⁆ : Subgroup (FreeAmalgam R)) = 2 ∧
      ⁅Z R r, Q R e⁆ ≤ Z R a := by
  have hg := escaping_neighbor_geometry common initial a b d ha hab hdb hbad
  obtain ⟨c,hc,hca,_,_,hcd,_⟩ := escaping_neighbor_critical common initial hb a b d ha hg.1 hab hdb hbad
  obtain ⟨x,hx⟩ := exists_mVertex_of_color R hc
  obtain ⟨y,hy⟩ := exists_mVertex_of_color R ha
  let f := x⁻¹ * y
  have hfa : act R f c = a := by rw [hx, hy, act_mVertex]; simp [f]
  let r := act R f d
  let e := act R f a
  have hr : color R r = false := by simpa [r, action_preserves_color] using hg.1
  have he : color R e = false := by simpa [e, action_preserves_color] using ha
  have hcrit : CriticalPair R a r (geometry.exists_critical a ha) := by
    have ht := (criticalPair_act_iff R f c d (geometry.exists_critical c hc)
      (geometry.exists_critical _ (by simpa only [action_preserves_color] using hc))).mpr hcd
    simpa only [hfa] using ht
  have hae : (cosetGraph R).dist a e = 2 := by
    exact (show (cosetGraph R).dist a (act R f a) = (cosetGraph R).dist c a by
      simpa only [hfa] using dist_act R f c a).trans hca
  have her : (cosetGraph R).dist e r = 2 := by
    change (cosetGraph R).dist (act R f a) (act R f d) = 2
    rw [dist_act, SimpleGraph.dist_comm]
    exact hg.2.1
  have hcard : Nat.card (⁅Z R r, Q R e⁆ : Subgroup (FreeAmalgam R)) = 2 := by
    change Nat.card (⁅Z R (act R f d), Q R (act R f a)⁆ : Subgroup (FreeAmalgam R)) = 2
    rw [Z_act, Q_act, ← map_commutator, card_map_of_injective (MulAut.conj f⁻¹).injective]
    exact escaping_neighbor_commutator_card common initial a b d ha hab hdb hbad
  have hZaQe : Z R a ≤ Q R e := Z_le_Q_of_dist_lt R a (geometry.exists_critical a ha) (by
    rw [hae, geometry.distance_constant a ha]; exact common.large_distance)
  have hcomm : ⁅Z R r, Z R a⁆ = ⁅Z R r, Q R e⁆ :=
    eq_of_nontrivial_le_two (commutator_mono le_rfl hZaQe)
      (by rw [commutator_comm]; exact common.critical_noncommutation a ha r hcrit) hcard
  refine ⟨f,r,e,hr,he,rfl,rfl,hcrit,hae,her,hcard,?_⟩
  rw [← hcomm]
  apply le_normalizer_iff_commutator_le_right.mp
  exact (critical_Z_le_stabilizer R geometry a ha (by
    rw [geometry.distance_constant a ha]; exact lt_trans (by decide : 0 < 2) common.large_distance) hcrit).trans
    (Z_normalized R a)

include common in
/-- The escaping neighbor's displacement is central in the whole local
stabilizer, not merely in its radius-two subgroup. -/
theorem escaping_neighbor_commutator_le_local_center (initial : InitialFacts R geometry)
    (hb : geometry.b R = 4) (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    ⁅Z R d, Q R a⁆ ≤ (center (stabilizer R a)).map (stabilizer R a).subtype := by
  have hg := escaping_neighbor_geometry common initial a b d ha hab hdb hbad
  have hcard := escaping_neighbor_commutator_card common initial a b d ha hab hdb hbad
  have hpos : ∀ v (hv : color R v = false),
      0 < criticalDistance R v (geometry.exists_critical v hv) := by
    intro v hv
    rw [geometry.distance_constant v hv]
    exact lt_trans (by decide : 0 < 2) common.large_distance
  have hcolb : color R b = true := by
    have hh := adjacent_color_ne R hab
    cases hh' : color R b <;> simp_all
  have hQaGa : Q R a ≤ stabilizer R a := fun _ hx => hx.1
  have hZda : Z R d ≤ Q R a := Z_le_Q_of_dist_lt R d (geometry.exists_critical d hg.1) (by
    rw [geometry.distance_constant d hg.1, hg.2.1]; exact common.large_distance)
  have hZaa : Z R a ≤ Q R a := by rw [← common.X_eq_Z a ha]; exact omegaCenter_le _
  have hQbGa : Q R b ≤ stabilizer R a := by rw [Q_h_eq_edge R hcolb hab]; exact inf_le_left
  have hQbGd : Q R b ≤ stabilizer R d := by rw [Q_h_eq_edge R hcolb hdb]; exact inf_le_left
  have hQaQb := Q_le_adjacent_h R hcolb hab
  have hDa : ⁅Z R d, Q R a⁆ ≤ Q R a :=
    (neighbor_commutator_le_center initial a b d ha hab hdb).trans
      ((map_subtype_le _).trans (radius_le_Q common a ha))
  have hDnormal : Q R b ≤ normalizer (⁅Z R d, Q R a⁆ : Subgroup (FreeAmalgam R)) :=
    normalizes_commutator _ _ _ (hQbGd.trans (Z_normalized R d))
      (hQbGa.trans (Q_normalized R a))
  have hSnormal : Q R b ≤ normalizer (Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) :=
    (le_inf (hQbGd.trans (Z_normalized R d)) (hQbGa.trans (Z_normalized R a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hSnonnormal : ¬ ((Z R d ⊔ Z R a).subgroupOf (stabilizer R a)).Normal := by
    obtain ⟨c,hc,hca,_,hdc,_,_⟩ := escaping_neighbor_critical common initial hb a b d ha hg.1 hab hdb hbad
    have hh := (critical_nonnormal_forward R geometry common.centralizer d hg.1 (hpos d hg.1)
      c hdc a hg.2.1 (by
        rw [SimpleGraph.dist_comm (u := a), hca, hdc.1, geometry.distance_constant d hg.1]
        exact hb.symm)).2
    simpa only [common.X_eq_Z a ha] using hh
  by_contra hnot
  have hDnonnormal : ¬ ((⁅Z R d, Q R a⁆).subgroupOf (stabilizer R a)).Normal := by
    intro hN
    have hnorm := (normal_subgroupOf_iff_le_normalizer (hDa.trans hQaGa)).mp hN
    have hcent := le_centralizer_iff.mp (centralizes_of_normalizes_card_two hcard hnorm)
    apply hnot
    intro x hx
    refine ⟨⟨x, hQaGa (hDa hx)⟩, mem_center_iff.mpr ?_, rfl⟩
    intro y
    exact Subtype.ext (hcent hx y y.property)
  obtain ⟨f,r,e,hr,he,_,_,hcrit,hae,her,_,hR⟩ :=
    escaping_neighbor_segment common initial hb a b d ha hab hdb hbad
  obtain ⟨g,hga,hnD,hnS⟩ := source_2_1_vii R a r b ha hab
    ⁅Z R d, Q R a⁆ (Z R d ⊔ Z R a) (hDa.trans hQaQb)
    ((sup_le hZda hZaa).trans hQaQb)
    (normal_subgroupOf_of_le_normalizer hDnormal)
    (normal_subgroupOf_of_le_normalizer hSnormal) hDnonnormal hSnonnormal
    (critical_generation common a r b ha hab hcrit)
  let d' := act R g d
  have hd' : color R d' = false := by simpa only [d', action_preserves_color] using hg.1
  have hfix : act R g a = a := hga
  have hdist : (cosetGraph R).dist d' a = 2 := by
    change (cosetGraph R).dist (act R g d) a = 2
    rw [← hfix, dist_act]
    exact hg.2.1
  have hDmap : (⁅Z R d, Q R a⁆).map (MulAut.conj g⁻¹).toMonoidHom = ⁅Z R d', Q R a⁆ := by
    rw [map_commutator, ← Z_act, ← Q_act, hfix]
  have hSmap : (Z R d ⊔ Z R a).map (MulAut.conj g⁻¹).toMonoidHom = Z R d' ⊔ Z R a := by
    rw [Subgroup.map_sup, ← Z_act, ← Z_act, hfix]
  rw [hDmap] at hnD
  rw [hSmap] at hnS
  have hescape : ¬ Z R d' ≤ Q R e := by
    intro hle
    have hcomm : ⁅Z R d', Z R r⁆ ≤ Z R a :=
      (commutator_mono hle le_rfl).trans (by rwa [commutator_comm])
    apply hnS
    exact (source_2_1_vi R source geometry a ha (hpos a ha) hcrit d'
      (by rwa [SimpleGraph.dist_comm])
      (Z_le_Q_of_dist_lt R d' (geometry.exists_critical d' hd') (by
        rw [hdist, geometry.distance_constant d' hd']; exact common.large_distance))
      (hcomm.trans le_sup_right)).1
  have hd'e : (cosetGraph R).dist d' e = 4 := by
    have hlo := criticalDistance_le R d' (geometry.exists_critical d' hd') hescape
    rw [geometry.distance_constant d' hd'] at hlo
    have hhi := (cosetGraph_connected R).dist_triangle (u := d') (v := a) (w := e)
    change geometry.b R ≤ _ at hlo
    omega
  have hpair : CriticalPair R d' e (geometry.exists_critical d' hd') :=
    ⟨by rw [geometry.distance_constant d' hd']; exact hd'e.trans hb.symm, hescape⟩
  have hZea : Z R e ≤ Q R a := Z_le_Q_of_dist_lt R e (geometry.exists_critical e he) (by
    rw [SimpleGraph.dist_comm, hae, geometry.distance_constant e he]; exact common.large_distance)
  have hcard' : Nat.card (⁅Z R d', Q R a⁆ : Subgroup (FreeAmalgam R)) = 2 := by
    rw [← hDmap, card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hcard
  have heq : ⁅Z R d', Z R e⁆ = ⁅Z R d', Q R a⁆ :=
    eq_of_nontrivial_le_two (commutator_mono le_rfl hZea)
      (common.critical_noncommutation d' hd' e hpair) hcard'
  have hDZe : ⁅Z R d', Q R a⁆ ≤ Z R e := by
    rw [← heq]
    apply le_normalizer_iff_commutator_le_right.mp
    exact (Z_le_stabilizer_of_dist_le d' (geometry.exists_critical d' hd') hpair.1.le).trans
      (Z_normalized R e)
  have hZer : Z R e ≤ Q R r := Z_le_Q_of_dist_lt R e (geometry.exists_critical e he) (by
    rw [her, geometry.distance_constant e he]; exact common.large_distance)
  apply hnD
  have hQrc := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes r hr))
  exact (le_centralizer_iff.mp ((hDZe.trans hZer).trans hQrc)).trans (Subgroup.centralizer_le_normalizer _)
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment
