module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Center.DerivedFixed.Displacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Moving.Symmetry.SmallAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.NormalizerTransfer

/-!
# Simultaneous escape of a radius generator and its displacement

If the radius-derived subgroup is not residual-fixed, one M-layer at distance
two has nonfixed displacement. Its join with the radius center is not normal:
local edge transitivity would make it centralize every radius generator.
Its displacement is also not normal: the edge bound gives order at most four,
and the local two-residual fixes every normal subgroup of that size.

Both groups are normal in their common edge kernel. The critical opposite
layer generates the local residual through its actual stabilizer conjugates,
so source (2.1)(vii) makes both groups escape under the same conjugation.
No center-failure hypothesis is needed for these selection steps.

Source: Meierfrankenfeld--Stellmacher (1993), (2.1)(vii) and (4.6.1),
printed pp.855--856 and 900--901; the order-four argument is the binary
natural-module specialization.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial.DerivedFixed
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
private theorem center_centralizes_radius (a : Vertex R) :
    (center (V R a)).map (V R a).subtype ≤ centralizer (V R a : Set (FreeAmalgam R)) := by
  rintro _ ⟨x,hx,rfl⟩ y hy
  exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)

omit [Finite M] in
/-- A nonfixed radius-derived subgroup has a nonfixed generator displacement
at an M-vertex at distance exactly two. -/
theorem exists_nonfixed_generator (common : CommonFacts R source geometry)
    (a : Vertex R) (ha : color R a = false)
    (hnot : ¬ ⁅V R a,V R a⁆ ≤ fixedCore R a) :
    ∃ d, color R d = false ∧ (cosetGraph R).dist d a = 2 ∧
      ¬ ⁅Z R d,V R a⁆ ≤ fixedCore R a := by
  classical
  let I := {d : Vertex R // color R d = false ∧ (cosetGraph R).dist d a ≤ 2}
  have hV : V R a = ⨆ d : I, Z R d.val := by
    apply le_antisymm
    · apply radius_le_of_generators a ha
      intro d hd hdist
      exact le_iSup_of_le (⟨d,hd,hdist⟩ : I) le_rfl
    · exact iSup_le fun d => le_iSup_of_le d.val (le_iSup_of_le d.property.2 le_rfl)
  obtain ⟨d,hd⟩ : ∃ d : I, ¬ ⁅Z R d.val,V R a⁆ ≤ fixedCore R a := by
    by_contra! h
    apply hnot
    conv_lhs => lhs; rw [hV]
    rw [commutator_iSup_of_le (fun d : I => Z R d.val) (V R a) (fun d =>
      le_iSup_of_le d.val (le_iSup_of_le d.property.2 le_rfl))]
    exact iSup_le h
  have hne : d.val ≠ a := by
    intro heq
    apply hd
    rw [heq]
    exact (commutator_mono le_rfl (radius_le_Q common a ha)).trans
      ((geometry.centralizes a ha).le.trans bot_le)
  have heven : Even ((cosetGraph R).dist d.val a) := by
    obtain ⟨p,hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist d.val a
    rw [← hp, walk_even_iff_color_eq, d.property.1, ha]
  have hpos : (cosetGraph R).dist d.val a ≠ 0 :=
    fun h => hne ((cosetGraph_connected R).dist_eq_zero_iff.mp h)
  have hle := d.property.2
  obtain ⟨n,hn⟩ := heven
  exact ⟨d.val,d.property.1,by omega,hd⟩

/-- Normality of Z_d Z(V_a) would make its generators commute with every
radius layer, by moving their common edge to each neighboring edge. -/
theorem center_join_nonnormal (common : CommonFacts R source geometry)
    (a d : Vertex R) (ha : color R a = false) (hd : color R d = false)
    (hda : (cosetGraph R).dist d a = 2)
    (hnot : ¬ ⁅Z R d,V R a⁆ ≤ fixedCore R a) :
    ¬ ((Z R d ⊔ (center (V R a)).map (V R a).subtype).subgroupOf
      (stabilizer R a)).Normal := by
  let C := (center (V R a)).map (V R a).subtype
  let S := Z R d ⊔ C
  have hdV : Z R d ≤ V R a := le_iSup_of_le d (le_iSup_of_le hda.le le_rfl)
  have hSV : S ≤ V R a := sup_le hdV (map_subtype_le _)
  have hSQ := hSV.trans (radius_le_Q common a ha)
  intro hnormal
  have hSN : stabilizer R a ≤ normalizer S :=
    (normal_subgroupOf_iff_le_normalizer (hSQ.trans (fun _ hx => hx.1))).mp hnormal
  obtain ⟨t,hat,hdt⟩ := exists_common_neighbor_of_dist_two R a d (by
    rw [SimpleGraph.dist_comm]; exact hda)
  have hVS : V R a ≤ centralizer (S : Set (FreeAmalgam R)) := by
    apply radius_le_of_generators a ha
    intro e he hea
    apply le_centralizer_iff.mp
    by_cases hzero : (cosetGraph R).dist e a = 0
    · have heq := (cosetGraph_connected R).dist_eq_zero_iff.mp hzero
      subst e
      exact hSQ.trans (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha)))
    have htwo : (cosetGraph R).dist a e = 2 := by
      have heven : Even ((cosetGraph R).dist e a) := by
        obtain ⟨p,hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist e a
        rw [← hp, walk_even_iff_color_eq, he, ha]
      obtain ⟨n,hn⟩ := heven
      rw [SimpleGraph.dist_comm]
      omega
    obtain ⟨s,has,hes⟩ := exists_common_neighbor_of_dist_two R a e htwo
    obtain ⟨g,hga,hgt⟩ := stabilizer_transitive_neighbors R a hat has
    have hfix : act R g a = a := hga
    have hds : Adjacent R (act R g d) s := by
      rw [← hgt]
      exact (adjacent_act_iff R g d t).mpr hdt
    have hde : (cosetGraph R).dist (act R g d) e ≤ 2 := by
      have htri := (cosetGraph_connected R).dist_triangle (u := act R g d) (v := s) (w := e)
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hds),
        SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr (adjacent_symm R hes))] at htri
      exact htri
    have hdg : color R (act R g d) = false := by rwa [action_preserves_color]
    have hdQ : Z R (act R g d) ≤ Q R e := Z_le_Q_of_dist_lt R _
      (geometry.exists_critical _ hdg) (by
        rw [geometry.distance_constant _ hdg]
        exact hde.trans_lt common.large_distance)
    have hSmap : S = Z R (act R g d) ⊔ C := by
      have hmap := mem_normalizer_iff_map_conj_eq.mp (hSN ((stabilizer R a).inv_mem hga))
      change S.map (MulAut.conj g⁻¹).toMonoidHom = S at hmap
      have hCmap : C.map (MulAut.conj g⁻¹).toMonoidHom = C :=
        mem_normalizer_iff_map_conj_eq.mp (radius_center_normalized a
          ((stabilizer R a).inv_mem hga))
      rw [show S = Z R d ⊔ C from rfl, Subgroup.map_sup, ← Z_act, hCmap] at hmap
      exact hmap.symm
    rw [hSmap]
    apply sup_le
    · exact hdQ.trans (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes e he)))
    · exact (center_centralizes_radius a).trans (centralizer_le
        (show Z R e ≤ V R a from le_iSup_of_le e (le_iSup_of_le hea le_rfl)))
  apply hnot
  have hc : ⁅Z R d,V R a⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (le_sup_left.trans (le_centralizer_iff.mpr hVS))
  rw [hc]
  exact bot_le

/-- A nonfixed generator displacement cannot be normal in the local group:
its edge-displacement order is at most four and the two-residual has no
nontrivial action on such a normal subgroup. -/
theorem generator_commutator_nonnormal (common : CommonFacts R source geometry)
    (a d : Vertex R) (ha : color R a = false) (hd : color R d = false)
    (hda : (cosetGraph R).dist d a = 2)
    (hnot : ¬ ⁅Z R d,V R a⁆ ≤ fixedCore R a) :
    ¬ ((⁅Z R d,V R a⁆).subgroupOf (stabilizer R a)).Normal := by
  let K := ⁅Z R d,V R a⁆
  have hdV : Z R d ≤ V R a := le_iSup_of_le d (le_iSup_of_le hda.le le_rfl)
  have hKQ : K ≤ Q R a := ((commutator_mono hdV le_rfl).trans
    (commutator_le_self _)).trans (radius_le_Q common a ha)
  have hKG := hKQ.trans (show Q R a ≤ stabilizer R a from fun _ hx => hx.1)
  obtain ⟨t,hat,hdt⟩ := exists_common_neighbor_of_dist_two R a d (by
    rw [SimpleGraph.dist_comm]; exact hda)
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have hKt : K ≤ ⁅Z R d,Q R t⁆ := commutator_mono le_rfl
    ((radius_le_Q common a ha).trans (Q_le_adjacent_h R ht hat))
  have hU := Escape.EdgeTransfer.edge_commutator_le_natural
    common.large_distance (moduleFacts common) d t hd hdt
  let : Finite (U R d) := Nat.finite_of_card_ne_zero (by
    rw [common.natural.card_at d hd]; decide)
  let : Finite (⁅Z R d,Q R t⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hU) (inclusion_injective _)
  have hsmall : Nat.card K ≤ 4 := (card_le_of_le hKt).trans
    (Escape.EdgeTransfer.edge_displacement_card_le_four
      common.large_distance (moduleFacts common) d t hd hdt)
  intro hn
  let := finite_stabilizer R a
  let : (K.subgroupOf (stabilizer R a)).Normal := hn
  obtain ⟨frame⟩ := ModuleAlternatives.SourceCalculation.exists_frame a ha
  have hp : IsPGroup 2 (frame.projection source).ker := by
    rw [frame.projection_kernel source]
    exact (Q_isPGroup R source.two_group source.core_le a ha).comap_subtype
  have hz := Escape.Propagation.Backward.Moving.Symmetry.small_normal_centralizes_residual
    (frame.projection source) (frame.projection_surjective source) hp
    (K.subgroupOf (stabilizer R a)) (by
      rw [Nat.card_congr (subgroupOfEquivOfLe hKG).toEquiv]
      exact hsmall)
  have hz' := congrArg (Subgroup.map (stabilizer R a).subtype) hz
  rw [map_commutator, map_subgroupOf_eq_of_le hKG, Subgroup.map_bot] at hz'
  exact hnot (le_inf hKQ (commutator_eq_bot_iff_le_centralizer.mp hz'))

/-- Both escape clauses use the same local conjugator. Relative normality
is checked in the common edge kernel, and conjugate generation in G_a. -/
theorem simultaneous_generator_escape (common : CommonFacts R source geometry)
    (a r : Vertex R) (ha : color R a = false)
    (hcrit : CriticalPair R a r (geometry.exists_critical a ha))
    (hnot : ¬ ⁅V R a,V R a⁆ ≤ fixedCore R a) :
    ∃ d, color R d = false ∧ (cosetGraph R).dist d a = 2 ∧
      ¬ Z R r ≤ normalizer (Z R d ⊔ (center (V R a)).map (V R a).subtype : Subgroup (FreeAmalgam R)) ∧
      ¬ Z R r ≤ normalizer (⁅Z R d,V R a⁆ : Subgroup (FreeAmalgam R)) := by
  obtain ⟨d,hd,hda,hbad⟩ := exists_nonfixed_generator common a ha hnot
  obtain ⟨t,hat,hdt⟩ := exists_common_neighbor_of_dist_two R a d (by
    rw [SimpleGraph.dist_comm]; exact hda)
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have hTa : Q R t ≤ stabilizer R a := by rw [Q_h_eq_edge R ht hat]; exact inf_le_left
  have hTd : Q R t ≤ stabilizer R d := by rw [Q_h_eq_edge R ht hdt]; exact inf_le_left
  have hVaT := (radius_le_Q common a ha).trans (Q_le_adjacent_h R ht hat)
  have hdV : Z R d ≤ V R a := le_iSup_of_le d (le_iSup_of_le hda.le le_rfl)
  let C := (center (V R a)).map (V R a).subtype
  have hST : Z R d ⊔ C ≤ Q R t := (sup_le hdV (map_subtype_le _)).trans hVaT
  have hKT : ⁅Z R d,V R a⁆ ≤ Q R t :=
    ((commutator_mono hdV le_rfl).trans (commutator_le_self _)).trans hVaT
  have hSN : Q R t ≤ normalizer (Z R d ⊔ C : Subgroup (FreeAmalgam R)) :=
    (le_inf (hTd.trans (Z_normalized R d))
      (hTa.trans (radius_center_normalized a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hKN : Q R t ≤ normalizer (⁅Z R d,V R a⁆ : Subgroup (FreeAmalgam R)) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp ((hTd.trans (Z_normalized R d)) hx),
      mem_normalizer_iff_map_conj_eq.mp ((hTa.trans (V_normalized a)) hx)]
  have hr := critical_endpoint_color R a ha (geometry.exists_critical a ha) hcrit
  have hout := (common.critical_reverse a ha r hr hcrit).2
  have hrG : Z R r ≤ stabilizer R a := critical_Z_le_stabilizer R geometry a ha
    (by rw [geometry.distance_constant a ha]; exact lt_trans (by decide : 0 < 2) common.large_distance)
    hcrit
  let N := NormalizerTransfer.conjugatesIn (Z R r) (stabilizer R a)
  have hNG : N ≤ stabilizer R a := NormalizerTransfer.conjugatesIn_le _ _ hrG
  have hrN : Z R r ≤ N := by
    intro x hx
    apply le_iSup (fun g : stabilizer R a => NormalizerTransfer.rightConjugate (Z R r) g) 1
    exact ⟨x,hx,by simp⟩
  have hLN : Ltilde R a ≤ N := NaturalStructure.Exclusion.residual_le_of_normal_not_le
    source a ha N hNG
    (normal_subgroupOf_of_le_normalizer (NormalizerTransfer.conjugatesIn_normalized _ _))
    (fun h => hout (hrN.trans h))
  have hgen : N ⊔ Q R t = stabilizer R a := by
    apply le_antisymm (sup_le hNG hTa)
    rw [← source.local_generation a ha]
    exact sup_le (hLN.trans le_sup_left) ((Q_le_adjacent_h R ht hat).trans le_sup_right)
  obtain ⟨g,hga,hnS,hnK⟩ := source_2_1_vii R a r t ha hat (Z R d ⊔ C) ⁅Z R d,V R a⁆
    hST hKT (normal_subgroupOf_of_le_normalizer hSN)
    (normal_subgroupOf_of_le_normalizer hKN)
    (center_join_nonnormal common a d ha hd hda hbad)
    (generator_commutator_nonnormal common a d ha hd hda hbad) hgen
  have hfix : act R g a = a := hga
  have hC : C.map (MulAut.conj g⁻¹).toMonoidHom = C :=
    mem_normalizer_iff_map_conj_eq.mp (radius_center_normalized a
      ((stabilizer R a).inv_mem hga))
  rw [Subgroup.map_sup, ← Z_act, hC] at hnS
  rw [map_commutator, ← Z_act, ← V_act, hfix] at hnK
  refine ⟨act R g d,by rwa [action_preserves_color],?_,hnS,hnK⟩
  rw [← hfix, dist_act]
  exact hda

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial.DerivedFixed
