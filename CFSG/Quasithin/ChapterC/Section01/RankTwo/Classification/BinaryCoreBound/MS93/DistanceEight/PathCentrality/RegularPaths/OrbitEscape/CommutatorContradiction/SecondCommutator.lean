module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.LocalImage
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The final R₂ calculation in MS93 (4.4.2)

The local commutator control puts R₂ in D_a: otherwise it covers Z_a
modulo D_a by a subgroup centralizing V_delta, contrary to the nontrivial
natural action of V_delta at a. If R₂ escapes Z_delta, its order is four,
so it fills the first edge commutator. That edge is normalized by Q_a;
D_a centralizes the local two-residual. Their generation of G_a therefore
proves invariance under the actual conjugator in Configuration.

The transported natural plane contains [Z_(a+2)^g,V_delta]. A subgroup
of order at most four cannot cover the natural eight modulo D_delta, so
(4.4.1)(ii) puts this commutator in D_delta. Its disjointness from the
critical line of order two proves the literal product equation and the
final containment in Z_delta D_delta.

The representation-theoretic implication from the index-two image and
proper forward span to R₂ not contained in Z_delta D_delta remains an
explicit premise of the final theorem. This file does not yet prove the
full conditional R₁/R₂ contradiction from those original inputs.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.2), printed p.893, second paragraph and final product equation.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem small_not_cover_natural
    (common : CommonFacts R source geometry) {c : Vertex R} (hc : color R c = false)
    {K : Subgroup (FreeAmalgam R)} (hK : K ≤ stabilizer R c) (hcard : Nat.card K ≤ 4) :
    ¬ Z R c ≤ K ⊔ fixedCore R c := by
  let S := stabilizer R c
  let D := (fixedCore R c).subgroupOf S
  let U₀ := (U R c).subgroupOf S
  let K₀ := K.subgroupOf S
  let := finite_stabilizer R c
  let : D.Normal := fixedCore_normal R c
  have hUS : U R c ≤ S := (MS93.U_le_Z _).trans (Z_le_stabilizer R c)
  have hDS : fixedCore R c ≤ S := fun _ hx => hx.1.1
  have hUD : U₀ ⊓ D = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    exact (Escape.EdgeTransfer.U_fixed_eq_bot (moduleFacts common) c hc).le
      ⟨hx.1, hx.2.2⟩
  have hUcard : Nat.card U₀ = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUS).toEquiv).trans
      (common.natural.card_at c hc)
  have hKcard : Nat.card K₀ ≤ 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hK).toEquiv]
    exact hcard
  have hindex : D.relIndex U₀ = 8 := by
    rw [← inf_relIndex_left, hUD, relIndex_bot_left, hUcard]
  intro h
  have hle : U₀ ≤ K₀ ⊔ D := by
    rw [← subgroupOf_sup hK hDS]
    exact comap_mono ((MS93.U_le_Z _).trans h)
  have hh := relIndex_le_of_le_right hle
    (show D.relIndex (K₀ ⊔ D) ≠ 0 from index_ne_zero_of_finite)
  rw [hindex, relIndex_sup_right] at hh
  have hsmall := Nat.le_of_dvd (show 0 < Nat.card K₀ from Nat.card_pos)
    (relIndex_dvd_card D K₀)
  omega

private theorem small_radius_displacement_le_fixed
    (common : CommonFacts R source geometry) (hlocal : LocalCommutatorControl R)
    {c : Vertex R} (hc : color R c = false)
    {A K : Subgroup (FreeAmalgam R)} (hA : A ≤ Q R c)
    (hK : K ≤ stabilizer R c) (hcard : Nat.card K ≤ 4)
    (hbound : ⁅V R c, A⁆ ≤ K) : ⁅V R c, A⁆ ≤ fixedCore R c := by
  have hQn : Q R c ≤ normalizer (fixedCore R c : Set (FreeAmalgam R)) :=
    (show Q R c ≤ stabilizer R c from fun _ hx => hx.1).trans (fixedCore_normalized R c)
  suffices hV : V R c ≤ commutatorPreimage (Q R c) A (fixedCore R c) from
    (commutator_mono hV le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hQn)
  apply (V_le_iff R hc _).mpr
  intro d hd hdist
  have hdQ : Z R d ≤ Q R c := by
    apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hd)
    rw [geometry.distance_constant d hd]
    exact lt_of_le_of_lt hdist common.large_distance
  apply le_commutatorPreimage hdQ
  by_cases hdc : d = c
  · subst d
    exact (commutator_mono le_rfl hA).trans_eq (geometry.centralizes c hc) |>.trans bot_le
  have hdist2 : (cosetGraph R).dist d c = 2 := by
    have hpos := (cosetGraph_connected R).pos_dist_of_ne hdc
    have hnot1 : (cosetGraph R).dist d c ≠ 1 := by
      intro h1
      have hadj := (cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp h1)
      exact adjacent_color_ne R hadj (hd.trans hc.symm)
    omega
  by_cases hinit : ⁅Z R d, Q R c⁆ ≤ fixedCore R c
  · exact (commutator_mono le_rfl hA).trans hinit
  apply commutator_le.mpr
  intro z hz x hx
  have hs : ⁅localZSpan R d c, zpowers x⁆ ≤ fixedCore R c := by
    by_contra hn
    have hh := (hlocal d c hd hc hdist2 hinit).2 x (hA hx) hn
    apply small_not_cover_natural common hc hK hcard
    apply hh.trans
    apply sup_le_sup_right
    rw [commutator_comm]
    exact (commutator_mono (localZSpan_le_V R hdist2.le) (zpowers_le.mpr hx)).trans hbound
  exact hs (commutator_mem_commutator (Z_le_localZSpan R d c hz) (mem_zpowers x))

namespace Configuration
variable {a a' : Vertex R} {p : CriticalPath R geometry a a'}
  (s : Configuration p) (hb : 4 < geometry.b R)

include hb

omit [Finite M] in
theorem conjugateSecond_distance :
    (cosetGraph R).dist s.conjugateSecond s.delta ≤ geometry.b R - 2 := by
  have hl := p.length_eq_b
  have hl' := s.chain.path.length_eq_b
  have hnear : (cosetGraph R).dist s.conjugateSecond
      (s.chain.path.walk.getVert (p.walk.length - 3)) = 1 := by
    rw [← s.turn, conjugateSecond, dist_act]
    have ha := p.walk.adj_getVert_succ (i := 1) (by omega)
    exact SimpleGraph.dist_eq_one_iff_adj.mpr ha.symm
  have hfar : (cosetGraph R).dist
      (s.chain.path.walk.getVert (p.walk.length - 3)) s.delta = p.walk.length - 3 := by
    rw [SimpleGraph.dist_comm]
    exact s.chain.path.dist_start (by omega)
  have ht := (cosetGraph_connected R).dist_triangle (u := s.conjugateSecond)
    (v := s.chain.path.walk.getVert (p.walk.length - 3)) (w := s.delta)
  omega

omit [Finite M] in
theorem conjugateSecond_Z_le_delta_kernel : Z R s.conjugateSecond ≤ Q R s.delta := by
  have hc : color R s.conjugateSecond = false :=
    (action_preserves_color R s.g _).trans
      ((p.vertex_color (by have hl := p.length_eq_b; omega)).mpr (by decide))
  apply Z_le_Q_of_dist_lt R s.conjugateSecond (geometry.exists_critical _ hc)
  rw [geometry.distance_constant _ hc]
  change (cosetGraph R).dist s.conjugateSecond s.delta < geometry.b R
  exact lt_of_le_of_lt (s.conjugateSecond_distance hb) (by omega)

omit [Finite M] in
theorem radius_le_conjugateSecond_stabilizer :
    V R s.delta ≤ stabilizer R s.conjugateSecond := by
  apply (V_le_iff R s.delta_color _).mpr
  intro d hd hdist
  apply Z_le_stabilizer_of_dist_le d (geometry.exists_critical d hd)
  rw [geometry.distance_constant d hd]
  change (cosetGraph R).dist d s.conjugateSecond ≤ geometry.b R
  have hle := s.conjugateSecond_distance hb
  have ht := (cosetGraph_connected R).dist_triangle (u := d) (v := s.delta)
    (w := s.conjugateSecond)
  rw [SimpleGraph.dist_comm (u := s.delta)] at ht
  omega

theorem critical_commutator_le_delta_natural (source : LocalSource L R) :
    ⁅Z R (p.walk.getVert 2), Z R s.delta⁆ ≤ U R s.delta := by
  rw [commutator_comm]
  exact (commutator_mono le_rfl (s.second_Z_le_delta_stabilizer hb)).trans_eq
    (Escape.Initial.Z_commutator_stabilizer source s.delta s.delta_color)

theorem conjugate_commutator_le_fixed_of_le_second
    (common : CommonFacts R source geometry) (hlocal : LocalCommutatorControl R)
    (hbound : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≤ s.secondCommutator) :
    ⁅Z R s.conjugateSecond, V R s.delta⁆ ≤ fixedCore R s.delta := by
  rw [commutator_comm] at hbound ⊢
  exact small_radius_displacement_le_fixed common hlocal s.delta_color
    (s.conjugateSecond_Z_le_delta_kernel hb)
    ((s.secondCommutator_le_radius hb).trans
      (geometry.V_local s.delta s.delta_color (by
        rw [geometry.distance_constant _ s.delta_color]; exact common.large_distance)))
    (s.secondCommutator_card_le_four hb common) hbound

/-- The critical line lies in the natural summand at delta, whereas the
conjugate commutator lies in its fixed core. -/
theorem critical_inf_conjugate_eq_bot
    (common : CommonFacts R source geometry) (hlocal : LocalCommutatorControl R)
    (hbound : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≤ s.secondCommutator) :
    ⁅Z R (p.walk.getVert 2), Z R s.delta⁆ ⊓ ⁅Z R s.conjugateSecond, V R s.delta⁆ = ⊥ := by
  apply le_bot_iff.mp
  rw [← Escape.EdgeTransfer.U_fixed_eq_bot (moduleFacts common) s.delta s.delta_color]
  exact inf_le_inf (s.critical_commutator_le_delta_natural hb source)
    ((s.conjugate_commutator_le_fixed_of_le_second hb common hlocal hbound).trans inf_le_right)

/-- The two disjoint nonzero factors fill the subgroup of order at most four. -/
theorem secondCommutator_eq_critical_sup_conjugate
    (common : CommonFacts R source geometry) (hlocal : LocalCommutatorControl R)
    (hmove : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥)
    (hbound : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≤ s.secondCommutator) :
    s.secondCommutator =
      ⁅Z R (p.walk.getVert 2), Z R s.delta⁆ ⊔ ⁅Z R s.conjugateSecond, V R s.delta⁆ := by
  let C := ⁅Z R (p.walk.getVert 2), Z R s.delta⁆
  let D := ⁅Z R s.conjugateSecond, V R s.delta⁆
  let E := C ⊔ D
  have hE : E ≤ s.secondCommutator :=
    sup_le (s.critical_commutator_le_secondCommutator hb) hbound
  let := finite_stabilizer R s.delta
  let : Finite s.secondCommutator := Finite.of_injective
    (inclusion ((s.secondCommutator_le_radius hb).trans
      (geometry.V_local s.delta s.delta_color (by
        rw [geometry.distance_constant _ s.delta_color]; exact common.large_distance))))
    (inclusion_injective _)
  let : Finite E := Finite.of_injective (inclusion hE) (inclusion_injective _)
  have hC : Nat.card C = 2 := s.critical_commutator_card hb common
  have hCD : C ⊓ D = ⊥ := s.critical_inf_conjugate_eq_bot hb common hlocal hbound
  have hne : C ≠ E := by
    intro he
    apply hmove
    apply le_bot_iff.mp
    intro x hx
    exact hCD.le ⟨(show D ≤ C from he ▸ le_sup_right) hx, hx⟩
  have hlarge : 2 < Nat.card E := by
    by_contra! hh
    exact hne (eq_of_le_of_card_ge (show C ≤ E from le_sup_left) (by omega))
  have hdiv : 2 ∣ Nat.card E := hC ▸ card_dvd_of_le (show C ≤ E from le_sup_left)
  have hsmall := s.secondCommutator_card_le_four hb common
  exact (eq_of_le_of_card_ge hE (by omega)).symm

/-- The join in the final equation is the literal subgroup set product. -/
theorem secondCommutator_eq_critical_mul_conjugate
    (common : CommonFacts R source geometry) (hlocal : LocalCommutatorControl R)
    (hmove : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥)
    (hbound : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≤ s.secondCommutator) :
    (s.secondCommutator : Set (FreeAmalgam R)) =
      (⁅Z R (p.walk.getVert 2), Z R s.delta⁆ : Subgroup (FreeAmalgam R)) *
        (⁅Z R s.conjugateSecond, V R s.delta⁆ : Subgroup (FreeAmalgam R)) := by
  have hcentral : ⁅Z R (p.walk.getVert 2), Z R s.delta⁆ ≤
      centralizer (↑(⁅Z R s.conjugateSecond, V R s.delta⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) :=
    (s.critical_commutator_le_secondCommutator hb).trans
      ((commutator_eq_bot_iff_le_centralizer.mp (s.secondCommutator_centralizes_radius hb)).trans
        (centralizer_le (hbound.trans (s.secondCommutator_le_radius hb))))
  rw [s.secondCommutator_eq_critical_sup_conjugate hb common hlocal hmove hbound]
  exact coe_mul_of_left_le_normalizer_right _ _
    (hcentral.trans (Subgroup.centralizer_le_normalizer _))

/-- The final source product lies in Z_delta D_delta. -/
theorem secondCommutator_le_delta_Z_sup_fixed_of_conjugate_le
    (common : CommonFacts R source geometry) (hlocal : LocalCommutatorControl R)
    (hmove : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥)
    (hbound : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≤ s.secondCommutator) :
    s.secondCommutator ≤ Z R s.delta ⊔ fixedCore R s.delta := by
  rw [s.secondCommutator_eq_critical_sup_conjugate hb common hlocal hmove hbound]
  exact sup_le_sup (s.critical_commutator_le_delta_Z hb)
    (s.conjugate_commutator_le_fixed_of_le_second hb common hlocal hbound)

/-- An invariant order-four subgroup of the natural eight contains all
commutators. The remaining fixed summand of Z centralizes the local actor. -/
theorem conjugate_commutator_le_second_of_natural
    (common : CommonFacts R source geometry)
    (hcard : Nat.card s.secondCommutator = 4)
    (hnatural : s.secondCommutator ≤ U R s.conjugateSecond) :
    ⁅Z R s.conjugateSecond, V R s.delta⁆ ≤ s.secondCommutator := by
  have hc : color R s.conjugateSecond = false :=
    (action_preserves_color R s.g _).trans
      ((p.vertex_color (by have hl := p.length_eq_b; omega)).mpr (by decide))
  have hindex : s.secondCommutator.relIndex (U R s.conjugateSecond) = 2 := by
    have hh := (s.secondCommutator.subgroupOf (U R s.conjugateSecond)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hnatural).toEquiv, hcard,
      common.natural.card_at _ hc] at hh
    change 4 * s.secondCommutator.relIndex (U R s.conjugateSecond) = 8 at hh
    omega
  have hWA : V R s.delta ≤ centralizer (s.secondCommutator : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (s.secondCommutator_centralizes_radius hb))
  have hU := commutator_le_of_normalized_index_two _ _ _ hnatural hindex
    ((s.radius_le_conjugateSecond_stabilizer hb).trans (U_normalized _))
    (hWA.trans (Subgroup.centralizer_le_normalizer _))
  have hZ : Z R s.conjugateSecond ≤
      centralizer (s.secondCommutator : Set (FreeAmalgam R)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes _ hc)).trans
      (centralizer_le (hnatural.trans ((MS93.U_le_Z _).trans
        ((Z_le_VBall R _ 2).trans (V_le_Q R hc common.large_distance)))))
  have hpre : Z R s.conjugateSecond ≤ commutatorPreimage
      (Z R s.conjugateSecond) (V R s.delta) s.secondCommutator := by
    conv_lhs => rw [(naturalStructure common).decomposition_at _ hc]
    apply sup_le (le_commutatorPreimage (MS93.U_le_Z _) hU)
    exact le_commutatorPreimage inf_le_left
      ((commutator_eq_bot_iff_le_centralizer.mpr
        (inf_le_right.trans (centralizer_le (s.radius_le_conjugateSecond_stabilizer hb)))).le.trans bot_le)
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _
      (hZ.trans (Subgroup.centralizer_le_normalizer _)))

/-- The source noncontainment and transport into the conjugate natural
summand suffice for the final contradiction. These two premises still
require the preceding source calculation. -/
theorem false_of_noncontainment_and_conjugate_natural
    (common : CommonFacts R source geometry) (hlocal : LocalCommutatorControl R)
    (hmove : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥)
    (hnot : ¬ s.secondCommutator ≤ Z R s.delta ⊔ fixedCore R s.delta)
    (hnatural : s.secondCommutator ≤ U R s.conjugateSecond) : False := by
  have hcard := s.secondCommutator_card_four_of_not_le_delta_Z hb common
    (fun h => hnot (h.trans le_sup_left))
  exact hnot (s.secondCommutator_le_delta_Z_sup_fixed_of_conjugate_le hb common hlocal hmove
    (s.conjugate_commutator_le_second_of_natural hb common hcard hnatural))

/-- Noncontainment gives order four, which fills the actual edge commutator. -/
theorem secondCommutator_eq_first_edge_of_not_le_delta_Z
    (common : CommonFacts R source geometry)
    (hnot : ¬ s.secondCommutator ≤ Z R s.delta) :
    s.secondCommutator = edgeCommutator R (p.walk.getVert 2) (p.walk.getVert 1) := by
  have hl := p.length_eq_b
  have hc : color R (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have ht : color R (p.walk.getVert 1) = true := by
    have hh := p.vertex_color (i := 1) (by omega)
    cases h : color R (p.walk.getVert 1) <;> simp_all
  have hat : Adjacent R a (p.walk.getVert 1) := by
    have hh := p.walk.adj_getVert_succ (i := 0) (by omega)
    simpa only [SimpleGraph.Walk.getVert_zero] using (cosetGraph_adj R _ _).mp hh
  have hct : Adjacent R (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hle : s.secondCommutator ≤ edgeCommutator R (p.walk.getVert 2) (p.walk.getVert 1) :=
    commutator_mono le_rfl (inf_le_right.trans (Q_le_adjacent_h R ht hat))
  have hsmall := Escape.EdgeTransfer.edge_displacement_card_le_four
    common.large_distance (moduleFacts common) _ _ hc hct
  have hU := Escape.EdgeTransfer.edge_commutator_le_natural
    common.large_distance (moduleFacts common) _ _ hc hct
  let : Finite (U R (p.walk.getVert 2)) := Nat.finite_of_card_ne_zero
    (by rw [common.natural.card_at _ hc]; decide)
  let : Finite (edgeCommutator R (p.walk.getVert 2) (p.walk.getVert 1)) :=
    Finite.of_injective (inclusion hU) (inclusion_injective _)
  exact eq_of_le_of_card_ge hle
    (by rw [s.secondCommutator_card_four_of_not_le_delta_Z hb common hnot]; exact hsmall)

/-- Actual conjugation invariance transports R₂ into the natural summand at
(a+2)^g. No abstract identification of the two natural modules is used. -/
theorem secondCommutator_le_conjugate_natural_of_map_eq
    (common : CommonFacts R source geometry)
    (hmap : s.secondCommutator.map (MulAut.conj s.g⁻¹).toMonoidHom = s.secondCommutator) :
    s.secondCommutator ≤ U R s.conjugateSecond := by
  have hh := map_mono (f := (MulAut.conj s.g⁻¹).toMonoidHom)
    (s.secondCommutator_le_second_natural hb common)
  rwa [hmap, ← U_act] at hh

/-- The literal transported edge identity follows from invariance under the
same g stored in Configuration and its prescribed neighbor image. -/
theorem secondCommutator_eq_conjugate_edge
    (common : CommonFacts R source geometry)
    (hnot : ¬ s.secondCommutator ≤ Z R s.delta)
    (hmap : s.secondCommutator.map (MulAut.conj s.g⁻¹).toMonoidHom = s.secondCommutator) :
    s.secondCommutator = edgeCommutator R s.conjugateSecond
      (s.chain.path.walk.getVert (p.walk.length - 3)) := by
  rw [← s.turn]
  change s.secondCommutator = edgeCommutator R
    (act R s.g (p.walk.getVert 2)) (act R s.g (p.walk.getVert 1))
  rw [edgeCommutator, Z_act, Q_act, ← map_commutator]
  change s.secondCommutator =
    (edgeCommutator R (p.walk.getVert 2) (p.walk.getVert 1)).map _
  rw [← s.secondCommutator_eq_first_edge_of_not_le_delta_Z hb common hnot, hmap]

/-- Assembly of the R₂ contradiction after its noncontainment and conjugation
invariance have been established. The order, the conjugate commutator bound,
the fixed-core containment and the final product are all derived. -/
theorem false_of_noncontainment_and_map_eq
    (common : CommonFacts R source geometry) (hlocal : LocalCommutatorControl R)
    (hmove : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥)
    (hnot : ¬ s.secondCommutator ≤ Z R s.delta ⊔ fixedCore R s.delta)
    (hmap : s.secondCommutator.map (MulAut.conj s.g⁻¹).toMonoidHom = s.secondCommutator) :
    False :=
  s.false_of_noncontainment_and_conjugate_natural hb common hlocal hmove hnot
    (s.secondCommutator_le_conjugate_natural_of_map_eq hb common hmap)

omit [Finite M] in
/-- Every radius generator at a is at distance at most b from delta. -/
theorem start_radius_le_delta_stabilizer : V R a ≤ stabilizer R s.delta := by
  apply (V_le_iff R p.start_color _).mpr
  intro d hd hdist
  apply Z_le_stabilizer_of_dist_le d (geometry.exists_critical d hd)
  rw [geometry.distance_constant d hd]
  change (cosetGraph R).dist d s.delta ≤ geometry.b R
  have ht := (cosetGraph_connected R).dist_triangle (u := d) (v := a) (w := s.delta)
  rw [SimpleGraph.dist_comm (u := a), s.distance_start hb] at ht
  omega

/-- Source (4.4.1)(ii) puts R₂ in D_a. Otherwise it covers Z_a modulo
D_a by a subgroup centralizing V_delta, contradicting the nontrivial action
of V_delta on the natural summand of Z_a. -/
theorem secondCommutator_le_start_fixed
    (common : CommonFacts R source geometry) (hlocal : LocalCommutatorControl R) :
    s.secondCommutator ≤ fixedCore R a := by
  have hl := p.length_eq_b
  have hc : color R (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hd : (cosetGraph R).dist (p.walk.getVert 2) a = 2 := by
    rw [SimpleGraph.dist_comm, p.dist_start (by omega)]
  by_cases hinit : ⁅Z R (p.walk.getVert 2), Q R a⁆ ≤ fixedCore R a
  · exact (commutator_mono le_rfl inf_le_right).trans hinit
  let W := localZSpan R (p.walk.getVert 2) a
  have hWQ : W ≤ Q R a := localZSpan_le_Q R p.start_color hd.le common.large_distance
  have hWS : W ≤ stabilizer R s.delta :=
    (localZSpan_le_V R hd.le).trans (s.start_radius_le_delta_stabilizer hb)
  have hDnorm : Q R a ≤ normalizer (fixedCore R a : Set (FreeAmalgam R)) :=
    (show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (fixedCore_normalized R a)
  have hDS : ⁅fixedCore R a, V R s.delta⁆ ≤ fixedCore R a :=
    le_normalizer_iff_commutator_le_left.mp
      ((s.radius_le_start_stabilizer hb).trans (fixedCore_normalized R a))
  let := s.radius_elementary hb
  have hVV : V R s.delta ≤ centralizer (V R s.delta : Set (FreeAmalgam R)) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  apply commutator_le.mpr
  intro z hz x hx
  have hWX : ⁅W, zpowers x⁆ ≤ fixedCore R a := by
    by_contra hn
    have hcover := (hlocal _ _ hc p.start_color hd hinit).2 x hx.2 hn
    have hKQ : ⁅zpowers x, W⁆ ≤ Q R a :=
      (commutator_mono (zpowers_le.mpr hx.2) hWQ).trans (commutator_le_self _)
    have hKV : ⁅zpowers x, W⁆ ≤ V R s.delta :=
      (commutator_mono (zpowers_le.mpr hx.1) le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (hWS.trans (MS93.V_normalized s.delta)))
    have hKzero : ⁅⁅zpowers x, W⁆, V R s.delta⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (hKV.trans hVV)
    have hpre : Z R a ≤ commutatorPreimage (Q R a) (V R s.delta) (fixedCore R a) :=
      hcover.trans (sup_le (le_commutatorPreimage hKQ (hKzero.le.trans bot_le))
        (le_commutatorPreimage inf_le_left hDS))
    have hCD : ⁅Z R a, V R s.delta⁆ ≤ fixedCore R a :=
      (commutator_mono hpre le_rfl).trans
        (commutator_commutatorPreimage_le _ _ _ hDnorm)
    have hCU : ⁅Z R a, V R s.delta⁆ ≤ U R a :=
      (commutator_mono le_rfl (s.radius_le_start_stabilizer hb)).trans_eq
        (Escape.Initial.Z_commutator_stabilizer source a p.start_color)
    apply s.start_commutator_ne_bot hb common
    apply le_bot_iff.mp
    rw [← Escape.EdgeTransfer.U_fixed_eq_bot (moduleFacts common) a p.start_color]
    exact le_inf hCU (hCD.trans inf_le_right)
  exact hWX (commutator_mem_commutator (Z_le_localZSpan R _ _ hz) (mem_zpowers x))

/-- Q_a normalizes the first edge and Ltilde_a centralizes R₂. The source
factorization G_a = Ltilde_a Q_a therefore normalizes R₂. -/
theorem secondCommutator_normalized_of_not_le_delta_Z
    (common : CommonFacts R source geometry) (hlocal : LocalCommutatorControl R)
    (hnot : ¬ s.secondCommutator ≤ Z R s.delta) :
    stabilizer R a ≤ normalizer (s.secondCommutator : Set (FreeAmalgam R)) := by
  have hl := p.length_eq_b
  have ht : color R (p.walk.getVert 1) = true := by
    have hh := p.vertex_color (i := 1) (by omega)
    cases h : color R (p.walk.getVert 1) <;> simp_all
  have hat : Adjacent R a (p.walk.getVert 1) := by
    have hh := p.walk.adj_getVert_succ (i := 0) (by omega)
    simpa only [SimpleGraph.Walk.getVert_zero] using (cosetGraph_adj R _ _).mp hh
  have hct : Adjacent R (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  rw [← source.local_generation a p.start_color]
  apply sup_le
  · exact (le_centralizer_iff.mp
      ((s.secondCommutator_le_start_fixed hb common hlocal).trans inf_le_right)).trans
        (Subgroup.centralizer_le_normalizer _)
  · rw [s.secondCommutator_eq_first_edge_of_not_le_delta_Z hb common hnot]
    intro g hg
    have hgQ := Q_le_adjacent_h R ht hat hg
    have hgsecond : g ∈ stabilizer R (p.walk.getVert 2) :=
      hgQ.2 _ (adjacent_symm R hct)
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅Z R (p.walk.getVert 2), Q R (p.walk.getVert 1)⁆).map
      (MulAut.conj g).toMonoidHom = _
    have hZ := mem_normalizer_iff_map_conj_eq.mp (Z_normalized R _ hgsecond)
    have hQ := mem_normalizer_iff_map_conj_eq.mp (Q_normalized R _ hgQ.1)
    change (Z R (p.walk.getVert 2)).map (MulAut.conj g).toMonoidHom = _ at hZ
    change (Q R (p.walk.getVert 1)).map (MulAut.conj g).toMonoidHom = _ at hQ
    rw [map_commutator, hZ, hQ]
    rfl

/-- The actual g in Configuration preserves R₂; no residual replacement of g
or abstract module transport is needed. -/
theorem secondCommutator_map_eq_of_not_le_delta_Z
    (common : CommonFacts R source geometry) (hlocal : LocalCommutatorControl R)
    (hnot : ¬ s.secondCommutator ≤ Z R s.delta) :
    s.secondCommutator.map (MulAut.conj s.g⁻¹).toMonoidHom = s.secondCommutator :=
  mem_normalizer_iff_map_conj_eq.mp
    (s.secondCommutator_normalized_of_not_le_delta_Z hb common hlocal hnot
      ((stabilizer R a).inv_mem s.mem_stabilizer))

/-- The complete final R₂ calculation, conditional only on the preceding
source noncontainment. It proves both edge identities, their transport,
the conjugate fixed-core bound, and the final product contradiction. -/
theorem false_of_secondCommutator_not_le_delta_Z_sup_fixed
    (common : CommonFacts R source geometry) (hlocal : LocalCommutatorControl R)
    (hmove : ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥)
    (hnot : ¬ s.secondCommutator ≤ Z R s.delta ⊔ fixedCore R s.delta) : False :=
  s.false_of_noncontainment_and_map_eq hb common hlocal hmove hnot
    (s.secondCommutator_map_eq_of_not_le_delta_Z hb common hlocal
      (fun h => hnot (h.trans le_sup_left)))

end Configuration
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
