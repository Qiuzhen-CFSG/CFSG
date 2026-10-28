module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedRadiusOriginalFixedPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedRadiusFixedIndex
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedRadiusDistanceSix

/-!
# Noncentral paired displacement at critical distance greater than six

The literal paired commutator cannot centralize its preceding vertex. Such
centrality would bound a joined radius image by q. Two applications of the
full two-kernel growth theorem then produce a displacement with central index
greater than q. Its index modulo the next seed is at most q; the retained
triple intersections and the same selected orbit put that kernel in its full
vertex center, a contradiction. All endpoints remain the actual paired
endpoints, and all fixed attachments remain in the relative indices.

Source: the displacement comparison in MS93 (5.11), printed p.924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

private theorem forget_original {M : Type*} [Group M] {R : Subgroup M}
    {geometry : Geometry R} {q : ℕ} {p : CriticalSegment geometry} {v w : Vertex R}
    (hc : pairedRadiusOriginalFixedChoice geometry q p v w) :
    pairedRadiusChoice geometry q p v w := by
  obtain ⟨hp,x,hx,ha,hv,hi,hg,hg',hf,_,_⟩ := hc
  exact ⟨hp,x,hx,ha,hv,hi,hg,hg',hf⟩

private theorem ordinary_links {M : Type*} [Group M] {R : Subgroup M}
    {geometry : Geometry R} {q : ℕ} {s : ℕ → CriticalSegment geometry}
    (hs : ∀ i, BackwardLink geometry (pairedRadiusOriginalFixedChoice geometry q)
      (s i) (s (i+1))) :
    ∀ i, BackwardLink geometry (pairedRadiusChoice geometry q) (s i) (s (i+1)) := by
  intro i
  obtain ⟨t,hc,hat,hvt,hfirst⟩ := (hs i).choice
  exact ⟨⟨t,forget_original hc,hat,hvt,hfirst⟩,(hs i).last_eq,(hs i).overlap⟩

private theorem fixed_seed_le_neighbor_seed
    {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    {a t c : Vertex R} (ha : color R a=false) (hc : color R c=false)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    (D : Subgroup (FreeAmalgam R)) (hDZ : D ≤ Z R a)
    (hDC : D ≤ centralizer (stabilizer R a : Set (FreeAmalgam R))) :
    D ≤ Z R c := by
  have ht : color R t=true := by
    have hh := adjacent_color_ne R hat
    rw [ha] at hh
    cases ht : color R t <;> simp_all
  have hZX := geometry.omega_bound a ha (by rw [geometry.distance_constant a ha]; exact hb)
  apply le_trans _ (adjacent_Z_le R hc hct)
  intro x hx
  rw [Z,if_neg (by rw [ht]; decide)]
  obtain ⟨hxQ,hx2,_⟩ := mem_omegaCenter_iff.mp (hZX (hDZ hx))
  exact mem_omegaCenter_iff.mpr ⟨Q_le_adjacent_h R ht hat hxQ,hx2,
    fun y hy => hDC hx y (hy.2 a (adjacent_symm R hat))⟩

private theorem center_transport
    {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R} {q : ℕ}
    (hb : 2 ≤ geometry.b R) (s : ℕ → CriticalSegment geometry)
    (hs : ∀ i, BackwardLink geometry (pairedRadiusChoice geometry q) (s i) (s (i+1)))
    (i : ℕ) (D : Subgroup (FreeAmalgam R))
    (hD₀ : D ≤ centralizer (stabilizer R (s i).first : Set (FreeAmalgam R)))
    (hD₁ : D ≤ centralizer (stabilizer R (s (i+1)).first : Set (FreeAmalgam R))) :
    D ≤ centralizer (stabilizer R (s (i+2)).first : Set (FreeAmalgam R)) := by
  obtain ⟨t,hpair,_,_,_⟩ := (hs (i+1)).choice
  obtain ⟨g,hg,hgu,_,_⟩ := hpair.1
  have htwo : (s (i+1)).path.walk.getVert 2=(s i).first := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using (hs i).overlap 0 hb
  have hact : act R g (s i).first=(s (i+2)).first := by
    simpa only [Nat.add_assoc,htwo] using hgu.symm
  have hgS := Ltilde_le_stabilizer (s (i+1)).first hg
  have hDmap : D.map (MulAut.conj g⁻¹).toMonoidHom=D :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp hD₁ ((stabilizer R (s (i+1)).first).inv_mem hgS)))
  have hh := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hD₀).trans
    (map_centralizer_le_centralizer_image _ _)
  change D.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer
    ((stabilizer R (s i).first).map (MulAut.conj g⁻¹).toMonoidHom : Set _) at hh
  rwa [hDmap,←stabilizer_act,hact] at hh

private theorem penultimate_radius_le_second_core
    {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 4 < geometry.b R) :
    V R (path.walk.getVert (geometry.b R-2)) ≤ Q R (path.walk.getVert 2) := by
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hp : color R (path.walk.getVert (path.walk.length-2))=false := by
    apply (path.vertex_color (Nat.sub_le _ _)).mpr
    have he : Even path.walk.length := by
      rw [path.shortest,path.critical.1]
      exact geometry.even a path.start_color
    rw [Nat.even_iff] at he ⊢
    omega
  rw [←path.length_eq_b]
  apply V_le_Q_of_dist_add_two_lt R (geometry := geometry) hp
  rw [SimpleGraph.dist_comm]
  have hh := SimpleGraph.dist_le ((path.walk.drop 2).take (path.walk.length-4))
  rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_getVert,
    show 2+(path.walk.length-4)=path.walk.length-2 by omega] at hh
  have hi := hh.trans (min_le_right _ _)
  change (cosetGraph R).dist (path.walk.getVert 2)
    (path.walk.getVert (path.walk.length-2))+2 < geometry.b R
  have he := path.length_eq_b
  omega

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

omit [CharP F 2] in
private theorem core_le_mover
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) :
    Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) := by
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hh := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
    (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
    (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
    (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
      (h.replacement_two_group d) (h.replacement_core_le d)))
  rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR] at hh

private theorem reverse_two_kernel_growth
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical) :
    Nat.card F^2 < (Q d.radical a ⊓ Q d.radical (path.walk.getVert 2)).relIndex
      (V d.radical z) := by
  let hedge := MSCentralOrbit.edgeCentralizerCondition d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  let rev := (show CriticalSegment geometry from ⟨a,z,path⟩).reverse hedge (by omega)
  have hh := h.replacement_two_kernel_radius_index_gt_square d rev.path hb
  change Nat.card F^2 < (Q d.radical a ⊓
    Q d.radical (path.walk.reverse.getVert (geometry.b d.radical-2))).relIndex
      (V d.radical z) at hh
  rwa [SimpleGraph.Walk.getVert_reverse,path.length_eq_b,
    show geometry.b d.radical-(geometry.b d.radical-2)=2 by omega] at hh

private theorem fourth_preceding_noncentral
    {geometry : Geometry d.radical} (hb : 6 < geometry.b d.radical)
    (s : ℕ → CriticalSegment geometry)
    (hs : ∀ i, BackwardLink geometry (pairedRadiusOriginalFixedChoice geometry (Nat.card F))
      (s i) (s (i+1))) :
    ¬ ⁅Z d.radical (s 4).first,Z d.radical (s 4).last⁆ ≤
      centralizer (stabilizer d.radical (s 3).first : Set (FreeAmalgam d.radical)) := by
  intro hcent
  let a (i : ℕ) := (s i).first
  let z (i : ℕ) := (s i).last
  let D := ⁅Z d.radical (a 4),Z d.radical (z 4)⁆
  let Y := V d.radical (z 3) ⊔ (V d.radical (z 2) ⊓ Q d.radical (a 1))
  let N := V d.radical (z 3) ⊓ Q d.radical (a 2)
  let H₀ := ⁅Z d.radical (a 3),N⁆
  have hb4 : 4 < geometry.b d.radical := by omega
  have hp := ordinary_links hs
  have ht (i : ℕ) : (s (i+1)).path.walk.getVert 2=a i := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using (hp i).overlap 0 (by omega)
  have htriple := h.replacement_paired_radius_original_fixed_triple d hb4 s hs
  have hprev (i : ℕ) : ⁅Z d.radical (a (i+1)),Z d.radical (z (i+1))⁆ ≤ Z d.radical (a i) := by
    have hh := h.replacement_critical_commutator_le_second_seed_of_four_lt d (s (i+1)).path hb4
    rwa [ht i] at hh
  have hD3 : D ≤ Z d.radical (a 3) := hprev 3
  obtain ⟨t₂,hchoice₂,ha₂,ha₃,hfirst₃⟩ := (hp 2).choice
  have hD2 : D ≤ Z d.radical (a 2) := fixed_seed_le_neighbor_seed geometry (by omega)
    (s 3).path.start_color (s 2).path.start_color ha₃ ha₂ D hD3 hcent
  have hnD2 : ¬ D ≤ centralizer (stabilizer d.radical (a 2) : Set (FreeAmalgam d.radical)) := by
    intro hc
    have hself := center_transport (by omega) s hp 2 D hc hcent
    have hi := h.replacement_critical_commutator_central_index d (s 4).path hb4.le
    have hDS := (critical_commutator_le_start_seed (s 4).path).trans (Z_le_stabilizer _ _)
    rw [relIndex_eq_one.mpr (le_inf hDS hself)] at hi
    have hlo := (h.replacement_critical_indices_ge_field d (s 4).path (by omega)).1
    have hq : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hV3Q1 : V d.radical (z 3) ≤ Q d.radical (a 1) := by
    have hh := penultimate_radius_le_second_core (s 2).path hb4
    rwa [←(hp 2).last_eq,ht 1] at hh
  have hV2Q0 : V d.radical (z 2) ≤ Q d.radical (a 0) := by
    have hh := penultimate_radius_le_second_core (s 1).path hb4
    rwa [←(hp 1).last_eq,ht 0] at hh
  have hfirst_adj (i : ℕ) : Adjacent d.radical (a i) ((s i).path.walk.getVert 1) := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      ((s i).path.walk.adj_getVert_succ (by rw [(s i).path.length_eq_b]; omega :
        0 < (s i).path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hsecond_adj (i : ℕ) : Adjacent d.radical (a i) ((s (i+1)).path.walk.getVert 1) := by
    rw [←ht i]
    exact adjacent_symm _ ((cosetGraph_adj d.radical _ _).mp
      ((s (i+1)).path.walk.adj_getVert_succ (by rw [(s (i+1)).path.length_eq_b]; omega :
        1 < (s (i+1)).path.walk.length)))
  have hequal (i : ℕ) :
      Subgroup.SmallMover.join (U d.radical (a i)) (Q d.radical (a i))
        (Q d.radical ((s (i+1)).path.walk.getVert 1)) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical (a (i+1))) (Q d.radical (a (i+1)))
        (Q d.radical ((s (i+1)).path.walk.getVert 1)) (Nat.card F^2) := by
    have hh := h.replacement_mover_agreement_of_four_lt d (s (i+1)) hb4
    simpa only [pathMoverAgreement,Nat.mul_zero,Nat.zero_add,SimpleGraph.Walk.getVert_zero,ht i]
      using hh
  have hQ1J2 : Q d.radical (a 1) ≤ Subgroup.SmallMover.join (U d.radical (a 2))
      (Q d.radical (a 2)) (Q d.radical ((s 2).path.walk.getVert 1)) (Nat.card F^2) := by
    rw [←hequal 1]
    exact core_le_mover h d (s 1).path.start_color (hsecond_adj 1)
  have hQ0J1 : Q d.radical (a 0) ≤ Subgroup.SmallMover.join (U d.radical (a 1))
      (Q d.radical (a 1)) (Q d.radical ((s 1).path.walk.getVert 1)) (Nat.card F^2) := by
    rw [←hequal 0]
    exact core_le_mover h d (s 0).path.start_color (hsecond_adj 0)
  have hYJ : Y ≤ Subgroup.SmallMover.join (U d.radical (a 2)) (Q d.radical (a 2))
      (Q d.radical ((s 2).path.walk.getVert 1)) (Nat.card F^2) :=
    (sup_le hV3Q1 inf_le_right).trans hQ1J2
  have hDfix (j : ℕ) (hj : j=2 ∨ j=3) : D ≤ centralizer (V d.radical (z j) : Set _) := by
    apply (critical_commutator_le_endpoint_seed (s 4).path).trans
    apply seed_centralizes_radius_of_distance geometry (s 4).path.end_color (s j).path.end_color
    rcases hj with rfl | rfl
    · have hh := shifted_last_distance (pairedRadiusChoice geometry (Nat.card F)) s hp 2 2 (by omega)
      change (cosetGraph d.radical).dist (s 4).last (s 2).last+2 < geometry.b d.radical
      rw [hh]
      omega
    · have hh := shifted_last_distance (pairedRadiusChoice geometry (Nat.card F)) s hp 3 1 (by omega)
      change (cosetGraph d.radical).dist (s 4).last (s 3).last+2 < geometry.b d.radical
      rw [hh]
      omega
  have hDY : ⁅D,Y⁆=⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mp (hDfix 3 (Or.inr rfl)))
      (inf_le_left.trans (le_centralizer_iff.mp (hDfix 2 (Or.inl rfl))))
  have hYi : (Q d.radical (a 2)).relIndex Y ≤ Nat.card F := by
    by_contra hn
    have hh := h.replacement_path_large_actor_fixed_le_next_seed d (s 2).path hb4
      Y hYJ (Nat.lt_of_not_ge hn) D hD2 hDY
    rw [ht 1] at hh
    exact hnD2 ((le_inf (le_inf (hh.trans inf_le_left) hD2) hD3).trans (htriple 1))
  let := finite_stabilizer d.radical (a 1)
  have hYS : Y ≤ stabilizer d.radical (a 1) :=
    (sup_le hV3Q1 inf_le_right).trans (fun _ hx => hx.1)
  let : Finite Y := Finite.of_injective (inclusion hYS) (inclusion_injective _)
  let : Finite (V d.radical (z 3)) := Finite.of_injective
    (inclusion (show V d.radical (z 3) ≤ Y from le_sup_left)) (inclusion_injective _)
  let := finite_stabilizer d.radical (z 2)
  let : Finite (V d.radical (z 2)) := Finite.of_injective
    (inclusion ((geometry.V_le_Q (by omega) (z 2) (s 2).path.end_color).trans
      (show Q d.radical (z 2) ≤ stabilizer d.radical (z 2) from fun _ hx => hx.1)))
    (inclusion_injective _)
  have hV3i : (Q d.radical (a 2)).relIndex (V d.radical (z 3)) ≤ Nat.card F :=
    (relIndex_le_of_le_right le_sup_left index_ne_zero_of_finite).trans hYi
  have hV2ki : (Q d.radical (a 2)).relIndex
      (V d.radical (z 2) ⊓ Q d.radical (a 1)) ≤ Nat.card F :=
    (relIndex_le_of_le_right le_sup_right index_ne_zero_of_finite).trans hYi
  have hV2large : Nat.card F < (Q d.radical (a 1)).relIndex (V d.radical (z 2)) := by
    have hg := reverse_two_kernel_growth h d (s 2).path hb4
    rw [ht 1] at hg
    have hm := relIndex_inf_mul_relIndex (Q d.radical (a 2)) (Q d.radical (a 1)) (V d.radical (z 2))
    rw [inf_comm (Q d.radical (a 1)) (V d.radical (z 2))] at hm
    rw [←hm] at hg
    by_contra hn
    have hu := Nat.mul_le_mul hV2ki (Nat.le_of_not_gt hn)
    nlinarith
  have hNlarge : Nat.card F < (Q d.radical (a 3)).relIndex N := by
    have hg := reverse_two_kernel_growth h d (s 3).path hb4
    rw [ht 2] at hg
    have hm := relIndex_inf_mul_relIndex (Q d.radical (a 3)) (Q d.radical (a 2)) (V d.radical (z 3))
    rw [inf_comm (Q d.radical (a 2)) (V d.radical (z 3))] at hm
    rw [←hm] at hg
    by_contra hn
    have hu := Nat.mul_le_mul (Nat.le_of_not_gt hn) hV3i
    nlinarith
  have hZ2V3 : Z d.radical (z 2) ≤ V d.radical (z 3) := by
    have hd : (cosetGraph d.radical).dist (z 2) (z 3) ≤ 2 := by
      have hh := shifted_last_distance (pairedRadiusChoice geometry (Nat.card F)) s hp 2 1 (by omega)
      simpa only [SimpleGraph.dist_comm] using hh.le
    exact le_iSup_of_le (z 2) (le_iSup_of_le hd le_rfl)
  have hroot : (Q d.radical (a 2)).relIndex (Z d.radical (z 2)) < Nat.card F^2 := by
    have hi := (relIndex_le_of_le_right hZ2V3 index_ne_zero_of_finite).trans hV3i
    have hq : 1 < Nat.card F := Finite.one_lt_card
    exact lt_of_le_of_lt hi (by nlinarith)
  have hNS : N ≤ stabilizer d.radical (a 3) := inf_le_right.trans
    (Q_le_stabilizer_of_dist_two d.radical (a 2) (a 3) (s 2).path.start_color (by
      have hh := shifted_start_distance (pairedRadiusChoice geometry (Nat.card F)) s hp 2 1 (by omega)
      simpa only [SimpleGraph.dist_comm] using hh))
  have hH3 : H₀ ≤ Z d.radical (a 3) :=
    le_normalizer_iff_commutator_le_left.mp (hNS.trans (Z_normalized _ _))
  have hH2 : H₀ ≤ Z d.radical (a 2) := by
    have heq : Subgroup.SmallMover.join (U d.radical (a 3)) (Q d.radical (a 3))
        (Q d.radical t₂) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical (a 2)) (Q d.radical (a 2))
        (Q d.radical t₂) (Nat.card F^2) := by
      simpa only [hfirst₃] using (hequal 2).symm
    obtain ⟨hz,hcomm⟩ := h.replacement_equal_root_neighbor_commutator d (s 2).path hb4.le
      ha₂ ha₃ hroot
      (h.replacement_small_mover_index_le_square_of_four_lt d geometry hb4 (s 2).path.start_color ha₂) heq
    exact (commutator_mono le_rfl (inf_le_right.trans
      (core_le_mover h d (s 2).path.start_color ha₂))).trans (hcomm.trans hz)
  have hHV : H₀ ≤ V d.radical (z 3) := by
    apply (commutator_mono le_rfl inf_le_left).trans
    apply le_normalizer_iff_commutator_le_right.mp
    exact (Z_le_stabilizer_of_dist_le _ (geometry.exists_critical _ (s 3).path.start_color)
      (s 3).path.critical.1.le).trans (DistanceEight.V_normalized _ _)
  have hHfix3 : H₀ ≤ centralizer (V d.radical (z 3) : Set (FreeAmalgam d.radical)) :=
    hHV.trans (le_centralizer_iff_isMulCommutative.mpr
      (V_abelian_of_four_lt d.radical (s 3).path.end_color hb4))
  have hHfix2 : H₀ ≤ centralizer (V d.radical (z 2) : Set (FreeAmalgam d.radical)) :=
    hHV.trans (nearby_radius_centralizes_of_six_lt geometry hb (s 3).path.end_color
      (s 2).path.end_color (by
        have hh := shifted_last_distance (pairedRadiusChoice geometry (Nat.card F)) s hp 2 1 (by omega)
        exact hh.le))
  have hV3ne : ¬ V d.radical (z 3) ≤ Q d.radical (a 2) := by
    intro hn
    have hi := (h.replacement_critical_indices_ge_field d (s 2).path (by omega)).2
    rw [relIndex_eq_one.mpr (hZ2V3.trans hn)] at hi
    have hq : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hHidx : (Z d.radical (a 1)).relIndex H₀ ≤ Nat.card F := by
    have hh := h.replacement_path_nontrivial_actor_fixed_seed_index_le_field d (s 2).path hb4
      (V d.radical (z 3)) (hV3Q1.trans hQ1J2) hV3ne H₀ hH2
      (commutator_eq_bot_iff_le_centralizer.mpr hHfix3)
    rwa [ht 1] at hh
  let E := H₀ ⊓ Z d.radical (a 1)
  have hE2 : E ≤ centralizer (stabilizer d.radical (a 2) : Set (FreeAmalgam d.radical)) :=
    (le_inf (le_inf inf_le_right (inf_le_left.trans hH2)) (inf_le_left.trans hH3)).trans (htriple 1)
  have hE0 : E ≤ Z d.radical (a 0) := by
    have hh := h.replacement_path_large_actor_fixed_le_next_seed d (s 1).path hb4
      (V d.radical (z 2)) (hV2Q0.trans hQ0J1) hV2large E inf_le_right
      (commutator_eq_bot_iff_le_centralizer.mpr (inf_le_left.trans hHfix2))
    rw [ht 0] at hh
    exact hh.trans inf_le_left
  have hE1 : E ≤ centralizer (stabilizer d.radical (a 1) : Set (FreeAmalgam d.radical)) :=
    (le_inf (le_inf hE0 inf_le_right) (inf_le_left.trans hH2)).trans (htriple 0)
  have hE3 := center_transport (by omega) s hp 1 E hE1 hE2
  let := finite_Z d.radical (a 3)
  let : Finite H₀ := Finite.of_injective (inclusion hH3) (inclusion_injective _)
  have hmoveU : Nat.card F < (centralizer (N : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical (a 3)) := by
    by_contra hn
    exact (not_lt_of_ge (h.replacement_field_fixed_index_image_bound d geometry hb4.le
      (s 3).path.start_color N hNS (Nat.le_of_not_gt hn))) hNlarge
  have hmoveZ := hmoveU.trans_le (relIndex_le_of_le_right (U_le_Z (a 3)) index_ne_zero_of_finite)
  have he := h.replacement_displacement_central_index d geometry hb4.le (s 3).path.start_color N hNS
  rw [commutator_comm N] at he
  have hEC : E ≤ stabilizer d.radical (a 3) ⊓
      centralizer (stabilizer d.radical (a 3) : Set (FreeAmalgam d.radical)) :=
    le_inf (inf_le_left.trans (hH3.trans (Z_le_stabilizer _ _))) hE3
  have hupper := relIndex_le_of_le_left hEC (by exact index_ne_zero_of_finite (H := E.subgroupOf H₀))
  rw [show E=H₀ ⊓ Z d.radical (a 1) from rfl,inf_relIndex_left] at hupper
  have hlow : Nat.card F < (stabilizer d.radical (a 3) ⊓
      centralizer (stabilizer d.radical (a 3) : Set (FreeAmalgam d.radical))).relIndex H₀ :=
    hmoveZ.trans_eq he.symm
  exact (not_lt_of_ge (hupper.trans hHidx)) hlow

/-- Every actual paired commutator four shifts onward remains noncentral
at its preceding vertex when the distance exceeds six. -/
theorem Input.replacement_paired_radius_large_preceding_noncentral
    {geometry : Geometry d.radical} (hb : 6 < geometry.b d.radical)
    (s : ℕ → CriticalSegment geometry)
    (hs : ∀ i, BackwardLink geometry (pairedRadiusOriginalFixedChoice geometry (Nat.card F))
      (s i) (s (i+1))) (k : ℕ) :
    ¬ ⁅Z d.radical (s (k+4)).first,Z d.radical (s (k+4)).last⁆ ≤
      centralizer (stabilizer d.radical (s (k+3)).first : Set (FreeAmalgam d.radical)) := by
  exact fourth_preceding_noncentral h d hb (fun i => s (k+i)) (fun i => by
    simpa only [Nat.add_assoc] using hs (k+i))

/-- The full paired displacement argument bounds the actual minimum
replacement critical distance by six, with no selected-path premise. -/
theorem Input.replacement_distance_le_six (geometry : Geometry d.radical) :
    geometry.b d.radical ≤ 6 := by
  by_contra hn
  have hb : 6 < geometry.b d.radical := Nat.lt_of_not_ge hn
  have hb4 : 4 < geometry.b d.radical := by omega
  obtain ⟨z,hz⟩ := criticalPair_exists d.radical (alpha d.radical)
    (geometry.exists_critical (alpha d.radical) rfl)
  let p : CriticalSegment geometry := ⟨alpha d.radical,z,CriticalPath.ofPair rfl hz⟩
  obtain ⟨s,_,hs,hp,_,_,htriple⟩ := h.replacement_paired_radius_original_fixed_paths d p hb4
  have hprev (i : ℕ) : ⁅Z d.radical (s (i+1)).first,Z d.radical (s (i+1)).last⁆ ≤
      Z d.radical (s i).first := by
    have hh := h.replacement_critical_commutator_le_second_seed_of_four_lt d (s (i+1)).path hb4
    have ht := (hp i).overlap 0 (by omega)
    have ht' : (s (i+1)).path.walk.getVert 2=(s i).first := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using ht
    rwa [ht'] at hh
  have halt := h.replacement_paired_radius_terminal_seed_alternative d hb4
    (fun i => s (i+2)) (fun i => hp (i+2))
  rcases halt with hleft | hright
  · exact h.replacement_paired_radius_large_preceding_noncentral d hb s hs 0
      ((le_inf (le_inf hleft (hprev 3))
        (critical_commutator_le_start_seed (s 4).path)).trans (htriple 2))
  · exact h.replacement_paired_radius_large_preceding_noncentral d hb s hs 1
      ((le_inf (le_inf hright (hprev 4))
        (critical_commutator_le_start_seed (s 5).path)).trans (htriple 3))

/-- The actual minimum replacement critical distance is at most four. -/
theorem Input.replacement_distance_le_four (geometry : Geometry d.radical) :
    geometry.b d.radical ≤ 4 := by
  have hu := h.replacement_distance_le_six d geometry
  have hn := h.replacement_distance_ne_six d geometry
  have he : Even (geometry.b d.radical) := by
    exact geometry.even (alpha d.radical) rfl
  obtain ⟨k,hk⟩ := he
  omega

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
