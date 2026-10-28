module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourDerivedEscape
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.Radius
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.Radius
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSpanMovement

/-!
# The full radius derived subgroup in the fixed-radius branch

The actual inner vertex quotient gives G_a = L_a Q_a. Thus the moved
radius and any incident edge radius generate V_a. The edge radius is
abelian for b > 2. Under [V_a,Q_a] <= D_a, the generated-core commutator
lemma gives [V_a,Vcirc_a] <= Vcirc_a', and consequently V_a' = Vcirc_a'.

Every compatible backward critical commutator lies in V_a', regardless
of its starting vertex's orbit. The actual large-back derived bound
therefore excludes a large backward image in the fixed-radius branch.
Both literal backward indices equal the original field order.

Source: the radius decomposition used in MS93 (5.12)(2), printed p.925,
and the derived bound in (3.10)(i), used on p.926. The internal imports
reuse only generic join normalization and residual commutator idempotence;
no binary LocalSource or private symbol occurs in the public statements.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem replacement_radius_edge_decomposition
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) :
    V d.radical a=Vcirc d.radical a ⊔ V d.radical t := by
  have htV := NaturalStructure.Exclusion.edge_radius_le_radius ha hat
  have hS : Ltilde d.radical a ⊔ Q d.radical a=stabilizer d.radical a := by
    obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ := vertex_coordinates_with_kernel d.radical
      (h.replacement_two_group d) (h.replacement_core_le d) ha
    rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
      h.replacement_inner_of_four_le d geometry hb,←MonoidHom.range_eq_map,hir]
  have hn : stabilizer d.radical a ≤ normalizer
      ((Vcirc d.radical a ⊔ V d.radical t : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    rw [←hS]
    apply sup_le
    · exact NaturalStructure.Exclusion.normalizes_sup_of_commutator_le _ _ _
        ((Ltilde_le_stabilizer a).trans (Vcirc_normalized a))
        (commutator_mono htV le_rfl)
    · exact (le_inf
        ((show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1).trans
          (Vcirc_normalized a))
        ((show Q d.radical a ≤ stabilizer d.radical t from fun _ hx => hx.2 t hat).trans
          (DistanceEight.V_normalized d.radical t))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  apply le_antisymm _ (sup_le (DistanceEight.Vcirc_le_V d.radical a) htV)
  apply NaturalStructure.Exclusion.radius_le_of_m_ball ha
  intro c hc hdist
  by_cases hca : c=a
  · subst c
    apply (show Z d.radical a ≤ V d.radical t from ?_).trans le_sup_right
    exact le_iSup_of_le a (le_iSup_of_le
      ((SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hat)).le.trans
        (by decide : 1 ≤ 2)) le_rfl)
  have htwo : (cosetGraph d.radical).dist a c=2 := by
    have hne : (cosetGraph d.radical).dist a c≠0 := by
      intro hz
      exact hca ((cosetGraph_connected d.radical).dist_eq_zero_iff.mp hz).symm
    have heven : Even ((cosetGraph d.radical).dist a c) := by
      obtain ⟨w,hw⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist a c
      rw [←hw,walk_even_iff_color_eq,ha,hc]
    rw [Nat.even_iff] at heven
    rw [SimpleGraph.dist_comm] at hdist
    omega
  obtain ⟨w,haw,hcw⟩ := exists_common_neighbor_of_dist_two d.radical a c htwo
  obtain ⟨g,hg,hgw⟩ := stabilizer_transitive_neighbors d.radical a hat haw
  have hVw : V d.radical w ≤ Vcirc d.radical a ⊔ V d.radical t := by
    rw [←hgw,V_act]
    exact (map_mono (show V d.radical t ≤ Vcirc d.radical a ⊔ V d.radical t from
      le_sup_right)).trans
      (mem_normalizer_iff_map_conj_eq.mp (hn ((stabilizer d.radical a).inv_mem hg))).le
  apply (show Z d.radical c ≤ V d.radical w from ?_).trans hVw
  exact le_iSup_of_le c (le_iSup_of_le
    ((SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hcw)).le.trans
      (by decide : 1 ≤ 2)) le_rfl)

/-- In the actual fixed-radius branch the full radius and the moved radius
have the same derived subgroup, with every fixed attachment retained. -/
theorem Input.replacement_distance_four_radius_derived_eq_moving_derived
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    ⁅V d.radical a,V d.radical a⁆=⁅Vcirc d.radical a,Vcirc d.radical a⁆ := by
  let P := Vcirc d.radical a
  let C := ⁅P,P⁆
  let t := path.walk.getVert 1
  have hl := path.length_eq_b
  have hat : Adjacent d.radical a t := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hPV : P ≤ V d.radical a := DistanceEight.Vcirc_le_V d.radical a
  have hTV : V d.radical t ≤ V d.radical a :=
    NaturalStructure.Exclusion.edge_radius_le_radius path.start_color hat
  have hVQ := geometry.V_le_Q (by omega : 2 < geometry.b d.radical) a path.start_color
  have hVS : V d.radical a ≤ stabilizer d.radical a := hVQ.trans (fun _ hx => hx.1)
  have hSP : stabilizer d.radical a ≤ normalizer (P : Set (FreeAmalgam d.radical)) :=
    Vcirc_normalized a
  have hVC : ⁅V d.radical a,P⁆ ≤ C := by
    apply commutator_le_derived_of_generated_core P (Ltilde d.radical a)
      (V d.radical a) (fixedCore d.radical a)
      (moving_full_commutation h d geometry (by omega) path.start_color)
      ((Ltilde_le_stabilizer a).trans hSP) (hVS.trans hSP) le_rfl
    · rw [commutator_eq_bot_iff_le_centralizer.mpr
        (show fixedCore d.radical a ≤ centralizer (Ltilde d.radical a : Set _) from inf_le_right)]
      exact bot_le
    · exact (commutator_mono le_rfl (hPV.trans hVQ)).trans hfixed
  have hn : V d.radical a ≤ normalizer (C : Set (FreeAmalgam d.radical)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hSP (hVS hg))]
  have hsplit : V d.radical a=P ⊔ V d.radical t :=
    replacement_radius_edge_decomposition h d geometry (by omega) path.start_color hat
  have hPC : ⁅P,V d.radical a⁆ ≤ C := (commutator_comm _ _).le.trans hVC
  have hTC : ⁅V d.radical t,V d.radical a⁆ ≤ C := by
    rw [commutator_comm,hsplit]
    apply commutator_sup_le_of_relative_normal (V d.radical a) P (V d.radical t)
      (V d.radical t) C hn hPV hTV ((commutator_mono le_rfl hTV).trans hPC)
    let := NaturalStructure.Exclusion.edge_radius_commutative geometry (by omega)
      a t path.start_color hat
    exact (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer (V d.radical t))).le.trans bot_le
  apply le_antisymm _ (commutator_mono hPV hPV)
  conv_lhs => lhs; rw [hsplit]
  exact commutator_sup_le_of_relative_normal (V d.radical a) P (V d.radical t)
    (V d.radical a) C hn hPV hTV hPC hTC

/-- Every compatible backward path has both critical indices equal to q
in the fixed-radius branch. No prescribed midpoint orbit is required. -/
theorem Input.replacement_distance_four_fixed_backward_indices
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u)=Nat.card F ∧
      (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2))=Nat.card F := by
  have hsmall : (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u) ≤ Nat.card F := by
    by_contra! hlarge
    have hn := (h.replacement_distance_four_critical_commutator_escapes_moving_derived
      d path hb back hmid hlarge hfixed).2 a path.start_color
    apply hn
    rw [←h.replacement_distance_four_radius_derived_eq_moving_derived d path hb hfixed]
    have hbl := back.length_eq_b
    have hl := path.length_eq_b
    have hua : (cosetGraph d.radical).dist u a=2 := by
      rw [←hmid]
      exact back.dist_start (by omega)
    have hea : (cosetGraph d.radical).dist (path.walk.getVert 2) a=2 := by
      rw [SimpleGraph.dist_comm]
      exact path.dist_start (by omega)
    exact commutator_mono (le_iSup_of_le u (le_iSup_of_le hua.le le_rfl))
      (le_iSup_of_le (path.walk.getVert 2) (le_iSup_of_le hea.le le_rfl))
  exact h.replacement_small_critical_indices_eq_field d back (by omega) (hsmall.trans_lt (by
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
