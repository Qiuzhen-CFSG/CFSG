module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootPlacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootFixed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.IndividualMovers

/-!
# The failed comparison fixes the original first mover

Reverse the actual backward critical path. Its full root commutator fixes
the mover at the literal last edge, which is the first edge of the original
path. If the two movers at this edge agree, this is the desired original
mover. Otherwise the neighboring mover and the edge kernel have the same
fixed subgroup on U. The full decomposition of Z lifts that equality while
retaining every vertex-fixed attachment.

The failed distance-four comparison puts the root commutator in the original
Z-layer. Thus it fixes the original mover even when the initial selector was
applied to a neighbor different from the original second path vertex. The
actual midpoint and last-edge overlaps are retained explicitly.
Source: MS93 (5.12)(1), printed p.925, the original fixedness needed before
applying the same selector from (5.6).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem neighbor_full_fixed_le_original
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t c : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t) :
    Z d.radical a ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
          (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical)) ≤
      centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical)) := by
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let E := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
    (Q d.radical t) (Nat.card F^2)
  change Z d.radical a ⊓ centralizer (E : Set (FreeAmalgam d.radical)) ≤
    centralizer (J : Set (FreeAmalgam d.radical))
  by_cases he : E=J
  · rw [he]
    exact inf_le_right
  have heU := (h.replacement_unequal_individual_edge_fixed d geometry hb ha hat hct he).2
  let D := Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))
  have hTS : Q d.radical t ≤ stabilizer d.radical a :=
    fun _ hx => hx.2 a (adjacent_symm _ hat)
  have hES : E ≤ stabilizer d.radical a := (Subgroup.SmallMover.join_le _ _ _ _).trans hTS
  have hJT : J ≤ Q d.radical t := Subgroup.SmallMover.join_le _ _ _ _
  have hJS : J ≤ stabilizer d.radical a := hJT.trans hTS
  have hDN : D ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    (inf_le_left.trans (Z_le_stabilizer d.radical a)).trans (U_normalized a)
  intro z hz
  have hzprod : z ∈ (U d.radical a : Set (FreeAmalgam d.radical)) * (D : Set _) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hDN]
    exact h.replacement_Z_eq_U_sup_fixed d geometry hb ha ▸ hz.1
  obtain ⟨u,hu,c,hc,heq⟩ := hzprod
  have huE : u ∈ centralizer (E : Set (FreeAmalgam d.radical)) := by
    have hh := (centralizer (E : Set (FreeAmalgam d.radical))).mul_mem hz.2
      ((centralizer (E : Set (FreeAmalgam d.radical))).inv_mem (centralizer_le hES hc.2))
    simpa only [←heq,mul_inv_cancel_right] using hh
  have huT : u ∈ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) :=
    (heU ▸ (show u ∈ U d.radical a ⊓ centralizer (E : Set (FreeAmalgam d.radical)) from
      ⟨hu,huE⟩)).2
  rw [←heq]
  exact (centralizer (J : Set (FreeAmalgam d.radical))).mul_mem
    (centralizer_le hJT huT) (centralizer_le hJS hc.2)

/-- The failed comparison's entire critical root commutator lies in the
original seed and fixes its literal first smaller mover. Both path overlaps
are actual selected-path data; no identification of the initially selected
neighbor with the original forward neighbor is required. -/
theorem Input.replacement_distance_four_root_commutator_fixed_by_original_mover
    {geometry : Geometry d.radical} {a z u v t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hlast : back.walk.getVert 3=path.walk.getVert 1)
    (hut : Adjacent d.radical u t) (hvt : Adjacent d.radical v t)
    (hbad : ¬ ⁅U d.radical v ⊓ Q d.radical z,Z d.radical (path.walk.getVert 2)⁆ ≤
      ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
        ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆) :
    ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ≤
      Z d.radical a ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) :
            Set (FreeAmalgam d.radical)) := by
  let e := path.walk.getVert 2
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  obtain ⟨hi,hi',_⟩ :=
    h.replacement_distance_four_comparison_failure d path hb back hut hvt hbad
  have hsmall : (Q d.radical u).relIndex (Z d.radical e) < Nat.card F^2 := by
    rw [hi']
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  have hsmall' : (Q d.radical e).relIndex (Z d.radical u) < Nat.card F^2 := by
    rw [hi]
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  have hat : Adjacent d.radical a (path.walk.getVert 1) := by
    simpa using (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 0<path.walk.length))
  have het : Adjacent d.radical e (path.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 1<path.walk.length)))
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical back.start_color
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical path.start_color
  let y := g⁻¹*j
  have hy : act d.radical y u=a := by
    rw [hg,act_mVertex]
    dsimp only [y]
    rw [mul_inv_cancel_left,←hj]
  have hsmallAct : (Q d.radical (act d.radical y u)).relIndex
      (Z d.radical (act d.radical y e)) < Nat.card F^2 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective]
    exact hsmall
  have hXa : X d.radical a=Z d.radical a := by
    have hh := h.replacement_root_X_eq_Z d (back.act y) hb4 (by rw [hy]; exact hat) hsmallAct
    simpa only [hy] using hh
  have huV : Z d.radical u ≤ V d.radical a := by
    apply le_iSup_of_le u
    apply le_iSup_of_le (show (cosetGraph d.radical).dist u a ≤ 2 from ?_)
    · exact le_rfl
    · rw [←hmid,back.dist_start (by rw [back.length_eq_b]; omega)]
  have heV : Z d.radical e ≤ V d.radical a := by
    apply le_iSup_of_le e
    apply le_iSup_of_le (show (cosetGraph d.radical).dist e a ≤ 2 from ?_)
    · exact le_rfl
    · rw [SimpleGraph.dist_comm,path.dist_start (by rw [path.length_eq_b]; omega)]
  have hRZa : ⁅Z d.radical u,Z d.radical e⁆ ≤ Z d.radical a :=
    ((commutator_mono huV heV).trans
      (h.replacement_radius_commutator_bounds d geometry hb4 path.start_color e z).1).trans_eq hXa
  let rev : CriticalPath d.radical geometry e u :=
    { start_color := back.end_color
      walk := back.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,back.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical geometry
        (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
          (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
        u back.start_color (by
          rw [geometry.distance_constant u back.start_color]
          exact lt_of_lt_of_le (by decide : 0<4) hb4) e back.end_color back.critical }
  have hrev : rev.walk.getVert 1=path.walk.getVert 1 := by
    change back.walk.reverse.getVert 1=path.walk.getVert 1
    rw [SimpleGraph.Walk.getVert_reverse,back.length_eq_b,hb]
    exact hlast
  have hRE : ⁅Z d.radical u,Z d.radical e⁆ ≤ centralizer
      (Subgroup.SmallMover.join (U d.radical e) (Q d.radical e)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical)) := by
    have hh := h.replacement_root_critical_commutator_fixed_by_first_mover d rev hb4 hsmall'
    rw [commutator_comm,hrev] at hh
    exact hh
  exact le_inf hRZa ((le_inf hRZa hRE).trans
    (neighbor_full_fixed_le_original h d geometry hb4 path.start_color hat het))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
