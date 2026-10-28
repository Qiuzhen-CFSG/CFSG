module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootSelectedPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TerminalKernelSaturation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootFixed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.IndividualMovers

/-!
# The whole critical root is fixed at the first selected source

The small image of a compatible backward critical path places its entire
commutator in the original Z-layer and fixes the original smaller mover.
Reversing that path and transferring full neighboring-mover fixed subgroups
keeps every central attachment. The same actual first selector then fixes
the whole root commutator at the original starting vertex.

No failed comparison is needed. The small backward image is an intermediate
case premise, later forced by any trapped second selector. Source: MS93
(5.12)(1) and its transition to a second backward critical pair, p.925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open scoped Pointwise
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
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

/-- The root image of the actual backward path suffices to fix its whole
commutator under the original first mover, with both literal overlaps. -/
theorem Input.replacement_distance_four_root_original_fixed
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hlast : back.walk.getVert 3=path.walk.getVert 1)
    (hsmall : (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) < Nat.card F^2) :
    ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ≤
      Z d.radical a ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) :
            Set (FreeAmalgam d.radical)) := by
  let e := path.walk.getVert 2
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hsmall' : (Q d.radical e).relIndex (Z d.radical u) < Nat.card F^2 := by
    rw [h.replacement_critical_indices_equal d back hb4]
    exact hsmall
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

/-- The same first equal-root selector centralizes the whole root commutator
of every compatible backward path with small image. This producer retains
the arbitrary initial neighbor and all original geometric alternatives. -/
theorem Input.replacement_distance_four_first_selector_root_centrality
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (hct : Adjacent d.radical c t)
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2))
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2) :
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      let t₁ := act d.radical g⁻¹ t
      let c₁ := act d.radical g⁻¹ c
      let t₂ := act d.radical x t₁
      let c₂ := act d.radical x c₁
      ∃ u ∈ ({c₁,c₂} : Set (Vertex d.radical)), ∃ w,
        (u=c₁ ∧ w=t₁ ∨ u=c₂ ∧ w=t₂) ∧
        Adjacent d.radical a w ∧ Adjacent d.radical u w ∧
        ¬ Z d.radical z ≤ normalizer
          ((Z d.radical u ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        ((∃ back : CriticalPath d.radical geometry u (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1=w ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∨
        (Z d.radical u ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
          Nat.card F ≤ (centralizer (Z d.radical u : Set (FreeAmalgam d.radical))).relIndex
            (Z d.radical z ⊓ Q d.radical a) ∧
          X d.radical z ⊓ Q d.radical a ≤ normalizer (Z d.radical u : Set _) ∧
          ⁅⁅X d.radical z ⊓ Q d.radical a,Z d.radical u⁆,Z d.radical u⁆=⊥)) ∧
        (∀ (back : CriticalPath d.radical geometry u (path.walk.getVert 2)),
          back.walk.getVert 1=w → back.walk.getVert 2=a →
          back.walk.getVert 3=path.walk.getVert 1 →
          (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) < Nat.card F^2 →
          ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ≤
            centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) := by
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  obtain ⟨E,hE,f,hf,hfQ,hTf,hindex,hcore,hTP,hquad,hmax⟩ :=
    h.replacement_maximizing_parabolic d geometry hb4 path.start_color hat
  have hJplane := h.replacement_small_mover_le_maximizing_plane_of_index_le d
    geometry hb4 path.start_color hat E hE f hfQ hTf hindex hmax hJm
  let D := ((((CentralRootGeometry.wing (F := E.Carrier) true).map unipotent.subtype).comap f).map
    (stabilizer d.radical a).subtype)
  have hJD : J ≤ D := by
    have hh := map_mono (f := (stabilizer d.radical a).subtype) hJplane
    rwa [map_subgroupOf_eq_of_le ((Subgroup.SmallMover.join_le _ _ _ _).trans
      (show Q d.radical t ≤ stabilizer d.radical a from fun _ hy => hy.2 a (adjacent_symm _ hat)))] at hh
  have hzD : Z d.radical z ≤ D :=
    (h.replacement_root_endpoint_le_small_mover d path hb4 hat hfirst hsmall
      E hE f hf hTf hindex hJplane).trans hJD
  have hfixed : Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (D : Set (FreeAmalgam d.radical)) :=
    h.replacement_small_mover_parabolic_full_fixed d geometry hb4 path.start_color hat
      E hE f hf hfQ hindex hJplane
  obtain ⟨g,hg,x,hx,ha₁,hc₁,ha₂,hc₂,hgen₁,hgen₂,hpair,hmove₁,hmove₂,hxn,hxp,
      u,hu,w,hwhich,haw,huw,hn,hnext⟩ :=
    h.replacement_equal_smaller_selected_root_alternative d path hb4 hat hfirst hct
      hnormal hequal hsmall E hE f hf hfQ hTf hindex hquad hJplane
  have finish (u w : Vertex d.radical) (y : FreeAmalgam d.radical)
      (hy : y ∈ normalizer (D : Set (FreeAmalgam d.radical)))
      (hgen : (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
          (Q d.radical w) (Nat.card F^2) ⊔ Z d.radical z) ⊔
          (Z d.radical z).map (MulAut.conj y).toMonoidHom = stabilizer d.radical a)
      (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
      (hback : back.walk.getVert 1=w) (hmid : back.walk.getVert 2=a)
      (hlast : back.walk.getVert 3=path.walk.getVert 1)
      (hsmall' : (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) < Nat.card F^2) :
      ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ≤
        centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    let C := ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆
    have horiginal := h.replacement_distance_four_root_original_fixed d
      path hb back hmid hlast hsmall'
    rw [hfirst] at horiginal
    have hCD : C ≤ centralizer (D : Set (FreeAmalgam d.radical)) :=
      (horiginal.trans hfixed.le).trans inf_le_right
    have hCJ := h.replacement_root_critical_commutator_fixed_by_first_mover d back hb4 hsmall'
    rw [hback] at hCJ
    have hzDy : (Z d.radical z).map (MulAut.conj y).toMonoidHom ≤ D :=
      (map_mono hzD).trans_eq (mem_normalizer_iff_map_conj_eq.mp hy)
    have hCZ := hCD.trans (centralizer_le hzD)
    have hCZy := hCD.trans (centralizer_le hzDy)
    intro r hr
    have hJ : Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical w) (Nat.card F^2) ≤ centralizer ({r} : Set (FreeAmalgam d.radical)) :=
      fun b hb => mem_centralizer_singleton_iff.mpr (hCJ hr b hb)
    have hZ : Z d.radical z ≤ centralizer ({r} : Set (FreeAmalgam d.radical)) :=
      fun b hb => mem_centralizer_singleton_iff.mpr (hCZ hr b hb)
    have hZy : (Z d.radical z).map (MulAut.conj y).toMonoidHom ≤
        centralizer ({r} : Set (FreeAmalgam d.radical)) :=
      fun b hb => mem_centralizer_singleton_iff.mpr (hCZy hr b hb)
    intro b hb
    exact mem_centralizer_singleton_iff.mp ((sup_le (sup_le hJ hZ) hZy) (hgen.symm ▸ hb))
  refine ⟨g,hg,x,hx,u,hu,w,hwhich,haw,huw,hn,hnext,?_⟩
  rcases hwhich with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact finish _ _ x hxn hgen₁
  · exact finish _ _ x⁻¹ ((normalizer (D : Set (FreeAmalgam d.radical))).inv_mem hxn) hgen₂

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
