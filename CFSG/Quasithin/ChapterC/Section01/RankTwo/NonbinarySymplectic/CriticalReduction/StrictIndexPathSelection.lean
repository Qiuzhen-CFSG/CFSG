module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexMovement

/-!
# Moving indices and source selection on the original critical path

The terminal residual twist puts U_z intersect B_(z-2) in the original
starting kernel. The faithful natural action therefore gives a field-sized
lower bound for its full moving index, without any uniform upper bound.
The already proved full-radius nontrapping theorem supplies a backward
critical extension with every overlap retained. Repeating that extension
places the original first two vertices at the end of a critical path.
Consequently their actual B-relative moving index is at least q; reversing
the original path gives the reciprocal bound.

The same backward witness lies in the literal T0: its kernel contains the
complete U_c intersect B_a by the terminal-intersection calculation. This
proves the required centralization and kernel escape, without inferring
centralization from distance. In the strict-index countercase, the moving
index is exactly q. The existing conjugator construction and terminal
selector now apply without an extra moving-neighbor hypothesis. They retain
both original second spans, their full kernels, the original path overlaps,
T2's kernel escape and the non-B conjugate starting seed.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.8) and (5.9)(**), printed pp.920--922. R3 centrality, the second-span
displacement comparison, the strict-index contradiction, the later terminal
exclusions and the minimum-replacement distance-two witness remain required.
No field degree, central attachment, quotient map or public interface is
changed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
private theorem terminal_color
    {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}
    {a z : Vertex R} (path : CriticalPath R geometry a z) (hb : 4 ≤ geometry.b R) :
    color R (path.walk.getVert (path.walk.length-2))=false := by
  have hlen : 4 ≤ path.walk.length := by rw [path.length_eq_b]; exact hb
  apply (path.vertex_color (Nat.sub_le _ _)).mpr
  have he : Even path.walk.length := by
    rw [path.shortest,path.critical.1]
    exact geometry.even a path.start_color
  rw [Nat.even_iff] at he ⊢
  omega

private theorem terminal_B_intersection_le_kernel
    {M : Type*} [Group M] [Finite M] {R : Subgroup M} {geometry : Geometry R}
    {a z : Vertex R} (path : CriticalPath R geometry a z) (hb : 4 ≤ geometry.b R)
    (x : FreeAmalgam R) (hx : x ∈ Ltilde R (path.walk.getVert (path.walk.length-2)))
    (htwist : act R x (path.walk.getVert (path.walk.length-1)) =
      path.walk.getVert (path.walk.length-3)) :
    U R z ⊓ B R (path.walk.getVert (path.walk.length-2)) (geometry.Z_normal _) ≤ Q R a := by
  let p := path.walk.getVert (path.walk.length-2)
  let A := U R z ⊓ B R p (geometry.Z_normal p)
  have hp : color R p=false := terminal_color path hb
  have hlen : 4 ≤ path.walk.length := by rw [path.length_eq_b]; exact hb
  have hVS : V R p ≤ stabilizer R p :=
    (geometry.V_le_Q (by omega) p hp).trans (fun _ hy => hy.1)
  have hcomm : ⁅A,Ltilde R p⁆ ≤ Z R p := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl u hu
    exact ((mem_B_iff R p (geometry.Z_normal p) hVS u).mp hu.2).2 l hl
  have hnorm : Ltilde R p ≤ normalizer ((A ⊔ Z R p : Subgroup (FreeAmalgam R)) : Set _) :=
    normalizes_sup_of_displacement _ _ _ ((Ltilde_le_stabilizer p).trans (Z_normalized R p)) hcomm
  have hmap := mem_normalizer_iff_map_conj_eq.mp (hnorm ((Ltilde R p).inv_mem hx))
  change (A ⊔ Z R p).map (MulAut.conj x⁻¹).toMonoidHom = A ⊔ Z R p at hmap
  have hfix : act R x p=p := Ltilde_le_stabilizer p hx
  have hbound : A ⊔ Z R p ≤ U R (act R x z) ⊔ Z R p := by
    rw [←hmap,Subgroup.map_sup,←Z_act,hfix, U_act]
    exact sup_le_sup (map_mono inf_le_left) le_rfl
  have hlast : Adjacent R z (path.walk.getVert (path.walk.length-1)) := by
    apply adjacent_symm R
    have hh := path.walk.adj_getVert_succ (by omega : path.walk.length-1 < path.walk.length)
    rw [show path.walk.length-1+1=path.walk.length by omega,SimpleGraph.Walk.getVert_length] at hh
    exact (cosetGraph_adj R _ _).mp hh
  have hnew : Adjacent R (act R x z) (path.walk.getVert (path.walk.length-3)) := by
    rw [←htwist]
    exact (adjacent_act_iff R x _ _).mpr hlast
  have hdist : (cosetGraph R).dist (act R x z) a < geometry.b R := by
    have hh := (cosetGraph_connected R).dist_triangle (u := act R x z)
      (v := path.walk.getVert (path.walk.length-3)) (w := a)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hnew),
      SimpleGraph.dist_comm (u := path.walk.getVert (path.walk.length-3)) (v := a),
      path.dist_start (Nat.sub_le _ _)] at hh
    have he := path.length_eq_b
    omega
  have hnewQ : U R (act R x z) ≤ Q R a := (U_le_Z _).trans
    (Z_le_Q_of_dist_lt R _ (geometry.exists_critical _
      (by rw [action_preserves_color]; exact path.end_color))
      (by rwa [geometry.distance_constant _ (by rw [action_preserves_color]; exact path.end_color)]))
  have hpQ : Z R p ≤ Q R a := by
    apply Z_le_Q_of_dist_lt R p (geometry.exists_critical p hp)
    rw [geometry.distance_constant p hp,SimpleGraph.dist_comm]
    dsimp only [p]
    rw [path.dist_start (Nat.sub_le _ _)]
    change path.walk.length-2 < geometry.b R
    have he := path.length_eq_b
    omega
  exact le_sup_left.trans (hbound.trans (sup_le hnewQ hpQ))

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The full terminal moving layer has B-relative index at least q,
without a uniform upper bound on other neighbors. -/
theorem Input.replacement_terminal_moving_index_ge_field
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical) :
    Nat.card F ≤ (B d.radical (path.walk.getVert (path.walk.length-2))
      (geometry.Z_normal _)).relIndex (U d.radical z) := by
  obtain ⟨x,hx,he,_⟩ := h.replacement_terminal_edge_residual_twist d path hb
  have hle := terminal_B_intersection_le_kernel path hb x hx he
  let := finite_Z d.radical z
  let : Finite (U d.radical z) := Finite.of_injective (inclusion (U_le_Z z)) (inclusion_injective _)
  have hupper := relIndex_le_of_le_left hle (L := U d.radical z) index_ne_zero_of_finite
  rw [inf_relIndex_left] at hupper
  have hAS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hlo := h.replacement_natural_fixed_index_lower d geometry hb path.end_color
    (Z d.radical a) hAS path.critical.2
  have hUS : U d.radical z ≤ stabilizer d.radical a :=
    (U_le_Z z).trans (path.endpoint_Z_le_start_stabilizer (by omega))
  have hCa := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) a path.start_color
  have hfix : U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ Q d.radical a := by
    rw [←hCa]
    ext r
    exact ⟨fun hr => ⟨hr.1,hUS hr.1,hr.2⟩,fun hr => ⟨hr.1,hr.2.2⟩⟩
  have hidxeq : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z)=(Q d.radical a).relIndex (U d.radical z) := by
    rw [←inf_relIndex_left,hfix,inf_relIndex_left]
  rw [hidxeq] at hlo
  exact hlo.trans hupper

/-- The full-radius nontrapping theorem supplies a backward critical path
with every overlapping vertex retained. -/
theorem Input.replacement_critical_backward_extension
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical) :
    ∃ v, ∃ back : CriticalPath d.radical geometry v
      (path.walk.getVert (path.walk.length-2)),
      ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i := by
  have hlen : 4 ≤ path.walk.length := by rwa [path.length_eq_b]
  have hat : Adjacent d.radical a (path.walk.getVert 1) := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hn := h.replacement_radius_not_trapped d path hb hat rfl
  obtain ⟨v,hv,hva,hvQ⟩ : ∃ v, color d.radical v=false ∧
      (cosetGraph d.radical).dist v a ≤ 2 ∧
      ¬ Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) := by
    simpa only [V_le_iff d.radical path.start_color,not_forall,exists_prop] using hn
  have hmin := criticalDistance_le d.radical v (geometry.exists_critical v hv) hvQ
  rw [geometry.distance_constant v hv] at hmin
  change geometry.b d.radical ≤ _ at hmin
  have htri := (cosetGraph_connected d.radical).dist_triangle (u := v) (v := a)
    (w := path.walk.getVert (path.walk.length-2))
  have hpa : (cosetGraph d.radical).dist a (path.walk.getVert (path.walk.length-2))=
      geometry.b d.radical-2 := (path.dist_start (Nat.sub_le _ _)).trans
        (congrArg (fun k => k-2) path.length_eq_b)
  rw [hpa] at htri
  have hd : (cosetGraph d.radical).dist a v=2 := by
    rw [SimpleGraph.dist_comm]
    omega
  obtain ⟨t,hat,hvt⟩ := exists_common_neighbor_of_dist_two d.radical a v hd
  obtain ⟨back,_,hover⟩ := exists_backward_path_of_not_le geometry (by omega) path hat hvt hvQ
  exact ⟨v,back,hover⟩

private theorem critical_segment_at_terminal
    {geometry : Geometry d.radical} (hb : 4 ≤ geometry.b d.radical) :
    ∀ k, ∀ {a z : Vertex d.radical} (path : CriticalPath d.radical geometry a z)
      (i : ℕ), path.walk.length-i=k → Even i → i+2 ≤ path.walk.length →
      ∃ v e, ∃ back : CriticalPath d.radical geometry v e,
        e=path.walk.getVert (i+2) ∧
        back.walk.getVert (back.walk.length-2)=path.walk.getVert i := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro a z path i hk hi hle
    by_cases hend : i+2=path.walk.length
    · refine ⟨a,z,path,?_,?_⟩
      · rw [hend,SimpleGraph.Walk.getVert_length]
      · congr 1
        omega
    · have heven : Even path.walk.length := by
        rw [path.length_eq_b]
        exact geometry.even (alpha d.radical) rfl
      have hi4 : i+4 ≤ path.walk.length := by
        rw [Nat.even_iff] at hi heven
        omega
      obtain ⟨v,back,hover⟩ := h.replacement_critical_backward_extension d path hb
      have hlength : back.walk.length=path.walk.length :=
        back.length_eq_b.trans path.length_eq_b.symm
      obtain ⟨v',e,back',he,hp⟩ := ih (back.walk.length-(i+2))
        (by rw [hlength]; omega) back (i+2) rfl (hi.add (by decide))
        (by rw [hlength]; omega)
      refine ⟨v',e,back',?_,?_⟩
      · exact he.trans (hover (i+2) (by omega))
      · exact hp.trans (hover i (by omega))

/-- The original first two-edge segment can be placed at the end of a
critical path, preserving the actual first neighbor. -/
theorem Input.replacement_first_segment_terminal_witness
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical) :
    ∃ v, ∃ back : CriticalPath d.radical geometry v (path.walk.getVert 2),
      back.walk.getVert (back.walk.length-2)=a := by
  obtain ⟨v,e,back,he,hp⟩ := critical_segment_at_terminal h d hb path.walk.length path 0
    (by omega) (by decide) (by rw [path.length_eq_b]; omega)
  simp only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] at he hp
  subst e
  exact ⟨v,back,hp⟩

/-- The actual first two-step neighbor satisfies the source (5.8) lower
bound, without replacing it by an unrelated moving neighbor. -/
theorem Input.replacement_path_moving_index_ge_field
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical) :
    Nat.card F ≤ (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) := by
  obtain ⟨v,back,hp⟩ := h.replacement_first_segment_terminal_witness d path hb
  have hi := h.replacement_terminal_moving_index_ge_field d back hb
  rwa [hp] at hi

/-- The same backward path supplies the actual escaping seed in T₀.
Its centralization of U_c intersect B_a is proved from the terminal
intersection, rather than inferred from distance alone. -/
theorem Input.replacement_kernelCentralizer_critical_witness
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical) :
    ∃ v, ∃ back : CriticalPath d.radical geometry v (path.walk.getVert 2),
      back.walk.getVert (back.walk.length-2)=a ∧
      Z d.radical v ≤ kernelCentralizer geometry a (path.walk.getVert 2) := by
  obtain ⟨v,back,hp⟩ := h.replacement_first_segment_terminal_witness d path hb
  obtain ⟨x,hx,ht,_⟩ := h.replacement_terminal_edge_residual_twist d back hb
  have hfix := terminal_B_intersection_le_kernel back hb x hx ht
  rw [hp] at hfix
  have hd := back.dist_start (Nat.sub_le back.walk.length 2)
  rw [hp,back.length_eq_b] at hd
  have hvQ : Z d.radical v ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical v (geometry.exists_critical v back.start_color)
    rw [geometry.distance_constant v back.start_color,hd]
    change geometry.b d.radical-2 < geometry.b d.radical
    omega
  exact ⟨v,back,hp,le_inf hvQ
    ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes v back.start_color)).trans
      (centralizer_le hfix))⟩

/-- The reciprocal moving index on the original first two vertices is
also at least the field order. -/
theorem Input.replacement_path_reciprocal_moving_index_ge_field
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical) :
    Nat.card F ≤ (B d.radical (path.walk.getVert 2) (geometry.Z_normal _)).relIndex
      (U d.radical a) := by
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  have hza := critical_reverse d.radical geometry hedge a path.start_color
    (by rw [geometry.distance_constant a path.start_color]; change 0 < geometry.b d.radical; omega)
    z path.end_color path.critical
  let back : CriticalPath d.radical geometry z a := ⟨path.end_color,path.walk.reverse,
    by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm],hza⟩
  have hi := h.replacement_terminal_moving_index_ge_field d back hb
  have hlen : 4 ≤ path.walk.length := by rw [path.length_eq_b]; exact hb
  have he : back.walk.getVert (back.walk.length-2)=path.walk.getVert 2 := by
    change path.walk.reverse.getVert (path.walk.reverse.length-2)=_
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,
      show path.walk.length-(path.walk.length-2)=2 by omega]
  rwa [he] at hi

/-- The source (5.9)(**) configuration on the original path now has no
extra moving-neighbor premise. Both moving indices, the escape of the
literal T₂, and the non-B conjugate seed are supplied by the same path. -/
theorem Input.replacement_strict_index_selected_path
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F) :
    (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2))=Nat.card F ∧
    ∃ y ∈ stabilizer d.radical (path.walk.getVert 2),
    let c := path.walk.getVert 2
    let mu := act d.radical y a
    let T₂ := (kernelCentralizer geometry a c).map (MulAut.conj y⁻¹).toMonoidHom
    let H₂ := conjugatedKernelCommutator geometry a c y
    let C₀ := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
    let Z₀ := conjugateSpanBy (Z d.radical mu) C₀
    let W := sourceCentralizerSpan d.radical c mu H₂
    ¬ Z d.radical mu ≤ B d.radical c (geometry.Z_normal c) ∧
    ¬ T₂ ≤ Q d.radical c ∧
    ¬ H₂ ≤ centralizer (V d.radical z : Set (FreeAmalgam d.radical)) ∧
    ∃ e, ∃ selected : CriticalPath d.radical geometry c e,
      (cosetGraph d.radical).dist e z=2 ∧
      (∀ i ≤ path.walk.length-2, selected.walk.getVert i=path.walk.getVert (i+2)) ∧
      ¬ H₂ ≤ centralizer (Z d.radical e : Set (FreeAmalgam d.radical)) ∧
      C₀ ⊔ Z d.radical e=stabilizer d.radical c ∧
      Z₀ ≤ W ∧ W ≤ Q d.radical c ∧
      W ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧ W ≤ Q d.radical z := by
  have hlo := h.replacement_path_moving_index_ge_field d path hb.le
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hmove : ¬ U d.radical (path.walk.getVert 2) ≤ B d.radical a (geometry.Z_normal a) := by
    intro hh
    rw [relIndex_eq_one.mpr hh] at hlo
    omega
  obtain ⟨y,hy,hm⟩ := h.replacement_strict_index_exists_radius_moving_conjugate d path hb hsmall hmove
  refine ⟨le_antisymm hsmall hlo,y,hy,?_,?_,hm,
    h.replacement_strict_index_second_span_selection d path hb hsmall y hy hm⟩
  · intro hZB
    have hn := Escape.Propagation.Rigidity.B_normalized (geometry := geometry) (by omega)
      (path.walk.getVert 2) ((path.vertex_color (by rw [path.length_eq_b]; omega)).mpr (by decide))
    have he := mem_normalizer_iff_map_conj_eq.mp (hn ((stabilizer d.radical (path.walk.getVert 2)).inv_mem hy))
    change (B d.radical (path.walk.getVert 2) (geometry.Z_normal _)).map
      (MulAut.conj y⁻¹).toMonoidHom=B d.radical (path.walk.getVert 2) (geometry.Z_normal _) at he
    rw [Z_act,←he] at hZB
    have hZa := (map_le_map_iff_of_injective (MulAut.conj y⁻¹).injective).mp hZB
    have hi := h.replacement_path_reciprocal_moving_index_ge_field d path hb.le
    rw [relIndex_eq_one.mpr ((U_le_Z a).trans hZa)] at hi
    omega
  · intro hT
    have hQ : (Q d.radical (path.walk.getVert 2)).map (MulAut.conj y⁻¹).toMonoidHom=
        Q d.radical (path.walk.getVert 2) := by
      rw [←Q_act,show act d.radical y (path.walk.getVert 2)=path.walk.getVert 2 from hy]
    rw [←hQ] at hT
    have hTQ := (map_le_map_iff_of_injective (MulAut.conj y⁻¹).injective).mp hT
    obtain ⟨v,back,_,hvT⟩ := h.replacement_kernelCentralizer_critical_witness d path hb.le
    exact back.critical.2 (hvT.trans hTQ)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
