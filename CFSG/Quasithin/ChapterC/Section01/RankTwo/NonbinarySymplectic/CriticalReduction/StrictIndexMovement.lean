module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TrappedRootComparison

/-!
# Constructing the radius-moving conjugator in source (5.9)

If the complete H = [U_c,T₀] vanishes, the full first orbit centralizes the
terminal subgroup. Its penultimate-kernel placement and the source (3.3)
bound make its displacement under the critical endpoint lie in Z_a.
Normality and the original simple quotient then put the orbit in B_a.
Thus the earlier source moving-neighbor clause U_c not <= B_a makes H
nonzero, with every central attachment retained.

Apply (5.8) to the reverse of the same critical path: the full endpoint
radius escapes Q_c. One of its seeds is therefore critical with c. The
natural-cover fixed-commutator theorem shows that the nonzero H is not
central at c. The original simple-quotient conjugation argument supplies
y in G_c with H^y moving that radius. The existing second-span selector
then constructs its terminal critical path, whole-H^y centralizer
generation, all original path overlaps and both full second-span kernels.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.8) and (5.9)(**), printed pp.920--921. The moving-neighbor
premise is the nontrivial-index consequence of earlier (5.8); this module
discharges the later radius-movement premise on y. The full (5.8) selector
applications, R₃ centrality, second-span displacement comparison, strict
index, terminal exclusions and minimum-replacement distance-two witness
remain with the critical-reduction assembly. No field restriction, central
complement or quotient-kernel replacement is introduced.
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
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Vanishing of the complete source displacement forces the starting
neighbor into the original fixed preimage. -/
theorem Input.replacement_strict_index_zero_kernel_le_B
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F)
    (hzero : kernelCommutator geometry a (path.walk.getVert 2)=⊥) :
    U d.radical (path.walk.getVert 2) ≤ B d.radical a (geometry.Z_normal a) := by
  let p := path.walk.getVert (path.walk.length-2)
  let W := sourceSeedSpan d.radical (path.walk.getVert 2) a
  obtain ⟨hZc,_,hWV,hn,hdisp⟩ :=
    h.replacement_strict_index_central_span_displacement d path hb hsmall
  obtain ⟨_,_,htail,_,_⟩ := h.replacement_strict_index_kernel_at_two_step d path hb hsmall
  have hWfix : W ≤ centralizer ((Z d.radical p ⊔
      (Z d.radical z ⊓ Q d.radical a) : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    have hh := commutator_eq_bot_iff_le_centralizer.mp (hdisp.trans hzero)
    exact hh.trans (centralizer_le htail)
  have hWp : W ≤ stabilizer d.radical p := hWV.trans
    (CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.radius_le_stabilizer_of_distance
      d.radical geometry path.start_color (by
      dsimp only [p]
      rw [path.dist_start (Nat.sub_le _ _),path.length_eq_b]
      omega))
  have hp : color d.radical p=false := by
    apply (path.vertex_color (Nat.sub_le _ _)).mpr
    have he : Even path.walk.length := by
      rw [path.length_eq_b]
      exact geometry.even (alpha d.radical) rfl
    rw [Nat.even_iff] at he ⊢
    omega
  have hWQ : W ≤ Q d.radical p := by
    rw [←MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
      (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) p hp]
    exact le_inf hWp (hWfix.trans (centralizer_le (fun _ hx => mem_sup_left hx)))
  have hWz : W ≤ stabilizer d.radical z :=
    (le_inf hWV hWQ).trans
      (CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.truncated_radius_le_endpoint_stabilizer path (by omega))
  have hWQa : W ≤ Q d.radical a := hWV.trans (geometry.V_le_Q (by omega) a path.start_color)
  have hzS := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  have hWA : W ≤ centralizer ((Z d.radical z ⊓ Q d.radical a :
      Subgroup (FreeAmalgam d.radical)) : Set _) :=
    hWfix.trans (centralizer_le (fun _ hx => mem_sup_right hx))
  have hWend : ⁅W,Z d.radical z⁆ ≤ Z d.radical a := by
    rw [commutator_comm]
    exact (h.replacement_critical_fixed_intersection_displacement d path (by omega)
      W hWz hWQa hWA).trans
      (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path)
  obtain ⟨E,hE,f,hf,hfQ,_⟩ := h.replacement_inner_natural_action d geometry hb.le path.start_color
  have hlarge : 3 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 3 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup hlarge
  let : IsSimpleGroup (Sp E.Carrier) :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
  have hk : f.ker=(Q d.radical a).subgroupOf (stabilizer d.radical a) := by
    apply map_injective (stabilizer d.radical a).subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical a ≤ stabilizer d.radical a from fun _ hv => hv.1)]
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  have hzQ := (critical_reverse d.radical geometry hedge a path.start_color
    (by rw [geometry.distance_constant a path.start_color]; change 0 < geometry.b d.radical; omega)
    z path.end_color path.critical).2
  have hWB := normal_radius_le_B_of_kernel_escape geometry (by omega) path.start_color f hf hk
    (Q_isPGroup d.radical (h.replacement_two_group d) (h.replacement_core_le d) a path.start_color)
    W (Z d.radical z) hWV hn hzS hzQ hWend
  exact (U_le_Z _).trans (hZc.trans hWB)

/-- The full endpoint radius escapes the actual two-step vertex kernel.
This is the reverse-path application of source (5.8). -/
theorem Input.replacement_endpoint_radius_not_le_two_step_kernel
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical) :
    ¬ V d.radical z ≤ Q d.radical (path.walk.getVert 2) := by
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  have hza := critical_reverse d.radical geometry hedge a path.start_color
    (by rw [geometry.distance_constant a path.start_color]; change 0 < geometry.b d.radical; omega)
    z path.end_color path.critical
  let back : CriticalPath d.radical geometry z a := ⟨path.end_color,path.walk.reverse,
    by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm],hza⟩
  have hlen : 4 ≤ path.walk.length := by rw [path.length_eq_b]; exact hb
  have hfirst : Adjacent d.radical z (back.walk.getVert 1) := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (back.walk.adj_getVert_succ (by change 0 < path.walk.reverse.length; rw [SimpleGraph.Walk.length_reverse]; omega))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hn := h.replacement_radius_not_trapped d back hb hfirst rfl
  have he : back.walk.getVert (back.walk.length-2)=path.walk.getVert 2 := by
    change path.walk.reverse.getVert (path.walk.reverse.length-2)=_
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,
      show path.walk.length-(path.walk.length-2)=2 by omega]
  rwa [he] at hn

/-- The original moving-neighbor clause makes H nonzero. A conjugate of
that same whole H moves the endpoint radius, so no movement of y is assumed. -/
theorem Input.replacement_strict_index_exists_radius_moving_conjugate
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F)
    (hmove : ¬ U d.radical (path.walk.getVert 2) ≤ B d.radical a (geometry.Z_normal a)) :
    ∃ y ∈ stabilizer d.radical (path.walk.getVert 2),
      ¬ conjugatedKernelCommutator geometry a (path.walk.getVert 2) y ≤
        centralizer (V d.radical z : Set (FreeAmalgam d.radical)) := by
  let c := path.walk.getVert 2
  let H₀ := kernelCommutator geometry a c
  have hc : color d.radical c=false :=
    (path.vertex_color (by rw [path.length_eq_b]; omega)).mpr (by decide)
  have hid : (MulAut.conj (1 : FreeAmalgam d.radical)).toMonoidHom=MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    simp
  have hHz : H₀ ≤ Z d.radical c := by
    have hh := (h.replacement_strict_index_kernel_at_two_step d path hb hsmall).2.2.2.2
      1 (one_mem _)
    simpa only [conjugatedKernelCommutator,inv_one,hid,Subgroup.map_id] using hh
  have hHn : ¬ H₀ ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
    intro hh
    have hTS : kernelCentralizer geometry a c ≤ stabilizer d.radical c := by
      have ht := kernelCentralizer_conjugate_le_stabilizer geometry path (by omega) 1 (one_mem _)
      simpa only [inv_one,hid,Subgroup.map_id] using ht
    have hfixed : ⁅kernelCentralizer geometry a c,U d.radical c⁆ ≤
        centralizer (Ltilde d.radical c : Set (FreeAmalgam d.radical)) := by
      rw [commutator_comm]
      exact hh.trans (centralizer_le (Ltilde_le_stabilizer c))
    have hz := (h.replacement_natural_commutator_fixed_iff d geometry hb.le hc
      (kernelCentralizer geometry a c) (U d.radical c) hTS le_rfl).mp hfixed
    rw [commutator_comm] at hz
    exact hmove (h.replacement_strict_index_zero_kernel_le_B d path hb hsmall hz)
  have hVQ := h.replacement_endpoint_radius_not_le_two_step_kernel d path hb.le
  obtain ⟨e,hecol,hed,heQ⟩ : ∃ e, color d.radical e=false ∧
      (cosetGraph d.radical).dist e z ≤ 2 ∧ ¬ Z d.radical e ≤ Q d.radical c := by
    simpa only [V_le_iff d.radical path.end_color,not_forall,exists_prop] using hVQ
  have hmin := criticalDistance_le d.radical e (geometry.exists_critical e hecol) heQ
  rw [geometry.distance_constant e hecol] at hmin
  change geometry.b d.radical ≤ _ at hmin
  have hzc : (cosetGraph d.radical).dist z c=geometry.b d.radical-2 := by
    rw [SimpleGraph.dist_comm,path.dist_end,path.length_eq_b]
  have htri := (cosetGraph_connected d.radical).dist_triangle (u := e) (v := z) (w := c)
  have hec : CriticalPair d.radical e c (geometry.exists_critical e hecol) := by
    refine ⟨?_,heQ⟩
    rw [geometry.distance_constant e hecol]
    change _=geometry.b d.radical
    omega
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  have hce := critical_reverse d.radical geometry hedge e hecol
    (by rw [geometry.distance_constant e hecol]; change 0 < geometry.b d.radical; omega) c hc hec
  obtain ⟨g,hg,x,hx,hxm⟩ := h.replacement_noncentral_seed_conjugate_escape d
    (CriticalPath.ofPair hc hce) hb.le H₀ hHz hHn
  refine ⟨g⁻¹,(stabilizer d.radical c).inv_mem hg,?_⟩
  intro hh
  have hx' : g*x*g⁻¹ ∈ conjugatedKernelCommutator geometry a c g⁻¹ := by
    change g*x*g⁻¹ ∈ H₀.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom
    rw [inv_inv]
    exact mem_map_of_mem _ hx
  have hEV : Z d.radical e ≤ V d.radical z :=
    le_iSup_of_le e (le_iSup_of_le hed le_rfl)
  exact hxm ((centralizer_le hEV) (hh hx'))

/-- Source (5.9)(**) with its actual moving-neighbor premise: the conjugator,
terminal critical path, whole-H₂ generation and both original second spans
are constructed simultaneously. -/
theorem Input.replacement_strict_index_source_selection
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F)
    (hmove : ¬ U d.radical (path.walk.getVert 2) ≤ B d.radical a (geometry.Z_normal a)) :
    ∃ y ∈ stabilizer d.radical (path.walk.getVert 2),
    let c := path.walk.getVert 2
    let mu := act d.radical y a
    let H₂ := conjugatedKernelCommutator geometry a c y
    let C₀ := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
    let Z₀ := conjugateSpanBy (Z d.radical mu) C₀
    let W := sourceCentralizerSpan d.radical c mu H₂
    ∃ e, ∃ selected : CriticalPath d.radical geometry c e,
      (cosetGraph d.radical).dist e z=2 ∧
      (∀ i ≤ path.walk.length-2, selected.walk.getVert i=path.walk.getVert (i+2)) ∧
      ¬ H₂ ≤ centralizer (Z d.radical e : Set (FreeAmalgam d.radical)) ∧
      C₀ ⊔ Z d.radical e=stabilizer d.radical c ∧
      Z₀ ≤ W ∧ W ≤ Q d.radical c ∧
      W ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧ W ≤ Q d.radical z := by
  obtain ⟨y,hy,hm⟩ := h.replacement_strict_index_exists_radius_moving_conjugate d path hb hsmall hmove
  exact ⟨y,hy,h.replacement_strict_index_second_span_selection d path hb hsmall y hy hm⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
