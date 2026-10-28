module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexCentralSpan
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Transport
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# The original shifted seed in the central strict-index branch

Transport the whole centralizer T₀, commutator H and vertex orbit by the
source conjugator y in G_(a+2). The resulting T₂, H₂ and V retain the
literal right action, all central attachments, and the same moving index.
The full orbit has displacement exactly H₂ and contains both source seeds.

If H₂ moves the original endpoint radius, the shifted initial vertex
cannot form a critical pair with that endpoint: concatenate the two
shifted initial edges with the unchanged tail. A critical pair would give
an actual shortest critical path, whose complete H₂ fixes that radius
by StrictIndexCentralSpan. Consequently the two opposite seeds lie in
each other's full kernels. This discharges the critical-pair alternative
on the same source y, rather than selecting a different path witness.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.9), printed pp.920--921. Existence of y with (**), the subsequent
second-span comparison, strict index and distance-two reduction remain.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
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

omit h in
private theorem strict_kernel_covariance
    (geometry : Geometry d.radical) (hb : 2 < geometry.b d.radical)
    {a c : Vertex d.radical} (ha : color d.radical a=false)
    (y : FreeAmalgam d.radical) :
    kernelCentralizer geometry (act d.radical y a) (act d.radical y c) =
      (kernelCentralizer geometry a c).map (MulAut.conj y⁻¹).toMonoidHom ∧
    kernelCommutator geometry (act d.radical y a) (act d.radical y c) =
      conjugatedKernelCommutator geometry a c y := by
  have he : kernelCentralizer geometry (act d.radical y a) (act d.radical y c) =
      (kernelCentralizer geometry a c).map (MulAut.conj y⁻¹).toMonoidHom := by
    change Q d.radical (act d.radical y a) ⊓ centralizer
      ((U d.radical (act d.radical y c) ⊓ B d.radical (act d.radical y a) (geometry.Z_normal _) : Subgroup _) : Set _) =
      (Q d.radical a ⊓ centralizer ((U d.radical c ⊓ B d.radical a (geometry.Z_normal a) : Subgroup _) : Set _)).map _
    rw [map_inf _ _ _ (MulAut.conj y⁻¹).injective,Theory.GroupTheory.map_centralizer_equiv]
    change Q d.radical (act d.radical y a) ⊓ centralizer
      ((U d.radical (act d.radical y c) ⊓ B d.radical (act d.radical y a) (geometry.Z_normal _) :
        Subgroup (FreeAmalgam d.radical)) : Set _) =
      (Q d.radical a).map (MulAut.conj y⁻¹).toMonoidHom ⊓ centralizer
        (((U d.radical c ⊓ B d.radical a (geometry.Z_normal a)).map
          (MulAut.conj y⁻¹).toMonoidHom : Subgroup (FreeAmalgam d.radical)) : Set _)
    rw [Q_act,U_act,Escape.PairingControl.FirstPairing.B_act hb y a ha,
      map_inf _ _ _ (MulAut.conj y⁻¹).injective]

  refine ⟨he,?_⟩
  change ⁅U d.radical (act d.radical y c),kernelCentralizer geometry (act d.radical y a) (act d.radical y c)⁆ =
    (⁅U d.radical c,kernelCentralizer geometry a c⁆).map _
  rw [he,U_act,map_commutator]

/-- The original y and its complete T₂, H₂ and V keep the same source maps. -/
theorem Input.replacement_strict_index_conjugated_span
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical (path.walk.getVert 2)) :
    let c := path.walk.getVert 2
    let mu := act d.radical y a
    let T₂ := (kernelCentralizer geometry a c).map (MulAut.conj y⁻¹).toMonoidHom
    let H₂ := conjugatedKernelCommutator geometry a c y
    let W := sourceSeedSpan d.radical c mu
    kernelCentralizer geometry mu c=T₂ ∧ kernelCommutator geometry mu c=H₂ ∧
      Z d.radical c ≤ W ∧ Z d.radical mu ≤ W ∧ W ≤ V d.radical mu ∧ W ≤ Q d.radical c ∧
      stabilizer d.radical mu ≤ normalizer (W : Set _) ∧
      ⁅W,T₂⁆=H₂ ∧ H₂ ≤ Z d.radical c ∧
      H₂ ≤ centralizer (stabilizer d.radical mu : Set (FreeAmalgam d.radical)) := by
  dsimp only
  let c := path.walk.getVert 2
  have hc : color d.radical c=false :=
    (path.vertex_color (by rw [path.length_eq_b]; omega)).mpr (by decide)
  have hyfix : act d.radical y c=c := hy
  obtain ⟨hT,hH⟩ := strict_kernel_covariance d geometry (by omega) path.start_color y (c := c)
  rw [hyfix] at hT hH
  obtain ⟨hZc,hZa,hWV,hn,he⟩ := h.replacement_strict_index_central_span_displacement d path hb hsmall
  have hspan : (sourceSeedSpan d.radical c a).map (MulAut.conj y⁻¹).toMonoidHom =
      sourceSeedSpan d.radical c (act d.radical y a) := by
    change (conjugateSpanBy _ _).map _=conjugateSpanBy _ _
    rw [map_conjugateSpanBy,←Z_act,←stabilizer_act,hyfix]
  have hseed := map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hZa
  rw [←Z_act,hspan] at hseed
  have hrad := map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hWV
  rw [hspan,←V_act] at hrad
  have hdisp := congrArg (Subgroup.map (MulAut.conj y⁻¹).toMonoidHom) he
  rw [map_commutator,hspan] at hdisp
  have hcent := map_mono (f := (MulAut.conj y⁻¹).toMonoidHom)
    (h.replacement_strict_index_kernel_central d path hb hsmall)
  rw [Theory.GroupTheory.map_centralizer_equiv] at hcent
  change conjugatedKernelCommutator geometry a c y ≤ centralizer
    (((stabilizer d.radical a).map (MulAut.conj y⁻¹).toMonoidHom : Subgroup _) : Set _) at hcent
  rw [←stabilizer_act] at hcent
  have hd : (cosetGraph d.radical).dist c (act d.radical y a) ≤ 2 := by
    have hh := dist_act d.radical y c a
    have hdca : (cosetGraph d.radical).dist c a=2 := by
      rw [SimpleGraph.dist_comm]
      exact path.dist_start (by rw [path.length_eq_b]; omega)
    rw [hyfix,hdca] at hh
    exact hh.le
  exact ⟨hT,hH,le_conjugateSpanBy _ _,hseed,hrad,sourceSeedSpan_le_Q geometry hb hc hd,
    le_normalizer_conjugateSpanBy _ _,hdisp,
    (h.replacement_strict_index_kernel_at_two_step d path hb hsmall).2.2.2.2 y hy,hcent⟩

omit h [Finite H] in
private theorem shifted_initial_path
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 2 ≤ geometry.b d.radical)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical (path.walk.getVert 2))
    (hn : ¬ Z d.radical (act d.radical y a) ≤ Q d.radical z) :
    ∃ shifted : CriticalPath d.radical geometry (act d.radical y a) z,
      shifted.walk.getVert 1=act d.radical y (path.walk.getVert 1) ∧
      ∀ i, shifted.walk.getVert (i+2)=path.walk.getVert (i+2) := by
  have hlen : 2 ≤ path.walk.length := by rwa [path.length_eq_b]
  have hat : Adjacent d.radical a (path.walk.getVert 1) := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have htc : Adjacent d.radical (path.walk.getVert 1) (path.walk.getVert 2) :=
    (cosetGraph_adj d.radical _ _).mp (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length))
  have htc' : Adjacent d.radical (act d.radical y (path.walk.getVert 1)) (path.walk.getVert 2) := by
    have hh := (adjacent_act_iff d.radical y _ _).mpr htc
    rwa [show act d.radical y (path.walk.getVert 2)=path.walk.getVert 2 from hy] at hh
  let q : (cosetGraph d.radical).Walk (act d.radical y a) (path.walk.getVert 2) :=
    .cons ((cosetGraph_adj d.radical _ _).mpr ((adjacent_act_iff d.radical y _ _).mpr hat))
      (.cons ((cosetGraph_adj d.radical _ _).mpr htc') .nil)
  let w := q.append (path.walk.drop 2)
  have hw : w.length=geometry.b d.radical := by
    rw [SimpleGraph.Walk.length_append,SimpleGraph.Walk.drop_length]
    change 2+(path.walk.length-2)=geometry.b d.radical
    rw [←path.length_eq_b]
    omega
  have hmu : color d.radical (act d.radical y a)=false := by
    rw [action_preserves_color]
    exact path.start_color
  have hmin := criticalDistance_le d.radical _ (geometry.exists_critical _ hmu) hn
  rw [geometry.distance_constant _ hmu] at hmin
  have hmax := SimpleGraph.dist_le w
  have hd : (cosetGraph d.radical).dist (act d.radical y a) z=geometry.b d.radical := by
    change geometry.b d.radical ≤ _ at hmin
    omega
  let shifted : CriticalPath d.radical geometry (act d.radical y a) z :=
    ⟨hmu,w,hw.trans hd.symm,hd.trans (geometry.distance_constant _ hmu).symm,hn⟩
  refine ⟨shifted,rfl,?_⟩
  intro i
  change (q.append (path.walk.drop 2)).getVert (i+2)=_
  rw [SimpleGraph.Walk.getVert_append,if_neg (by change ¬ i+2<2; omega)]
  change (path.walk.drop 2).getVert (i+2-2)=_
  rw [SimpleGraph.Walk.drop_getVert]
  congr 1
  omega

/-- If the same source H₂ moves the endpoint radius, its conjugate starting
vertex cannot be critical with that endpoint. Both literal kernels contain
the opposite seed. No new conjugator or smaller central quotient is chosen. -/
theorem Input.replacement_strict_index_shifted_critical_exclusion
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical (path.walk.getVert 2))
    (hmove : ¬ conjugatedKernelCommutator geometry a (path.walk.getVert 2) y ≤
      centralizer (V d.radical z : Set (FreeAmalgam d.radical))) :
    Z d.radical (act d.radical y a) ≤ Q d.radical z ∧
      Z d.radical z ≤ Q d.radical (act d.radical y a) := by
  have hmu : color d.radical (act d.radical y a)=false := by
    rw [action_preserves_color]
    exact path.start_color
  have hcfix : act d.radical y (path.walk.getVert 2)=path.walk.getVert 2 := hy
  have hsmall' : (B d.radical (act d.radical y a) (geometry.Z_normal _)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F := by
    rw [Escape.PairingControl.FirstPairing.B_act (by omega) y a path.start_color,
      ←hcfix,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective]
    exact hsmall
  have hH := (strict_kernel_covariance d geometry (by omega) path.start_color y
    (c := path.walk.getVert 2)).2
  rw [hcfix] at hH
  have hQ : Z d.radical (act d.radical y a) ≤ Q d.radical z := by
    by_contra hn
    obtain ⟨shifted,_,hover⟩ := shifted_initial_path d path (by omega) y hy hn
    have hsecond := hover 0
    simp only [Nat.zero_add] at hsecond
    have hh := h.replacement_strict_index_kernel_centralizes_endpoint_radius d shifted hb (by
      rw [hsecond]; exact hsmall')
    rw [hsecond,hH] at hh
    exact hmove hh
  refine ⟨hQ,?_⟩
  have hdc : (cosetGraph d.radical).dist (act d.radical y a) (path.walk.getVert 2)=2 := by
    have hh := dist_act d.radical y a (path.walk.getVert 2)
    rw [hcfix,path.dist_start (by rw [path.length_eq_b]; omega)] at hh
    exact hh
  have hdist : (cosetGraph d.radical).dist z (act d.radical y a) ≤ geometry.b d.radical := by
    have hh := (cosetGraph_connected d.radical).dist_triangle
      (u := act d.radical y a) (v := path.walk.getVert 2) (w := z)
    rw [hdc,path.dist_end] at hh
    have hlen : 2 ≤ path.walk.length := by rw [path.length_eq_b]; omega
    rw [SimpleGraph.dist_comm]
    have he := path.length_eq_b
    omega
  have hzS : Z d.radical z ≤ stabilizer d.radical (act d.radical y a) :=
    Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color) (by
      rw [geometry.distance_constant z path.end_color]; exact hdist)
  rw [←MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) _ hmu]
  exact le_inf hzS (le_centralizer_iff.mp (hQ.trans (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z path.end_color)))))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
