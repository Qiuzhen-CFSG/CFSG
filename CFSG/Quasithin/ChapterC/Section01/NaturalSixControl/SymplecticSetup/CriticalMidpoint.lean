module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.BackwardEscape
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.RadiusComplete
/-!
# Selected midpoint consequences for the native symplectic source

The first edge kernel preserves the opposite critical kernel in the starting
Z-layer: its point-core image is abelian, so its commutators with the opposite
layer centralize the starting layer. For a coordinated backward choice this
removes the first-edge normalization premise in the Baumann containment step;
normalization by the selected opposite generator remains explicit.

A small critical commutator centralizes the first edge kernel. When that kernel
and a nearby Z-layer generate the midpoint stabilizer, the commutator centralizes
that stabilizer. At critical distance four the derived-radius bound places it
in the midpoint X-layer, hence in every adjacent seed. The final theorem applies
these facts to the literal characteristic replacement of SourceData.

Source: Meierfrankenfeld--Stellmacher (1993), (5.12), printed pp.924--926,
using (5.2)(ii), (3.3)(ii), and the selected generators from (5.5).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

/-- The abelian point-core image preserves the opposite critical kernel
inside the starting Z-layer. -/
theorem critical_start_kernel_normalized_by_first_edge
    (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    {m c : Vertex R} (p : CriticalPath R s.geometry m c) :
    Q R (p.walk.getVert 1)≤normalizer ((Z R m⊓Q R c:Subgroup (FreeAmalgam R)):Set (FreeAmalgam R)) := by
  have hpos : 0<p.walk.length := p.length_eq_b ▸ s.criticalDistance_pos
  have hmt : Adjacent R m (p.walk.getVert 1) := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) hpos
  have hct : Z R c≤Q R (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt R c (s.geometry.exists_critical c p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,s.geometry.distance_constant c p.end_color]
    change p.walk.length-1<s.geometry.b R
    rw [←p.length_eq_b]
    omega
  have htG : Q R (p.walk.getVert 1)≤stabilizer R m :=
    fun _ hx => hx.2 _ (adjacent_symm R hmt)
  have hZmG : Z R m≤stabilizer R c := Z_le_stabilizer_of_dist_le m _ p.critical.1.le
  have hcomm : ⁅Q R (p.walk.getVert 1),Z R c⁆≤Q R m :=
    (commutator_mono le_rfl hct).trans (s.edge_derived_le_kernel u hfull p.start_color hmt)
  have hCm : Q R m≤centralizer (Z R m:Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R m p.start_color))
  have hCc : Q R c≤centralizer (Z R c:Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R c p.end_color))
  apply le_normalizer_iff.mpr
  intro q hq z hz
  have hzn : q*z*q⁻¹∈Z R m := le_normalizer_iff.mp (htG.trans (Z_normalized R m)) q hq z hz.1
  refine ⟨hzn,?_⟩
  rw [←s.C_eq_Q c p.end_color]
  refine ⟨hZmG hzn,?_⟩
  intro y hy
  have hk : ⁅q⁻¹,y⁆∈Q R m := hcomm (commutator_mem_commutator
    ((Q R (p.walk.getVert 1)).inv_mem hq) hy)
  have hzq : (q⁻¹*y*q)*z=z*(q⁻¹*y*q) := by
    rw [show q⁻¹*y*q=⁅q⁻¹,y⁆*y by simp [commutatorElement_def,mul_assoc]]
    rw [mul_assoc,hCc hz.2 y hy,←mul_assoc,←hCm hk z hz.1,mul_assoc]
  calc
    y*(q*z*q⁻¹)=q*((q⁻¹*y*q)*z)*q⁻¹ := by group
    _=q*(z*(q⁻¹*y*q))*q⁻¹ := congrArg (fun w : FreeAmalgam R => q*w*q⁻¹) hzq
    _=(q*z*q⁻¹)*y := by group

/-- The first-edge part of the selected kernel normality is automatic. The
opposite generator's normalization is the remaining input from source (5.12)(1). -/
theorem CoordinatedChoice.critical_kernel_le_B_of_selected_normalizer
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2<s.geometry.b R) {e : Vertex R}
    {p : CriticalPath R s.geometry (alpha R) e} {delta : Vertex R}
    (c : s.CoordinatedChoice p delta) {f : Vertex R}
    (q : CriticalPath R s.geometry c.alpha1 f)
    (hq : q.walk.getVert 1=c.beta1)
    (hn : Z R e≤normalizer
      (((Z R c.alpha1⊓Q R f)⊔Z R (alpha R):Subgroup (FreeAmalgam R)):Set (FreeAmalgam R))) :
    Z R c.alpha1⊓Q R f≤B R (alpha R) (s.geometry.Z_normal _) := by
  let A := Z R c.alpha1⊓Q R f
  let H := A⊔Z R (alpha R)
  let D := Z R c.alpha1⊔Z R (alpha R)
  have hD : D≤V R (alpha R) :=
    sup_le c.back_layer_le_radius (Z_le_VBall R (alpha R) 2)
  have hHD : H≤D := sup_le_sup_right inf_le_left _
  have hDV : D≤stabilizer R (alpha R) :=
    hD.trans ((V_le_Q R rfl hb).trans (fun _ hx => hx.1))
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite D := Finite.of_injective (inclusion hDV) (inclusion_injective _)
  have hHnorm : stabilizer R (alpha R)≤normalizer (H:Set (FreeAmalgam R)) := by
    rw [←c.generation,s.selectedCriticalLayer_eq h u hfull p]
    apply sup_le _ hn
    apply le_trans (le_inf _ _) (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · simpa only [hq] using s.critical_start_kernel_normalized_by_first_edge u hfull q
    · have hQt : Q R c.beta1≤stabilizer R (alpha R) :=
        fun _ hx => hx.2 _ (adjacent_symm R c.adjacent_start)
      exact hQt.trans (Z_normalized R (alpha R))
  have hi : (Z R (alpha R)).relIndex H≤8 :=
    (relIndex_le_of_le_right hHD index_ne_zero_of_finite).trans
      (c.backward_product_index_le_eight s h u hfull)
  exact le_trans le_sup_left (s.normal_radius_subgroup_le_B_of_index
    (s.projection_surjective_of_radical_image_le_conjugate u hfull.le) hb H
    (hHD.trans hD) hHnorm hi)

/-- The small critical line centralizes its first edge kernel at any start. -/
private theorem small_critical_commutator_le_first_centralizer_at
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    {m c : Vertex R} (p : CriticalPath R s.geometry m c)
    (hsmall : (Q R c).relIndex (Z R m)<4) :
    ⁅Z R m,Z R c⁆≤centralizer (Q R (p.walk.getVert 1):Set (FreeAmalgam R)) := by
  have hpos : 0<p.walk.length := p.length_eq_b ▸ s.criticalDistance_pos
  have hmt : Adjacent R m (p.walk.getVert 1) := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) hpos
  have hct : Z R c≤Q R (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt R c (s.geometry.exists_critical c p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,s.geometry.distance_constant c p.end_color]
    change p.walk.length-1<s.geometry.b R
    rw [←p.length_eq_b]
    omega
  exact s.small_edge_commutator_le_centralizer u hfull p.start_color hmt (Z R c) hct
    (s.small_critical_commutator_card h p hsmall).le

/-- The selected midpoint generator centralizes the small critical line. -/
theorem small_critical_commutator_le_selected_center
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    {m c : Vertex R} (p : CriticalPath R s.geometry m c)
    (hsmall : (Q R c).relIndex (Z R m)<4)
    (a e : Vertex R) (he : color R e=false)
    (hce : (cosetGraph R).dist c e<s.geometry.b R)
    (hgen : Q R (p.walk.getVert 1)⊔Z R e=stabilizer R a) :
    ⁅Z R m,Z R c⁆≤centralizer (stabilizer R a:Set (FreeAmalgam R)) := by
  have hRt := s.small_critical_commutator_le_first_centralizer_at h u hfull p hsmall
  have hRc : ⁅Z R m,Z R c⁆≤Z R c :=
    ((s.critical_Z_commutator_le_moving p).trans inf_le_right).trans (DistanceEight.U_le_Z R c)
  have hceQ : Z R c≤Q R e := by
    apply Z_le_Q_of_dist_lt R c (s.geometry.exists_critical c p.end_color)
    rwa [s.geometry.distance_constant c p.end_color]
  have hRe : ⁅Z R m,Z R c⁆≤centralizer (Z R e:Set (FreeAmalgam R)) :=
    (hRc.trans hceQ).trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R e he)))
  apply le_centralizer_iff.mp
  rw [←hgen]
  exact sup_le (le_centralizer_iff.mp hRt) (le_centralizer_iff.mp hRe)

/-- The same selected line lies in every neighboring seed once placed in X. -/
private theorem small_critical_commutator_le_selected_seed
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    {m c : Vertex R} (p : CriticalPath R s.geometry m c)
    (hsmall : (Q R c).relIndex (Z R m)<4)
    (a e : Vertex R) (ha : color R a=false) (he : color R e=false)
    (hce : (cosetGraph R).dist c e<s.geometry.b R)
    (hgen : Q R (p.walk.getVert 1)⊔Z R e=stabilizer R a)
    (hRa : ⁅Z R m,Z R c⁆≤X R a)
    (k : Vertex R) (hak : Adjacent R a k) : ⁅Z R m,Z R c⁆≤Z R k := by
  have hcenter := s.small_critical_commutator_le_selected_center h u hfull p hsmall a e he hce hgen
  have hk : color R k=true := by
    have hh := adjacent_color_ne R hak
    rw [ha] at hh
    cases he : color R k <;> simp_all
  have hRk : ⁅Z R m,Z R c⁆≤Q R k := (hRa.trans (omegaCenter_le _)).trans
    (Q_le_adjacent_h R hk hak)
  have hQka : Q R k≤stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hak)
  have hRZ : ⁅Z R m,Z R c⁆≤Z R m :=
    ((s.critical_Z_commutator_le_moving p).trans inf_le_left).trans (DistanceEight.U_le_Z R m)
  let := s.geometry.Z_elementary s.criticalDistance_pos m p.start_color
  intro r hr
  rw [Z,if_neg (by rw [hk]; decide)]
  exact mem_omegaCenter_iff.mpr ⟨hRk hr,
    elemPow_eq_one_of_isElementaryAbelian _ (hRZ hr),(hcenter.trans (centralizer_le hQka)) hr⟩
/-- At distance four, the selected midpoint centralizes the critical line,
and the derived-radius bound places that same line in every midpoint seed. -/
theorem small_critical_midpoint_seeds
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R=4) {m c : Vertex R} (p : CriticalPath R s.geometry m c)
    (hsmall : (Q R c).relIndex (Z R m)<4)
    (e : Vertex R) (he : color R e=false)
    (hce : (cosetGraph R).dist c e<s.geometry.b R)
    (hgen : Q R (p.walk.getVert 1)⊔Z R e=stabilizer R (p.walk.getVert 2)) :
    ⁅Z R m,Z R c⁆≤centralizer (stabilizer R (p.walk.getVert 2):Set (FreeAmalgam R)) ∧
      ∀ k, Adjacent R (p.walk.getVert 2) k → ⁅Z R m,Z R c⁆≤Z R k := by
  let a := p.walk.getVert 2
  have hl : p.walk.length=4 := p.length_eq_b.trans hb
  have ha : color R a=false := (p.vertex_color (by omega)).mpr (by decide)
  have hma : (cosetGraph R).dist m a≤2 := by
    rw [p.dist_start (by omega)]
  have hca : (cosetGraph R).dist c a≤2 := by
    change (cosetGraph R).dist c (p.walk.getVert 2)≤2
    rw [SimpleGraph.dist_comm,p.dist_end 2,hl]
  have hVm : Z R m≤V R a := le_iSup_of_le m (le_iSup_of_le hma le_rfl)
  have hVc : Z R c≤V R a := le_iSup_of_le c (le_iSup_of_le hca le_rfl)
  have hp : R.map s.projection≤Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
      (MulAut.conj u).toMonoidHom := by
    simpa only [Model.pointCore_eq_exceptional] using hfull.le
  have hRa : ⁅Z R m,Z R c⁆≤X R a := (commutator_mono hVm hVc).trans
    (s.radius_bounds_of_two_lt h u hp (by omega) ha m c).2.1
  refine ⟨s.small_critical_commutator_le_selected_center h u hfull p hsmall a e he hce hgen,?_⟩
  intro k hak
  exact s.small_critical_commutator_le_selected_seed h u hfull p hsmall a e ha he hce hgen hRa k hak
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K] {L W : Subgroup K} [L.Normal] [W.Normal]
  {T : Sylow 2 K} (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L⊔d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

/-- The literal characteristic replacement supplies the marked model in the
small selected-chain step of source (5.12), or gives the alternating block. -/
theorem reducedSource_block_or_small_critical_midpoint_seeds
    (r : CharacteristicReduction (L.subgroupOf J) R) {m c : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry m c)
    (hb : ((originalSource d hm).reduce r).geometry.b r.radical=4)
    (hsmall : (Q r.radical c).relIndex (Z r.radical m)<4)
    (e : Vertex r.radical) (he : color r.radical e=false)
    (hce : (cosetGraph r.radical).dist c e<4)
    (hgen : Q r.radical (p.walk.getVert 1)⊔Z r.radical e=
      stabilizer r.radical (p.walk.getVert 2)) :
    IsAlternatingBlock L 6 ∨
      (⁅Z r.radical m,Z r.radical c⁆≤centralizer
        (stabilizer r.radical (p.walk.getVert 2):Set (FreeAmalgam r.radical)) ∧
      ∀ k, Adjacent r.radical (p.walk.getVert 2) k → ⁅Z r.radical m,Z r.radical c⁆≤Z r.radical k) := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock|hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have hf : r.radical.map s.projection=Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    exact s.small_critical_midpoint_seeds (reduced_nativeCentralLayer d hm r) _ hf hb p hsmall e he
      (by simpa only [hb] using hce) hgen
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
