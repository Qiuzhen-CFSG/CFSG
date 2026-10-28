module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceSixCentralizer
public import Theory.GroupTheory.CentralizerInjectiveImage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.P1Comparison.Lifting

/-!
# Triviality of the moving fixed attachment after MS93 (3.7)(6)

Choose the genuine field-sized critical pair already constructed in source
(6). Its moving fixed attachment A lies in the critical commutator. At any
other neighbor of the midpoint, source (4) either identifies its attachment
with A or both critical Z-layers lie in that neighbor's full core. In the
second case their commutator lies in its Frattini subgroup and hence in its
component-fixed core. Thus A centralizes every neighboring component.

The midpoint omega-center intersected with the centralizer of the span of
those components is normal in both incident vertex stabilizers. The actual
characteristic amalgam has no nontrivial such subgroup. This proves A = 1,
then conjugation transports the result to every vertex of the component
color. The full fixed core D is retained throughout.

Consequently the original critical commutator has order q. The literal
quotient by D also preserves the overlap index: its kernel on Z_a Z_z
lies in Z_a intersect Z_z, since the fixed part of Z_a lies in the midpoint
center. The final configuration supplies these two SourceEndgame premises,
together with the proved whole-core decomposition and its disjoint factors.
It does not assert the remaining point-parabolic or relative-centralizer
geometry, nor the degree-two or block conclusions.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the paragraph after (3.7)(6), printed p.876, referring to the last
paragraph of (3.6), printed p.872; quotient conventions on printed p.877.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F) (d : CharacteristicReduction K R)
include h

private theorem edge_center_fixed_by_neighbors_eq_bot
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) (c : EdgeMarking h d a t)
    (A : Subgroup (FreeAmalgam d.radical)) (hAZ : A ≤ Z d.radical t)
    (hAC : ∀ v : Vertex d.radical, Adjacent d.radical v t →
      A ≤ centralizer (Ltilde d.radical v : Set (FreeAmalgam d.radical))) : A=⊥ := by
  let W := ⨆ v : Vertex d.radical, ⨆ (_ : Adjacent d.radical v t), Ltilde d.radical v
  let N := Z d.radical t ⊓ centralizer (W : Set (FreeAmalgam d.radical))
  have hAN : A ≤ N := le_inf hAZ (le_centralizer_iff.mp (iSup_le fun v => iSup_le fun hv =>
    le_centralizer_iff.mp (hAC v hv)))
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hat (ha.trans he.symm)
  have hZQ : Z d.radical t ≤ Q d.radical t := by
    rw [show Z d.radical t=omegaCenter (Q d.radical t) by simp [Z,ht,edgeOmega]]
    exact omegaCenter_le _
  have hZC : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [show Z d.radical t=omegaCenter (Q d.radical t) by simp [Z,ht,edgeOmega]]
    exact fun y hy => (mem_omegaCenter_iff.mp hy).2.2
  have hNS : N ≤ stabilizer d.radical a ⊓ stabilizer d.radical t :=
    le_inf ((inf_le_left.trans hZQ).trans c.edge_le)
      ((inf_le_left.trans hZQ).trans (fun _ hx => hx.1))
  have hNC : N ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    rw [←c.residual_sup_core g (by omega)]
    apply le_centralizer_iff.mp
    apply sup_le
    · exact le_centralizer_iff.mp (inf_le_right.trans
        (centralizer_le (show Ltilde d.radical a ≤ W from
          le_iSup_of_le a (le_iSup_of_le hat le_rfl))))
    · exact le_centralizer_iff.mp ((inf_le_left.trans hZC).trans (centralizer_le c.core_le_edge))
  have hWN : stabilizer d.radical t ≤ normalizer (W : Set (FreeAmalgam d.radical)) := by
    apply le_normalizer_iff.mpr
    intro x hx w hw
    have hxT : act d.radical x⁻¹ t=t := (stabilizer d.radical t).inv_mem hx
    have hm : W.map (MulAut.conj x).toMonoidHom ≤ W := by
      dsimp only [W]
      rw [Subgroup.map_iSup]
      apply iSup_le
      intro v
      rw [Subgroup.map_iSup]
      apply iSup_le
      intro hv
      have hvT : Adjacent d.radical (act d.radical x⁻¹ v) t := by
        simpa only [hxT] using (adjacent_act_iff d.radical x⁻¹ v t).mpr hv
      have he := Ltilde_act d.radical x⁻¹ v
      rw [inv_inv] at he
      rw [←he]
      exact le_iSup_of_le _ (le_iSup_of_le hvT le_rfl)
    exact hm (mem_map_of_mem _ hw)
  have hNt : stabilizer d.radical t ≤ normalizer (N : Set (FreeAmalgam d.radical)) :=
    (le_inf (Z_normalized d.radical t)
      (hWN.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hNb : N=⊥ := no_common_normal_at_edge d.radical (replacement_characteristic h d)
    a t ha hat N hNS
    (normal_subgroupOf_of_le_normalizer
      ((le_centralizer_iff.mp hNC).trans (Subgroup.centralizer_le_normalizer _)))
    (normal_subgroupOf_of_le_normalizer hNt)
  exact le_bot_iff.mp (hAN.trans hNb.le)

private theorem fixed_attachments_eq_or_contained
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a v t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) (hvt : Adjacent d.radical v t)
    (c : EdgeMarking h d a t) (cv : EdgeMarking h d v t) :
    U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical v ⊓ centralizer (Ltilde d.radical v : Set (FreeAmalgam d.radical)) ∨
      Z d.radical a ≤ Q d.radical v := by
  by_cases hin : Z d.radical a ≤ Q d.radical v
  · exact Or.inr hin
  have hneq : a≠v := by
    intro he
    subst v
    exact hin ((g.omega_bound a ha (by
      rw [g.distance_constant a ha]; change 0<g.b d.radical; omega)).trans (omegaCenter_le _))
  have hd : (cosetGraph d.radical).dist a v=2 :=
    Escape.Propagation.neighbor_distance_two ha hat hvt hneq
  let p : CriticalPath d.radical g a v := CriticalPath.ofPair ha
    ⟨by rw [hd,g.distance_constant a ha]; exact hb.symm,hin⟩
  exact Or.inl (source_four_fixed_attachments h d g hb hsat p hat hvt c cv)

private theorem core_derived_le_fixed
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    {a : Vertex d.radical} (ha : color d.radical a=false) :
    ⁅Q d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a := by
  let := finite_stabilizer d.radical a
  let : Finite (Q d.radical a) := Finite.of_injective
    (inclusion (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1))
    (inclusion_injective _)
  let : Fact (IsPGroup 2 (Q d.radical a)) := ⟨Q_isPGroup d.radical
    (replacement_isPGroup h d) (replacement_core_le h d) a ha⟩
  have hh := map_mono (f := (Q d.radical a).subtype)
    (commutator_le_frattini_of_isPGroup (R := Q d.radical a) (p := 2))
  have hd : ⁅Q d.radical a,Q d.radical a⁆ ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype := by
    simpa only [commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype] using hh
  exact hd.trans (frattini_le_fixedCore h d g hb ha)

private theorem field_critical_fixed_attachment_eq_bot
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a)=2^n) :
    U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))=⊥ := by
  let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
  have he := source_four_fixed_attachments h d g hb hsat path hat hzt c c'
  have hAR := (critical_fixed_layer_index h d path hb hat hzt hcritical).1
  apply edge_center_fixed_by_neighbors_eq_bot h d g hb path.start_color hat c A
    ((inf_le_inf_right _ ((U_le_Z a).trans (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0<g.b d.radical; omega)))).trans
      (replacement_fixed_X_le_edge h d (g := g) (by omega) path.start_color hat))
  intro v hvt
  have hv : color d.radical v=false := by
    have ht : color d.radical t=true := by
      apply Bool.eq_true_of_not_eq_false
      intro hh
      exact adjacent_color_ne d.radical hat (path.start_color.trans hh.symm)
    cases hv : color d.radical v
    · rfl
    · exact (adjacent_color_ne d.radical hvt (hv.trans ht.symm)).elim
  obtain ⟨cv⟩ := exists_edgeMarking h d g (by omega) hv hvt
  rcases fixed_attachments_eq_or_contained h d g hb hsat path.start_color hat hvt c cv with hA | hQa
  · exact hA.le.trans inf_le_right
  rcases fixed_attachments_eq_or_contained h d g hb hsat path.end_color hzt hvt c' cv with hA | hQz
  · exact (he.trans hA).le.trans inf_le_right
  exact (hAR.trans ((commutator_mono hQa hQz).trans (core_derived_le_fixed h d g hb hv))).trans inf_le_right

/-- The fixed attachment inside the moving layer vanishes. This is the
paragraph immediately following MS93 (3.7)(6); the full core D is retained. -/
theorem source_moving_fixed_attachment_eq_bot
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {b : Vertex d.radical} (hbcolor : color d.radical b=false) :
    U d.radical b ⊓ centralizer (Ltilde d.radical b : Set (FreeAmalgam d.radical))=⊥ := by
  obtain ⟨a,z,⟨path⟩,hcritical⟩ := source_six_exists_field_critical_pair h d g hb hsat
  have hd : (cosetGraph d.radical).dist a z=2 :=
    path.critical.1.trans ((g.distance_constant a path.start_color).trans hb)
  obtain ⟨t,hat,hzt⟩ := exists_common_neighbor_of_dist_two d.radical a z hd
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hA := field_critical_fixed_attachment_eq_bot h d g hb hsat path hat hzt c c' hcritical
  obtain ⟨x,hx⟩ := exists_mVertex_of_color d.radical path.start_color
  obtain ⟨y,hy⟩ := exists_mVertex_of_color d.radical hbcolor
  have hab : act d.radical (x⁻¹*y) a=b := by
    rw [hx,hy,act_mVertex,mul_inv_cancel_left]
  rw [←hab,U_act,Ltilde_act,map_inf_centralizer_of_injective _ (MulAut.conj _).injective,
    hA,Subgroup.map_bot]

/-- Source (3.7)'s moving group meets the complete fixed core trivially,
without identifying that fixed core with the moving attachment. -/
theorem source_moving_disjoint_fixedCore
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a : Vertex d.radical} (ha : color d.radical a=false) :
    Disjoint (U d.radical a) (fixedCore d.radical a) := by
  apply disjoint_iff_inf_le.mpr
  exact (inf_le_inf_left _ (show fixedCore d.radical a ≤
    centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) from inf_le_right)).trans
    (source_moving_fixed_attachment_eq_bot h d g hb hsat ha).le

/-- The genuine order-q pair now has a commutator of order q in the original
amalgam, before quotienting by either complete fixed core. -/
theorem source_field_critical_commutator_order
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a)=2^n) :
    Nat.card (⁅Z d.radical a,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical))=2^n := by
  have hi := (critical_fixed_layer_index h d path hb hat hzt hcritical).2
  rw [source_moving_fixed_attachment_eq_bot h d g hb hsat path.start_color,
    relIndex_bot_left] at hi
  exact hi

omit h d [Group H] [Finite H] [Field F] [Finite F] [CharP F 2] in
private theorem relIndex_map_of_kernel_in_overlap
    {G J : Type*} [Group G] [Group J] (f : G →* J) (A B : Subgroup G)
    (hk : (A ⊔ B) ⊓ f.ker ≤ A ⊓ B) :
    (B.map f).relIndex (A.map f)=B.relIndex A := by
  rw [←relIndex_comap,comap_map_eq]
  unfold relIndex
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨b,hb,k,hk',he⟩ := mem_sup_of_normal_right.mp hx
    change b*k=x.val at he
    have hkJ : k ∈ A ⊔ B := by
      have hh := (A ⊔ B).mul_mem ((A ⊔ B).inv_mem (mem_sup_right hb))
        (mem_sup_left x.property)
      rw [←he,inv_mul_cancel_left] at hh
      exact hh
    change x.val ∈ B
    exact he ▸ B.mul_mem hb (hk ⟨hkJ,hk'⟩).2
  · intro hx
    exact mem_sup_left hx

private theorem field_critical_overlap_le_Z
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a)=2^n) :
    Z d.radical z ⊓ Q d.radical a ≤ Z d.radical a := by
  obtain ⟨hin,_,hX,_⟩ := source_three_of_field_critical h d g hb hsat path hat hzt c c' hcritical
  have hc : Z d.radical z ⊓ Q d.radical a ≤
      centralizer ((Z d.radical a ⊔ Q d.radical z : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    apply sup_le
    · exact (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a path.start_color)).trans (centralizer_le inf_le_right)
    · exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical z path.end_color))).trans (centralizer_le inf_le_left)
  let := g.Z_elementary (by omega : 0<g.b d.radical) z path.end_color
  intro x hx
  rw [←hX]
  exact mem_omegaCenter_iff.mpr ⟨hx.2,
    elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx.1,
    (hc.trans (centralizer_le hin)) hx⟩

/-- The source overlap index survives the quotient by the entire fixed core.
Its kernel on Z_a Z_z is contained in the actual overlap: its Z_a part lies
in the midpoint center. This supplies SourceEndgame.intersection_index. -/
theorem source_field_critical_quotient_overlap
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a)=2^n) :
    (P1Comparison.layerImage d a (Z d.radical z)).relIndex
      (P1Comparison.layerImage d a (Z d.radical a))=2^n := by
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hZQ : Z d.radical a ≤ Q d.radical a :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0<g.b d.radical; omega)).trans (omegaCenter_le _)
  have hZS : Z d.radical a ≤ stabilizer d.radical a := hZQ.trans (fun _ hx => hx.1)
  have hZzS : Z d.radical z ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  have hover := field_critical_overlap_le_Z h d g hb hsat path hat hzt c c' hcritical
  have hk : ((Z d.radical a ⊔ Z d.radical z) ⊓ fixedCore d.radical a) ≤
      Z d.radical a ⊓ Z d.radical z := by
    intro x hx
    have hn : Z d.radical z ≤ normalizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
      hZzS.trans (Z_normalized d.radical a)
    have hxprod : x ∈ Z d.radical a ⊔ Z d.radical z := hx.1
    rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hn] at hxprod
    obtain ⟨u,hu,v,hv,he⟩ := hxprod
    change u*v=x at he
    have hvQ : v ∈ Q d.radical a := by
      have hh := (Q d.radical a).mul_mem ((Q d.radical a).inv_mem (hZQ hu)) hx.2.1
      rwa [←he,inv_mul_cancel_left] at hh
    have hxZ : x ∈ Z d.radical a := he ▸ (Z d.radical a).mul_mem hu (hover ⟨hv,hvQ⟩)
    have hxX : x ∈ X d.radical a := g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0<g.b d.radical; omega) hxZ
    have hxt : x ∈ Z d.radical t :=
      replacement_fixed_X_le_edge h d (g := g) (by omega) path.start_color hat ⟨hxX,hx.2.2⟩
    exact ⟨hxZ,Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt hxt⟩
  let S := stabilizer d.radical a
  let A := (Z d.radical a).subgroupOf S
  let B := (Z d.radical z).subgroupOf S
  have hk' : (A ⊔ B) ⊓ (P1Comparison.fixedProjection d a).ker ≤ A ⊓ B := by
    rw [show (P1Comparison.fixedProjection d a).ker=P1Comparison.fixedAttachment d a from
      QuotientGroup.ker_mk' _]
    intro x hx
    have hxJ : x.val ∈ Z d.radical a ⊔ Z d.radical z := by
      have he : A ⊔ B=(Z d.radical a ⊔ Z d.radical z).subgroupOf S :=
        (subgroupOf_sup hZS hZzS).symm
      have hh : x ∈ (Z d.radical a ⊔ Z d.radical z).subgroupOf S := he ▸ hx.1
      exact hh
    exact hk ⟨hxJ,hx.2⟩
  change (B.map (P1Comparison.fixedProjection d a)).relIndex
    (A.map (P1Comparison.fixedProjection d a))=2^n
  rw [relIndex_map_of_kernel_in_overlap _ _ _ hk',relIndex_subgroupOf hZS]
  exact (source_three_of_field_critical h d g hb hsat path hat hzt c c' hcritical).2.2.2.1

/-- The actual source pair, its complete fixed core and the two numerical
endgame clauses, with no additional pair-selection or attachment premise. -/
theorem source_field_critical_preparation
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical) :
    ∃ a z t : Vertex d.radical, ∃ _path : CriticalPath d.radical g a z,
      Adjacent d.radical a t ∧ Adjacent d.radical z t ∧
      (Q d.radical z).relIndex (Z d.radical a)=2^n ∧
      Q d.radical a=U d.radical a ⊔ fixedCore d.radical a ∧
      Disjoint (U d.radical a) (fixedCore d.radical a) ∧
      Nat.card (⁅Z d.radical a,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical))=2^n ∧
      (P1Comparison.layerImage d a (Z d.radical z)).relIndex
        (P1Comparison.layerImage d a (Z d.radical a))=2^n := by
  obtain ⟨a,z,⟨path⟩,hcritical⟩ := source_six_exists_field_critical_pair h d g hb hsat
  have hd : (cosetGraph d.radical).dist a z=2 :=
    path.critical.1.trans ((g.distance_constant a path.start_color).trans hb)
  obtain ⟨t,hat,hzt⟩ := exists_common_neighbor_of_dist_two d.radical a z hd
  exact ⟨a,z,t,path,hat,hzt,hcritical,
    source_six_core_decomposition h d g hb hsat path.start_color,
    source_moving_disjoint_fixedCore h d g hb hsat path.start_color,
    source_field_critical_commutator_order h d g hb hsat path hat hzt hcritical,
    source_field_critical_quotient_overlap h d g hb hsat path hat hzt hcritical⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
