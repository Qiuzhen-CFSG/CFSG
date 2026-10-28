module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexDisplacement

/-!
# Strict moving index at every nonbinary critical path

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.9), printed pp.920--922.

For a conjugate seed fixing A₀, every nonzero A₀-displacement in its first
orbit span saturates the literal T₀-image. Its whole commutator would then
be the same H₂, contained in U_e and hence fixing Z_e, contrary to the
selected endpoint movement. Thus these remaining spans centralize A₀ and
satisfy the displacement comparison. Together with the previously proved
comparison for moving seeds, this makes the complete second span W normal
in G_c. The simple quotient and nilpotent kernel collapse W to the first
span. Its T₂-displacement is H₂ ≤ Z_c, while T₂ escapes Q_c; simplicity
therefore puts the original selected seed in B_c, a contradiction.

This proves the strict index on the original two-step segment, retaining
the full quotient kernels, natural covers and central attachments at every
nonbinary degree. The argument completes the span comparison directly,
without requiring the intervening R₃-centrality calculation. The later
terminal exclusions and the actual distance-two replacement remain needed;
the separate original-radical characteristic-control gap is unchanged.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open ChapterB.QuasisimpleSource MSCentralOrbit
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four

private theorem quiet_span_centralizes_intersection
    {geometry : Geometry d.radical} {c e nu t : Vertex d.radical}
    (path : CriticalPath d.radical geometry c e) (hb : 4 < geometry.b d.radical)
    (hnu : color d.radical nu=false)
    (hnut : Adjacent d.radical nu t) (hct : Adjacent d.radical c t)
    (hsmall : (B d.radical nu (geometry.Z_normal nu)).relIndex (U d.radical c) ≤ Nat.card F)
    (hi : (Q d.radical e).relIndex (Z d.radical c)=Nat.card F)
    (hYS : sourceSeedSpan d.radical c nu ≤ stabilizer d.radical e)
    (hAT : X d.radical e ⊓ Q d.radical c ≤ kernelCentralizer geometry nu c)
    (hHC : kernelCommutator geometry nu c ≤
      centralizer (stabilizer d.radical nu : Set (FreeAmalgam d.radical)))
    (hmove : ¬ kernelCommutator geometry nu c ≤
      centralizer (Z d.radical e : Set (FreeAmalgam d.radical))) :
    ⁅sourceSeedSpan d.radical c nu,X d.radical e ⊓ Q d.radical c⁆=⊥ := by
  let A := X d.radical e ⊓ Q d.radical c
  let Y := sourceSeedSpan d.radical c nu
  have hroot : (Q d.radical e).relIndex (Z d.radical c) < Nat.card F^2 := by
    rw [hi]; have hq : 1 < Nat.card F := Finite.one_lt_card; nlinarith
  have hCa := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) c path.start_color
  have hUS : U d.radical e ≤ stabilizer d.radical c :=
    (U_le_Z e).trans (path.endpoint_Z_le_start_stabilizer (by omega))
  have hAU : U d.radical e ⊓ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) =
      U d.radical e ⊓ Q d.radical c := by
    rw [←hCa]
    ext x
    exact ⟨fun hx => ⟨hx.1,hUS hx.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩
  let := geometry.Z_elementary (by omega) e path.end_color
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply (closure_le _).mpr
  rintro _ ⟨k,hk,u,hu,rfl⟩
  let c' := act d.radical k⁻¹ c
  let t' := act d.radical k⁻¹ t
  have hknu : act d.radical k⁻¹ nu=nu := (stabilizer d.radical nu).inv_mem hk
  have hnut' : Adjacent d.radical nu t' := by
    have hh := (adjacent_act_iff d.radical k⁻¹ nu t).mpr hnut
    rwa [hknu] at hh
  have hct' : Adjacent d.radical c' t' := (adjacent_act_iff d.radical k⁻¹ c t).mpr hct
  have hc' : color d.radical c'=false := by
    rw [action_preserves_color]; exact path.start_color
  have hd : (cosetGraph d.radical).dist nu c' ≤ 2 :=
    neighbor_distance_le_two hct' hnut'
  have hseed : Z d.radical c' ≤ Y := by
    rw [Z_act]
    rintro _ ⟨v,hv,rfl⟩
    exact subset_closure ⟨k,hk,v,hv,by simp only [inv_inv]; rfl⟩
  have hTS : kernelCentralizer geometry nu c' ≤ stabilizer d.radical c' :=
    inf_le_left.trans (Q_le_stabilizer_of_dist_le_two nu c' hnu hc' hd)
  obtain ⟨hT,hH⟩ := h.replacement_kernel_conjugate_at_edge d geometry (by omega) hnu
    hnut hct k⁻¹ ((stabilizer d.radical nu).inv_mem hk)
  have hHeq : kernelCommutator geometry nu c'=kernelCommutator geometry nu c := by
    rw [hH]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.centralizer_le_normalizer _) (le_centralizer_iff.mp hHC
        (show (k⁻¹)⁻¹ ∈ stabilizer d.radical nu by simpa using hk)))
  have hsmall' : (B d.radical nu (geometry.Z_normal nu)).relIndex (U d.radical c') ≤ Nat.card F := by
    rw [movingIndex_act geometry (by omega) hnu k⁻¹ ((stabilizer d.radical nu).inv_mem hk)]
    exact hsmall
  have hAT' : A ≤ kernelCentralizer geometry nu c' := by rw [hT]; exact hAT
  have hAS := hAT'.trans hTS
  have hzero : ⁅Z d.radical c',A⁆=⊥ := by
    by_contra hn
    have hnonzero : ⁅Z d.radical c',U d.radical e ⊓
        centralizer (Z d.radical c : Set (FreeAmalgam d.radical))⁆ ≠ ⊥ := by
      rw [hAU,←(h.replacement_root_intersection_fixed_and_commutator d path hb.le
        hroot (Z d.radical c') (hseed.trans hYS)).1]
      exact hn
    have hlo := h.replacement_fixed_U_moving_index_lower d geometry hb.le path.end_color
      (Z d.radical c') (Z d.radical c) (hseed.trans hYS)
      (Z_le_stabilizer_of_dist_le c (geometry.exists_critical c path.start_color) path.critical.1.le)
      hnonzero
    rw [hAU] at hlo
    have hUA : U d.radical e ⊓ Q d.radical c ≤ A :=
      inf_le_inf_right _ ((U_le_Z e).trans (geometry.omega_bound e path.end_color (by
        rw [geometry.distance_constant e path.end_color]; change 0 < geometry.b d.radical; omega)))
    let := finite_stabilizer d.radical c'
    let : Finite A := Finite.of_injective (inclusion hAS) (inclusion_injective _)
    have hCn : A ⊓ centralizer (Z d.radical c' : Set (FreeAmalgam d.radical))=A ⊓ Q d.radical c' := by
      rw [←MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
        (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) c' hc']
      ext x
      exact ⟨fun hx => ⟨hx.1,hAS hx.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩
    have hQlo := hlo.trans (relIndex_le_of_le_right hUA index_ne_zero_of_finite)
    rw [←inf_relIndex_left,hCn,inf_relIndex_left] at hQlo
    have he := (h.replacement_field_index_actor_saturates d geometry hb.le hc' A
      (kernelCentralizer geometry nu c') hAT' hTS
      ((kernelCentralizer_moving_index_le geometry nu c').trans hsmall') hQlo).2
    rw [h.replacement_kernel_full_seed_commutator d geometry hb.le hnu hnut' hct',hHeq] at he
    apply hmove
    rw [←he,(h.replacement_root_intersection_fixed_and_commutator d path hb.le
      hroot (Z d.radical c') (hseed.trans hYS)).1,commutator_comm]
    exact ((commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp ((hseed.trans hYS).trans (U_normalized e)))).trans
      ((U_le_Z e).trans (le_centralizer_iff_isMulCommutative.mpr inferInstance))
  apply commutator_eq_bot_iff_le_centralizer.mp hzero
  rw [Z_act]
  exact ⟨u,hu,by simp only [inv_inv]; rfl⟩

/-- MS93 (5.9): the moving index on the original two-step segment is
strictly greater than the original nonbinary field order. -/
theorem Input.replacement_path_moving_index_gt_field
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical) :
    Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) := by
  by_contra! hsmall
  obtain ⟨hi,y,hy,hnotB,hT,hmove,e,selected,hez,hover,hmoveE,hgen,hZW,hWQ,hWp,hWz,
      hic,hie,hbad,hne,hcard,heq,hRU,hnotn,hsize,hcentral,t,ht,htEq,htU,hidx,hQidx,hfixed,
      hYW,hproper,hstrict,hcompare,hmoving,hquiet⟩ :=
    h.replacement_strict_index_selected_displacement_comparison d path hb hsmall
  let c := path.walk.getVert 2
  let mu := act d.radical y a
  let T₂ := (kernelCentralizer geometry a c).map (MulAut.conj y⁻¹).toMonoidHom
  let H₂ := conjugatedKernelCommutator geometry a c y
  let C₀ := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
  let Y := sourceSeedSpan d.radical c mu
  let W := sourceCentralizerSpan d.radical c mu H₂
  let A₀ := X d.radical e ⊓ Q d.radical c
  have hc := selected.start_color
  have hmu : color d.radical mu=false := by
    rw [action_preserves_color]; exact path.start_color
  have hd : (cosetGraph d.radical).dist c mu ≤ 2 := by
    have hh := dist_act d.radical y c a
    rw [show act d.radical y c=c from hy] at hh
    rw [hh,SimpleGraph.dist_comm]
    exact (path.dist_start (by rw [path.length_eq_b]; omega)).le
  have hYS : W ≤ stabilizer d.radical e := hWz.trans
    (Q_le_stabilizer_of_dist_le_two z e path.end_color selected.end_color
      (by rw [SimpleGraph.dist_comm]; exact hez.le))
  have hall (s : FreeAmalgam d.radical) (hs : s ∈ C₀) :
      let Y₁ := sourceSeedSpan d.radical c (act d.radical s mu)
      Y₁ ≤ W ∧ ⁅Y₁,Z d.radical e⁆ ≤ Z d.radical c ⊔ ⁅Y₁,A₀⁆ := by
    dsimp only
    by_cases hm : ⁅Z d.radical (act d.radical s mu),A₀⁆=⊥
    · let nu := act d.radical s mu
      have hnu : color d.radical nu=false := by
        rw [action_preserves_color,action_preserves_color]; exact path.start_color
      have hys : y*s ∈ stabilizer d.radical c := (stabilizer d.radical c).mul_mem hy hs.1
      have hysnu : act d.radical (y*s) a=nu := by rw [act_mul]
      have hHeq : conjugatedKernelCommutator geometry a c (y*s)=H₂ := by
        change (kernelCommutator geometry a c).map (MulAut.conj (y*s)⁻¹).toMonoidHom=H₂
        have he : (MulAut.conj (y*s)⁻¹).toMonoidHom=
            (MulAut.conj s⁻¹).toMonoidHom.comp (MulAut.conj y⁻¹).toMonoidHom := by
          apply MonoidHom.ext
          intro x
          change (y*s)⁻¹*x*((y*s)⁻¹)⁻¹=s⁻¹*(y⁻¹*x*(y⁻¹)⁻¹)*(s⁻¹)⁻¹
          group
        rw [he,←map_map]
        exact mem_normalizer_iff_map_conj_eq.mp
          ((Subgroup.centralizer_le_normalizer _) (C₀.inv_mem hs).2)
      obtain ⟨_,hHnu,_,_,_,_,_,_,_,hHcent⟩ :=
        h.replacement_strict_index_conjugated_span d path hb hsmall (y*s) hys
      rw [hysnu,hHeq] at hHnu hHcent
      have hBi : (B d.radical nu (geometry.Z_normal nu)).relIndex (U d.radical c) ≤ Nat.card F := by
        have hh := relIndex_map_map_of_injective (f := (MulAut.conj (y*s)⁻¹).toMonoidHom)
          (B d.radical a (geometry.Z_normal a)) (U d.radical c) (MulAut.conj (y*s)⁻¹).injective
        rw [←Escape.PairingControl.FirstPairing.B_act (by omega) (y*s) a path.start_color,
          ←U_act,show act d.radical (y*s) c=c from hys,hysnu] at hh
        exact hh.le.trans hsmall
      have hmap : Y.map (MulAut.conj s⁻¹).toMonoidHom=sourceSeedSpan d.radical c nu := by
        change (conjugateSpanBy _ _).map _=conjugateSpanBy _ _
        rw [map_conjugateSpanBy,←Z_act,←stabilizer_act,show act d.radical s c=c from hs.1]
      have hYW : sourceSeedSpan d.radical c nu ≤ W := by
        rw [←hmap]
        rintro _ ⟨v,hv,rfl⟩
        exact subset_closure ⟨s⁻¹,C₀.inv_mem hs,v,hv,rfl⟩
      have hat : Adjacent d.radical a (path.walk.getVert 1) := by
        have hh := (cosetGraph_adj d.radical _ _).mp
          (path.walk.adj_getVert_succ (i := 0) (by rw [path.length_eq_b]; omega))
        simpa only [SimpleGraph.Walk.getVert_zero] using hh
      have hct : Adjacent d.radical c (path.walk.getVert 1) :=
        adjacent_symm _ ((cosetGraph_adj d.radical _ _).mp
          (path.walk.adj_getVert_succ (i := 1) (by rw [path.length_eq_b]; omega)))
      have hnut : Adjacent d.radical nu (act d.radical (y*s) (path.walk.getVert 1)) := by
        rw [←hysnu]
        exact (adjacent_act_iff d.radical (y*s) _ _).mpr hat
      have hct' : Adjacent d.radical c (act d.radical (y*s) (path.walk.getVert 1)) := by
        have hh := (adjacent_act_iff d.radical (y*s) _ _).mpr hct
        rwa [show act d.radical (y*s) c=c from hys] at hh
      have hz := quiet_span_centralizes_intersection h d selected hb hnu hnut hct' hBi hic
        (hYW.trans hYS) (hquiet s hs hm).1 (hHnu ▸ hHcent) (hHnu ▸ hmoveE)
      have hYQ := hYW.trans hWQ
      have hZX : Z d.radical e ≤ X d.radical e := geometry.omega_bound e selected.end_color (by
        rw [geometry.distance_constant e selected.end_color]; change 0 < geometry.b d.radical; omega)
      have hYZ : ⁅sourceSeedSpan d.radical c nu,Z d.radical e⁆ ≤ Z d.radical c := by
        rw [commutator_comm]
        exact (h.replacement_critical_fixed_intersection_displacement d selected (by omega)
          _ (hYW.trans hYS) hYQ
          ((commutator_eq_bot_iff_le_centralizer.mp hz).trans
            (centralizer_le (inf_le_inf_right _ hZX)))).trans (critical_commutator_le_start_seed selected)
      exact ⟨hYW,hYZ.trans le_sup_left⟩
    · obtain ⟨_,hYW,_,_,hcompare⟩ := hmoving s hs hm
      exact ⟨hYW,hcompare⟩
  have hQY : Q d.radical c ≤ normalizer (Y : Set _) :=
    sourceSeedSpan_normalized_by_kernel hc hmu hd
  have hQW : Q d.radical c ≤ normalizer (W : Set _) :=
    TwoOrbitSpan.normalizes_span Y C₀ (Q d.radical c) hQY
      (inf_le_left.trans (Q_normalized d.radical c))
  have hZcY : Z d.radical c ≤ Y := le_conjugateSpanBy _ _
  have hZcW : Z d.radical c ≤ W := hZcY.trans (le_conjugateSpanBy _ _)
  let D := ⁅W,Q d.radical c⁆ ⊔ Z d.radical c
  have hQD : Q d.radical c ≤ normalizer (D : Set _) := by
    intro q hq
    rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_sup,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hQW hq),
      mem_normalizer_iff_map_conj_eq.mp ((Q d.radical c).le_normalizer hq),
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical c hq.1)]
  have hWD : ⁅W,Z d.radical e⁆ ≤ D := by
    rw [show W=⨆ g : C₀,Y.map (MulAut.conj (g : FreeAmalgam d.radical)).toMonoidHom from
      conjugateSpanBy_eq_iSup_conj Y C₀]
    apply commutator_iSup_le_of_relative_normal (Q d.radical c) (Z d.radical e) D _ hQD
    · intro g
      have hg := hall (g : FreeAmalgam d.radical)⁻¹ (C₀.inv_mem g.property)
      have hm : Y.map (MulAut.conj (g : FreeAmalgam d.radical)).toMonoidHom=
          sourceSeedSpan d.radical c (act d.radical (g : FreeAmalgam d.radical)⁻¹ mu) := by
        change (conjugateSpanBy _ _).map _=conjugateSpanBy _ _
        rw [map_conjugateSpanBy,←inv_inv (g : FreeAmalgam d.radical),←Z_act,←stabilizer_act]
        rw [inv_inv,show act d.radical (g : FreeAmalgam d.radical)⁻¹ c=c from
          (stabilizer d.radical c).inv_mem g.property.1]
      rw [hm]
      exact hg.1.trans hWQ
    · intro g
      have hg := hall (g : FreeAmalgam d.radical)⁻¹ (C₀.inv_mem g.property)
      have hm : Y.map (MulAut.conj (g : FreeAmalgam d.radical)).toMonoidHom=
          sourceSeedSpan d.radical c (act d.radical (g : FreeAmalgam d.radical)⁻¹ mu) := by
        change (conjugateSpanBy _ _).map _=conjugateSpanBy _ _
        rw [map_conjugateSpanBy,←inv_inv (g : FreeAmalgam d.radical),←Z_act,←stabilizer_act]
        rw [inv_inv,show act d.radical (g : FreeAmalgam d.radical)⁻¹ c=c from
          (stabilizer d.radical c).inv_mem g.property.1]
      rw [hm]
      exact hg.2.trans (sup_le le_sup_right
        ((commutator_mono hg.1 inf_le_right).trans le_sup_left))
  have hDW : D ≤ W := sup_le (le_normalizer_iff_commutator_le_left.mp hQW) hZcW
  have hSW : stabilizer d.radical c ≤ normalizer (W : Set _) := by
    rw [←hgen]
    exact sup_le (le_normalizer_conjugateSpanBy _ _)
      (le_normalizer_iff_commutator_le_left.mpr (hWD.trans hDW))
  have hQcS : Q d.radical c ≤ stabilizer d.radical c := fun _ hx => hx.1
  have hWS := hWQ.trans hQcS
  obtain ⟨E,hE,f,hf,hfQ,_⟩ := h.replacement_inner_natural_action d geometry hb.le hc
  have hlarge : 3 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 3 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup hlarge
  let : IsSimpleGroup (Sp E.Carrier) :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
  have hk : f.ker=(Q d.radical c).subgroupOf (stabilizer d.radical c) := by
    apply map_injective (stabilizer d.radical c).subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hQcS]
  have hp := Q_isPGroup d.radical (h.replacement_two_group d) (h.replacement_core_le d) c hc
  have hresidual (D T : Subgroup (FreeAmalgam d.radical))
      (hn : stabilizer d.radical c ≤ normalizer (D : Set _))
      (hTS : T ≤ stabilizer d.radical c) (hTQ : ¬ T ≤ Q d.radical c)
      (hcomm : ⁅W,T⁆ ≤ D) : ⁅W,Ltilde d.radical c⁆ ≤ D := by
    let S := stabilizer d.radical c
    let W₀ := W.subgroupOf S
    let D₀ := D.subgroupOf S
    let T₀ := T.subgroupOf S
    let : W₀.Normal := normal_subgroupOf_of_le_normalizer hSW
    let : D₀.Normal := normal_subgroupOf_of_le_normalizer hn
    have hp' : IsPGroup 2 f.ker := by rw [hk]; exact hp.comap_subtype
    have hnot : ¬ T₀ ≤ f.ker := by
      intro hh
      apply hTQ
      intro t ht
      have hh' := hh (show (⟨t,hTS ht⟩ : S) ∈ T₀ from ht)
      rwa [hk] at hh'
    have hcomm' : ⁅W₀,T₀⁆ ≤ D₀ := commutator_le.mpr fun _ hw _ ht =>
      hcomm (commutator_mem_commutator hw ht)
    have hh := map_mono (f := S.subtype)
      (commutator_pResidual_le_of_simple_kernel_escape 2 f hf hp' W₀ D₀ T₀ hnot hcomm')
    rw [map_commutator,map_subgroupOf_eq_of_le hWS] at hh
    exact hh.trans (map_comap_le _ _)
  have hSD : stabilizer d.radical c ≤ normalizer (D : Set _) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_sup,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hSW hg),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical c hg),
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical c hg)]
  have heQ : ¬ Z d.radical e ≤ Q d.radical c := by
    intro hh
    have he := relIndex_eq_one.mpr hh
    rw [hie] at he
    exact (ne_of_gt (Finite.one_lt_card (α := F))) he
  have hWL := hresidual D (Z d.radical e) hSD
    (selected.endpoint_Z_le_start_stabilizer (by omega)) heQ hWD
  have hlocal : Ltilde d.radical c ⊔ Q d.radical c=stabilizer d.radical c := by
    obtain ⟨i,hinj,hir,hiL,hiU,hiQ⟩ := Sp4Four.SourceComparison.vertex_coordinates_with_kernel d.radical
      (h.replacement_two_group d) (h.replacement_core_le d) hc
    rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
      h.replacement_inner_of_four_le d geometry hb.le,←MonoidHom.range_eq_map,hir]
  let := finite_stabilizer d.radical c
  let : Finite (Q d.radical c) := Finite.of_injective (inclusion hQcS) (inclusion_injective _)
  have hcollapse : W=Y := conjugateSpanBy_eq_of_nilpotent_local_generation Y C₀
    (Q d.radical c) (Z d.radical c) (Ltilde d.radical c) (stabilizer d.radical c)
    hp.isNilpotent hWQ hQY hZcY inf_le_left hlocal hSW
    (Q_normalized d.radical c) (Z_normalized d.radical c) hWL
  obtain ⟨_,_,_,hZmuY,_,_,_,hdisp,hH₂Z,_⟩ :=
    h.replacement_strict_index_conjugated_span d path hb hsmall y hy
  have hWT : ⁅W,T₂⁆ ≤ Z d.radical c := by rw [hcollapse,hdisp]; exact hH₂Z
  have hfinal := hresidual (Z d.radical c) T₂ (Z_normalized d.radical c)
    (kernelCentralizer_conjugate_le_stabilizer geometry path (by omega) y hy) hT hWT
  have hZmuV : Z d.radical mu ≤ V d.radical c :=
    le_iSup_of_le _ (le_iSup_of_le (by rwa [SimpleGraph.dist_comm] : (cosetGraph d.radical).dist mu c ≤ 2) le_rfl)
  apply hnotB
  exact radius_le_B_of_commutator geometry (by omega) hc (Z d.radical mu) hZmuV
    ((commutator_mono (hZmuY.trans (le_conjugateSpanBy _ _)) le_rfl).trans hfinal)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
