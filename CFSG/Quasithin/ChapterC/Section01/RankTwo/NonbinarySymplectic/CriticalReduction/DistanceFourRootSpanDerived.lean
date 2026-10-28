module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootSpanNatural
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusFixedCentrality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.InnerAction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedCover
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.Commutator.GeneratedCoreLifts
public import Theory.SpecificGroups.SymplecticFour.NaturalSmallIndexGeneral

/-!
# Derived groups of the native root-offender span

For the literal midpoint span W, retain its native residual commutator
P=[W,L_a]. The same full-kernel coordinates identify its image with the
moved space. Natural recognition and zero fixed space give a central
natural quotient of P. The original fixed-radius hypothesis fixes P'
pointwise, so the derived order is at most the original field order and
every literal intersection of index at most that order retains P'.

The vertex stabilizer decomposition gives W=P Z_e and W'=P'. No equality
of P with the full moved radius or the residual commutator of Q_a is used.
Source: MS93 (3.10)(i), printed p.880, in the root branch of (5.12).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative commutatorElement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
private theorem root_span_movement_normalized
    {M : Type*} [Group M] (R : Subgroup M) (a e : Vertex R) :
    stabilizer R a ≤ normalizer
      ((⁅localZSpan R e a,Ltilde R a⁆ : Subgroup (FreeAmalgam R)) : Set _) := by
  have hSL : stabilizer R a ≤ normalizer (Ltilde R a : Set (FreeAmalgam R)) := by
    have hh := le_normalizer_map (H := pResidual 2 (stabilizer R a))
      (stabilizer R a).subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (localZSpan_normalized R e a hg),
    mem_normalizer_iff_map_conj_eq.mp (hSL hg)]

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

omit [Finite F] [CharP F 2] in
private theorem root_span_movement_idempotent
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4) :
    ⁅⁅localZSpan d.radical (path.walk.getVert 2) a,Ltilde d.radical a⁆,
      Ltilde d.radical a⁆ =
      ⁅localZSpan d.radical (path.walk.getVert 2) a,Ltilde d.radical a⁆ := by
  let S := stabilizer d.radical a
  let W := localZSpan d.radical (path.walk.getVert 2) a
  let A := W.subgroupOf S
  let := finite_stabilizer d.radical a
  have hl := path.length_eq_b
  have hWV : W ≤ V d.radical a := localZSpan_le_V d.radical (by
    rw [SimpleGraph.dist_comm,path.dist_start (by omega)])
  have hVQ := geometry.V_le_Q (by omega : 2 < geometry.b d.radical) a path.start_color
  have hWS : W ≤ S := hWV.trans (hVQ.trans (fun _ hx => hx.1))
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (localZSpan_normalized d.radical (path.walk.getVert 2) a)
  have hp : IsPGroup 2 A :=
    ((Q_isPGroup d.radical (h.replacement_two_group d) (h.replacement_core_le d)
      a path.start_color).to_le (hWV.trans hVQ)).comap_subtype
  have hid := congrArg (Subgroup.map S.subtype)
    (commutator_isPPerfect_idempotent (pResidual 2 S) A (isPPerfect_pResidual 2)
      hp le_normalizer_of_normal)
  have hAm : A.map S.subtype=W := map_subgroupOf_eq_of_le hWS
  simpa only [map_commutator,hAm,Ltilde] using hid

private theorem root_span_eq_movement_sup_seed
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4) :
    localZSpan d.radical (path.walk.getVert 2) a =
      ⁅localZSpan d.radical (path.walk.getVert 2) a,Ltilde d.radical a⁆ ⊔
        Z d.radical (path.walk.getVert 2) := by
  let e := path.walk.getVert 2
  let W := localZSpan d.radical e a
  let P := ⁅W,Ltilde d.radical a⁆
  let J := P ⊔ Z d.radical e
  have hl := path.length_eq_b
  have hd : (cosetGraph d.radical).dist a e=2 := path.dist_start (by omega)
  have hPW : P ≤ W := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (localZSpan_normalized d.radical e a))
  have hZW : Z d.radical e ≤ W := Z_le_localZSpan d.radical e a
  have hJW : J ≤ W := sup_le hPW hZW
  have hSP : stabilizer d.radical a ≤ normalizer (P : Set (FreeAmalgam d.radical)) :=
    root_span_movement_normalized d.radical a e
  have hLJ : Ltilde d.radical a ≤ normalizer (J : Set (FreeAmalgam d.radical)) := by
    apply le_normalizer_iff.mpr
    intro l hl j hj
    have hc : ⁅l,j⁆ ∈ P := by
      change ⁅l,j⁆ ∈ ⁅W,Ltilde d.radical a⁆
      rw [commutator_comm]
      exact commutator_mem_commutator hl (hJW hj)
    have hh := J.mul_mem (mem_sup_left hc) hj
    simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hh
  have hQJ : Q d.radical a ≤ normalizer (J : Set (FreeAmalgam d.radical)) :=
    (le_inf
      ((show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1).trans hSP)
      ((Q_le_stabilizer_of_dist_two d.radical a e path.start_color hd).trans
        (Z_normalized d.radical e))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ := vertex_coordinates_with_kernel d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) path.start_color
  have hS : Ltilde d.radical a ⊔ Q d.radical a=stabilizer d.radical a := by
    rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
      h.replacement_inner_of_four_le d geometry (by omega),←MonoidHom.range_eq_map,hir]
  have hSJ : stabilizer d.radical a ≤ normalizer (J : Set (FreeAmalgam d.radical)) :=
    hS ▸ sup_le hLJ hQJ
  apply le_antisymm _ hJW
  apply iSup_le
  intro g
  rw [Z_act]
  exact (map_mono (show Z d.radical e ≤ J from le_sup_right)).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp (hSJ ((stabilizer d.radical a).inv_mem g.property)))

private theorem root_span_derived_eq_movement_derived
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    ⁅localZSpan d.radical (path.walk.getVert 2) a,localZSpan d.radical (path.walk.getVert 2) a⁆ =
      ⁅⁅localZSpan d.radical (path.walk.getVert 2) a,Ltilde d.radical a⁆,
        ⁅localZSpan d.radical (path.walk.getVert 2) a,Ltilde d.radical a⁆⁆ := by
  let e := path.walk.getVert 2
  let W := localZSpan d.radical e a
  let P := ⁅W,Ltilde d.radical a⁆
  let A := Z d.radical e
  let C := ⁅P,P⁆
  have hl := path.length_eq_b
  have hWV : W ≤ V d.radical a := localZSpan_le_V d.radical (by
    rw [SimpleGraph.dist_comm,path.dist_start (by omega)])
  have hAW : A ≤ W := Z_le_localZSpan d.radical e a
  have hPW : P ≤ W := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (localZSpan_normalized d.radical e a))
  have hVQ := geometry.V_le_Q (by omega : 2 < geometry.b d.radical) a path.start_color
  have hWS : W ≤ stabilizer d.radical a := hWV.trans (hVQ.trans (fun _ hx => hx.1))
  have hSP : stabilizer d.radical a ≤ normalizer (P : Set (FreeAmalgam d.radical)) :=
    root_span_movement_normalized d.radical a e
  have hAC : ⁅A,P⁆ ≤ C := by
    apply commutator_le_derived_of_generated_core P (Ltilde d.radical a) A
      (fixedCore d.radical a) (root_span_movement_idempotent h d path hb)
      ((Ltilde_le_stabilizer a).trans hSP) (hAW.trans (hWS.trans hSP))
    · exact commutator_mono hAW le_rfl
    · rw [commutator_eq_bot_iff_le_centralizer.mpr
        (show fixedCore d.radical a ≤ centralizer (Ltilde d.radical a : Set _) from inf_le_right)]
      exact bot_le
    · exact (commutator_mono (hAW.trans hWV) (hPW.trans (hWV.trans hVQ))).trans hfixed
  have hWC : W ≤ normalizer (C : Set (FreeAmalgam d.radical)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hSP (hWS hg))]
  have hsplit : W=P ⊔ A := root_span_eq_movement_sup_seed h d path hb
  have hAP : ⁅A,W⁆ ≤ C := by
    rw [commutator_comm,hsplit]
    apply commutator_sup_le_of_relative_normal W P A A C hWC hPW hAW
      ((commutator_comm P A).le.trans hAC)
    let := geometry.Z_elementary (by omega) e
      ((path.vertex_color (by omega)).mpr (by decide))
    exact (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer A)).le.trans bot_le
  have hPP : ⁅P,W⁆ ≤ C := by
    rw [commutator_comm,hsplit]
    exact commutator_sup_le_of_relative_normal W P A P C hWC hPW hAW le_rfl hAC
  apply le_antisymm _ (commutator_mono hPW hPW)
  conv_lhs => lhs; rw [hsplit]
  exact commutator_sup_le_of_relative_normal W P A W C hWC hPW hAW hPP hAP

omit [Finite F] [CharP F 2] in
private theorem root_span_moved_image
    (geometry : Geometry d.radical) (a e : Vertex d.radical)
    (E : BinaryField) (hE : E.degree=n)
    (f : stabilizer d.radical a →* Sp E.Carrier) (hf : Function.Surjective f)
    {V₀ : Type*} [AddCommGroup V₀] [Module (ZMod 2) V₀]
    (σ : Representation (ZMod 2) (Sp E.Carrier) V₀)
    (c : BinaryConjugationSection (stabilizer d.radical a)
      (localZSpan d.radical e a)
      (localZSpan d.radical e a ⊓ B d.radical a (geometry.Z_normal a)) (σ.comp f)) :
    c.imageSpace ⁅localZSpan d.radical e a,Ltilde d.radical a⁆ =
      subspaceCommutator σ ⊤ ⊤ := by
  let := finite_stabilizer d.radical a
  have hcard : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let : Group.IsPerfect (Sp E.Carrier) := perfect_of_card_gt_two hcard
  have hmap : ((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map f = ⊤ := by
    have he : (Ltilde d.radical a).subgroupOf (stabilizer d.radical a) =
        pResidual 2 (stabilizer d.radical a) :=
      comap_map_eq_self_of_injective (stabilizer d.radical a).subtype_injective _
    rw [he,map_pResidual_of_surjective 2 f hf,pResidual_eq_top_of_isPerfect 2]
  rw [commutator_comm,c.imageSpace_commutator _ _ (Ltilde_le_stabilizer a) le_rfl,
    c.imageSpace_self,subspaceCommutator_comp_map,hmap]

omit [Finite F] [CharP F 2] in
private theorem derived_facts_from_same_root_span
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hnat : distanceFourRootSpanNatural geometry a (path.walk.getVert 2) z n) :
    let P := ⁅localZSpan d.radical (path.walk.getVert 2) a,Ltilde d.radical a⁆
    Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) ≤ Nat.card F ∧
      ∀ Y : Subgroup (FreeAmalgam d.radical), (Y.subgroupOf P).index ≤ Nat.card F →
        ⁅P ⊓ Y,P ⊓ Y⁆ = ⁅P,P⁆ := by
  obtain ⟨E,hE,f,hf,hfQ,hD,hdata⟩ := hnat
  let := hD
  obtain ⟨hEA,hdata⟩ := hdata
  let := hEA
  obtain ⟨σ,hfaith,c,hcoord,hactor,hzero,hIrr,Eₙ,hEₙ,⟨eₙ⟩⟩ := hdata
  let W := localZSpan d.radical (path.walk.getVert 2) a
  let P := ⁅W,Ltilde d.radical a⁆
  let L := Ltilde d.radical a
  let S := stabilizer d.radical a
  let s := MovedSection.ofNormal σ (⊤ : Subgroup (Sp E.Carrier))
  have hb2 : 2 < geometry.b d.radical := by omega
  have hl := path.length_eq_b
  have hWV : W ≤ V d.radical a := localZSpan_le_V d.radical (by
    rw [SimpleGraph.dist_comm,path.dist_start (by omega)])
  have hPW : P ≤ W := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (localZSpan_normalized d.radical _ a))
  have hm : c.imageSpace P=s.space.toSubmodule :=
    (root_span_moved_image h d geometry a (path.walk.getVert 2) E hE f hf σ c).trans
      s.space_eq.symm
  let κ : P →* Multiplicative s.space.toSubmodule := {
    toFun v := Multiplicative.ofAdd ⟨(c.coordinates (inclusion hPW v)).toAdd,by
      rw [←hm]
      exact (c.mem_imageSpace_iff P _).mpr ⟨inclusion hPW v,v.property,rfl⟩⟩
    map_one' := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd c.coordinates.map_one
    map_mul' v w := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd (c.coordinates.map_mul (inclusion hPW v) (inclusion hPW w)) }
  have hκ : Function.Surjective κ := by
    intro v
    have hv : v.toAdd.val ∈ c.imageSpace P := hm.symm ▸ v.toAdd.property
    obtain ⟨w,hw,he⟩ := (c.mem_imageSpace_iff P v.toAdd.val).mp hv
    refine ⟨⟨w,hw⟩,?_⟩
    apply Multiplicative.toAdd.injective
    exact Subtype.ext he
  let p : s.space.toSubmodule →ₗ[ZMod 2] Vector Eₙ.Carrier :=
    eₙ.linearEquiv.toLinearMap.comp s.central.toSubmodule.mkQ
  have hp : Function.Surjective p :=
    eₙ.linearEquiv.surjective.comp (Submodule.mkQ_surjective s.central.toSubmodule)
  have hpk (v : s.space.toSubmodule) (hv : p v=0) : v.val=0 := by
    change eₙ.linearEquiv (s.central.toSubmodule.mkQ v)=0 at hv
    have hz : s.central.toSubmodule.mkQ v=0 :=
      eₙ.linearEquiv.injective (hv.trans eₙ.linearEquiv.map_zero.symm)
    have hmem := (Submodule.Quotient.mk_eq_zero s.central.toSubmodule).mp hz
    rw [s.central_eq] at hmem
    have hvfix : v.val ∈ fixedSpace σ ⊤ := by
      intro g
      exact congrArg Subtype.val (hmem g)
    simpa only [hzero,Submodule.mem_bot] using hvfix
  let q : P →* Multiplicative (Vector Eₙ.Carrier) := p.toAddMonoidHom.toMultiplicative.comp κ
  have hq : Function.Surjective q := by
    intro v
    obtain ⟨w,hw⟩ := hp v.toAdd
    obtain ⟨v₀,hv₀⟩ := hκ (Multiplicative.ofAdd w)
    refine ⟨v₀,Multiplicative.toAdd.injective ?_⟩
    change p (κ v₀).toAdd=v.toAdd
    rw [hv₀]
    exact hw
  have hBP : B d.radical a (geometry.Z_normal a) ≤ centralizer (P : Set (FreeAmalgam d.radical)) :=
    commutator_eq_bot_iff_le_centralizer.mp (by
      rw [commutator_comm]
      apply le_bot_iff.mp
      exact (commutator_mono (commutator_mono hWV le_rfl) le_rfl).trans_eq
        (radius_moving_centralizes_full_B geometry hb2 path.start_color hfixed))
  have hk : q.ker ≤ center P := by
    intro v hv
    have hvzero : (c.coordinates (inclusion hPW v)).toAdd=0 := hpk (κ v).toAdd hv
    have hvB := ((c.coordinates_eq_one_iff (inclusion hPW v)).mp hvzero).2
    apply mem_center_iff.mpr
    intro w
    exact Subtype.ext (hBP hvB w w.property)
  have hLP : L ≤ normalizer (P : Set (FreeAmalgam d.radical)) :=
    normalizer_commutator_ge_right W L
  let α : L →* MulAut P := P.normalizerMonoidHom.comp (inclusion hLP)
  have hLS : L ≤ S := Ltilde_le_stabilizer a
  let fL : L →* Sp E.Carrier := f.comp (inclusion hLS)
  let := finite_stabilizer d.radical a
  have hcard : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let : Group.IsPerfect (Sp E.Carrier) := perfect_of_card_gt_two hcard
  have hmap : (L.subgroupOf S).map f=⊤ := by
    have he : L.subgroupOf S=pResidual 2 S :=
      comap_map_eq_self_of_injective S.subtype_injective _
    rw [he,map_pResidual_of_surjective 2 f hf,pResidual_eq_top_of_isPerfect 2]
  have hfL : Function.Surjective fL := by
    intro x
    obtain ⟨l,hl,he⟩ := (show x ∈ (L.subgroupOf S).map f from hmap.symm ▸ mem_top x)
    exact ⟨⟨l,hl⟩,he⟩
  let π : L →* Sp Eₙ.Carrier :=
    eₙ.groupEquiv.toMonoidHom.comp (topEquiv.symm.toMonoidHom.comp fL)
  have hπ : Function.Surjective π :=
    eₙ.groupEquiv.surjective.comp (topEquiv.symm.surjective.comp hfL)
  have heq (l : L) (v : P) : (q (α l v)).toAdd=π l • (q v).toAdd := by
    have he : (κ (α l v)).toAdd=s.space.toRepresentation (fL l) (κ v).toAdd := by
      apply Subtype.ext
      exact c.equivariant (inclusion hLS l) (inclusion hPW v)
    change p (κ (α l v)).toAdd=π l • p (κ v).toAdd
    exact (congrArg p he).trans
      (eₙ.intertwines (topEquiv.symm (fL l)) (s.central.toSubmodule.mkQ (κ v).toAdd))
  have hPV : P ≤ V d.radical a := hPW.trans hWV
  have hder : ⁅P,P⁆ ≤ fixedCore d.radical a :=
    (commutator_mono hPV (hPV.trans (geometry.V_le_Q hb2 a path.start_color))).trans hfixed
  have hfix (l : L) (v : P) (hv : v ∈ _root_.commutator P) : α l v=v := by
    have hv' : (v : FreeAmalgam d.radical) ∈ ⁅P,P⁆ := by
      rw [←map_subtype_commutator]
      exact mem_map_of_mem P.subtype hv
    apply Subtype.ext
    change (l : FreeAmalgam d.radical)*(v : FreeAmalgam d.radical)*(l : FreeAmalgam d.radical)⁻¹=v
    rw [(hder hv').2 l l.property,mul_inv_cancel_right]
  have hc : _root_.commutator P ≤ center P := (Abelianization.commutator_subset_ker q).trans hk
  have hbound := Subgroup.ClassTwo.card_commutator_le_of_symplectic_section
    hc α π hπ q hq hk heq hfix
  have hPS : P ≤ S := hPV.trans
    ((geometry.V_le_Q hb2 a path.start_color).trans (fun _ hx => hx.1))
  let : Finite P := Finite.of_injective (inclusion hPS) (inclusion_injective _)
  refine ⟨?_,?_⟩
  · rw [←map_subtype_commutator,card_map_of_injective P.subtype_injective]
    simpa only [Eₙ.card_eq,hEₙ,h.field_card] using hbound
  · intro Y hi
    have hi' : (Y.subgroupOf P).index ≤ Nat.card Eₙ.Carrier := by
      simpa only [Eₙ.card_eq,hEₙ,←h.field_card] using hi
    have he := Subgroup.ClassTwo.derived_eq_of_symplectic_section_index_le_field
      hc α π hπ q hq hk heq hfix (Y.subgroupOf P) hi'
    have hm := congrArg (Subgroup.map P.subtype) he
    have hYM : (Y.subgroupOf P).map P.subtype=P ⊓ Y := by
      rw [subgroupOf_map_subtype,inf_comm]
    rw [map_commutator,hYM,map_subtype_commutator] at hm
    exact hm

/-- In the actual root-offender branch, the original midpoint span has the
same derived subgroup as its native residual commutator. Its order is at most
the original field size, and every literal intersection of index at most
that size retains this entire derived subgroup. -/
theorem Input.replacement_distance_four_root_span_derived
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (path.walk.getVert 2))
    (hga : act d.radical g a=z)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hfirst : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F)
    (hlast : (B d.radical (path.walk.getVert 2) (geometry.Z_normal _)).relIndex
      (U d.radical z) ≤ Nat.card F) :
    let W := localZSpan d.radical (path.walk.getVert 2) a
    let P := ⁅W,Ltilde d.radical a⁆
    W=P ⊔ Z d.radical (path.walk.getVert 2) ∧
      ⁅W,W⁆=⁅P,P⁆ ∧ Nat.card (⁅W,W⁆ : Subgroup (FreeAmalgam d.radical)) ≤ Nat.card F ∧
      ∀ Y : Subgroup (FreeAmalgam d.radical), (Y.subgroupOf P).index ≤ Nat.card F →
        ⁅P ⊓ Y,P ⊓ Y⁆=⁅W,W⁆ := by
  have hnat := h.replacement_distance_four_root_span_natural d path hb g hg hga
    hfixed hfirst hlast
  obtain ⟨hbound,hindex⟩ := derived_facts_from_same_root_span h d path hb hfixed hnat
  have hsplit := root_span_eq_movement_sup_seed h d path hb
  have hderived := root_span_derived_eq_movement_derived h d path hb hfixed
  refine ⟨hsplit,hderived,?_,?_⟩
  · rwa [hderived]
  · intro Y hi
    exact (hindex Y hi).trans hderived.symm

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
