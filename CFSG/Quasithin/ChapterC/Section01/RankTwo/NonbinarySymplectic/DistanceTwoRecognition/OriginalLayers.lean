module
public import Theory.Representation.SymplecticFourOrthogonalCover.PointRadicalLayers
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.CenterAction


/-!
# The original radical displacement series

The two-core of the root normalizer moves the entire natural cover onto
the replacement-root centralizer. Its second displacement is therefore the
same overlap as its action on the whole edge center. This identifies the
opposite full fixed kernel with the second original-normalizer displacement
in the unequal-kernel branch.

The literal replacement transport identifies that normalizer core with
R intersect M, using the ORIGINAL odd-index witness. For the intrinsic
core U, [U,R intersect M] = C_U(T), the second displacement has order q
and is disjoint from C_U(K), and the third displacement is trivial. All
fixed attachments and the original field degree are retained. These action
identities do not yet exclude exchanged kernels or prove radical saturation.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7), printed pp.872--877;
the original-radical comparison before the field restriction and the
shared-layer kernel comparison on p.875.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h
open ChapterB.QuasisimpleSource
open Representation Representation.BinaryOffender Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour

/-- The original normalizer moves the complete cover onto its root centralizer. -/
theorem replacement_field_sized_original_first_displacement
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    let S := stabilizer d.radical a
    let T := (Q d.radical t).subgroupOf S
    let B := (normalizer (T : Set S)).pCoreIn 2
    ⁅U d.radical a,B.map S.subtype⁆ =
      U d.radical a ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.start_color
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hCtop : replacementComponent d = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 d.overgroup)
    have hh := congrArg (fun A : Subgroup d.overgroup => A.map q)
      (replacement_inner_of_positive h d g (by omega))
    rw [Subgroup.map_sup,show (pCore 2 d.overgroup).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict (replacementComponent d) (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  have hγker : γ.ker=κ.ker := by
    ext x
    change e.groupEquiv (κC x)=1 ↔ κ x=1
    rw [e.groupEquiv.map_eq_one_iff]
    exact Subtype.ext_iff
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have haq := (replacement_field_sized_edge_factorization h d rev hb hzt hat hsize).1
  have hzq := (replacement_field_sized_edge_factorization h d path hb hat hzt hsize).1
  have hZS : Z d.radical z ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  let δ := κ.comp (inclusion hZS)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZS κ hκQ).trans (hzq.trans hFc.symm)
  obtain ⟨β,hβcard,hβmark,hβ,hβdim,hβquad⟩ := inner_root_actor_of_field_index rev (by omega)
    (MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) z path.end_color)
    h.nonbinary hFc s e he (replacement_component_image_structure h d).2.2.2.2
    j hj hjr δ (fun x v => hconj (inclusion hZS x) v) hδcard (haq.trans hFc.symm)
  let S := stabilizer d.radical a
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hQS : Q d.radical a ≤ S := fun _ hx => hx.1
  have hjoin := (replacement_field_sized_paired_edges h d path hb hat hzt hsize).1
  have hTS : Q d.radical t ≤ S := by rw [←hjoin]; exact sup_le hQS hZS
  let U₀ := (U d.radical a).subgroupOf S
  let T₀ := (Q d.radical t).subgroupOf S
  let jS := j.codRestrict S (fun w => hUS (hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)))
  have hjSr : jS.range=U₀ := by
    ext x
    constructor
    · rintro ⟨w,rfl⟩
      change j w ∈ U d.radical a
      exact hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)
    · intro hx
      obtain ⟨w,hw⟩ := (show x.val ∈ j.range from hjr.symm ▸ hx)
      exact ⟨w,Subtype.ext hw⟩
  have haction (x : S) (w : s.space.toSubmodule) :
      jS (Multiplicative.ofAdd (MovedSection.coverAction s e (γ x) w)) =
        x*jS (Multiplicative.ofAdd w)*x⁻¹ := by
    apply Subtype.ext
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC x))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj x w
  have hγβ (x : Z d.radical z) : γ (inclusion hZS x)=β x := by
    exact (congrArg e.groupEquiv
      (show κC (inclusion hZS x)=e.groupEquiv.symm (β x) from
        Subtype.ext (hβmark x).symm)).trans (e.groupEquiv.apply_symm_apply _)
  have hQker : (Q d.radical a).subgroupOf S = γ.ker := by
    rw [hγker,←hκQ,subgroupOf_map_subtype_eq]
  have hZimage : ((Z d.radical z).subgroupOf S).map γ=β.range := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,hγβ ⟨x.val,hx⟩ |>.symm⟩
    · rintro _ ⟨x,rfl⟩
      exact ⟨inclusion hZS x,x.property,hγβ x⟩
  have hTimage : T₀.map γ=β.range := by
    change ((Q d.radical t).subgroupOf S).map γ=β.range
    rw [←hjoin,subgroupOf_sup hQS hZS,Subgroup.map_sup,hQker,
      show γ.ker.map γ=⊥ from (Subgroup.map_eq_bot_iff _).mpr le_rfl,bot_sup_eq,hZimage]
  let := finite_stabilizer d.radical a
  have hγonto : Function.Surjective γ := by
    intro x
    obtain ⟨y,hy⟩ := hκ (e.groupEquiv.symm x).val
    exact ⟨y,(congrArg e.groupEquiv (Subtype.ext hy)).trans (e.groupEquiv.apply_symm_apply x)⟩
  have hγp : IsPGroup 2 γ.ker := by
    rw [←hQker]
    exact (Q_isPGroup d.radical (replacement_isPGroup h d) (replacement_core_le h d)
      a path.start_color).comap_subtype
  have hγT : γ.ker ≤ T₀ := by
    rw [←hQker]
    intro x hx
    exact (le_sup_left.trans_eq hjoin) hx
  have hh := embedded_root_normalizer_displacement_eq hFc h.nonbinary U₀ T₀
    (MovedSection.coverProjection s e) he jS
    (fun x y hxy => hj (congrArg Subtype.val hxy)) hjSr γ haction hγonto hγp hγT
    (by rw [hTimage]; exact hβcard) (by rw [hTimage]; exact hβdim)
    (by rw [hTimage]; exact hβquad)
  have hm := congrArg (fun A : Subgroup S => A.map S.subtype) hh
  rw [map_commutator,←map_inf_centralizer_of_injective S.subtype S.subtype_injective,
    map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hTS] at hm
  exact hm

/-- Transport the full first displacement to the literal replacement group. -/
theorem replacement_proper_nonsylow_original_first_displacement
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    ⁅⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆,R.subgroupOf d.overgroup⁆ =
      ⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆ ⊓
        centralizer (d.radical : Set d.overgroup) := by
  obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from (R := d.radical) (geometry := g)
    (a := alpha d.radical) rfl
  have hd : (cosetGraph d.radical).dist (alpha d.radical) z = 2 :=
    path.critical.1.trans ((g.distance_constant _ path.start_color).trans hb)
  obtain ⟨t,hat,hzt⟩ := exists_common_neighbor_of_dist_two d.radical (alpha d.radical) z hd
  have hab : Adjacent d.radical (alpha d.radical) (beta d.radical) :=
    (adjacent_iff_exists_common d.radical _ _).mpr ⟨1,Or.inl ⟨rfl,rfl⟩⟩
  obtain ⟨v,hv,hvt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) hab hat
  let f := (MulAut.conj v⁻¹).toMonoidHom.comp (embedM d.radical)
  have hf : Function.Injective f := (MulAut.conj v⁻¹).injective.comp (embedM_injective d.radical)
  have hmT : d.radical.map f=Q d.radical t := by
    dsimp only [f]
    rw [←Subgroup.map_map,←Q_beta,←Q_act,hvt]
  have hmU : (⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆).map f =
      U d.radical (alpha d.radical) := by
    dsimp only [f]
    rw [←Subgroup.map_map,←core_alpha d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_residual h d),
      replacement_core_eq_U_of_distance_two h d g hb rfl,←U_act,hv]
  let S := stabilizer d.radical (alpha d.radical)
  have hfr : f.range=S := by
    dsimp only [f,S]
    rw [MonoidHom.range_comp,show (embedM d.radical).range=stabilizer d.radical (alpha d.radical)
      from (stabilizer_m_base d.radical).symm,←stabilizer_act,hv]
  let fS := f.codRestrict S (fun x => hfr ▸ ⟨x,rfl⟩)
  have hfSi : Function.Injective fS := fun x y he => hf (congrArg Subtype.val he)
  have hfSs : Function.Surjective fS := by
    intro x
    obtain ⟨y,hy⟩ := (show x.val ∈ f.range from hfr.symm ▸ x.property)
    exact ⟨y,Subtype.ext hy⟩
  let e := MulEquiv.ofBijective fS ⟨hfSi,hfSs⟩
  have hTS : Q d.radical t ≤ S := hmT ▸ hfr ▸ map_le_range f d.radical
  have heT : d.radical.map e.toMonoidHom=(Q d.radical t).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [Subgroup.map_map,map_subgroupOf_eq_of_le hTS]
    exact hmT
  have heB : (R.subgroupOf d.overgroup).map e.toMonoidHom=
      (normalizer ((Q d.radical t).subgroupOf S : Set S)).pCoreIn 2 := by
    rw [←replacement_normalizer_core_eq_original_restriction h d g hb hnsyl,
      map_pCoreIn_of_injective 2 _ e.toMonoidHom (show Function.Injective e.toMonoidHom from e.injective),map_equiv_normalizer_eq,heT]
  have hmB : (R.subgroupOf d.overgroup).map f=
      ((normalizer ((Q d.radical t).subgroupOf S : Set S)).pCoreIn 2).map S.subtype := by
    rw [←heB,Subgroup.map_map]
    rfl
  have hh := replacement_field_sized_original_first_displacement h d path hb hat hzt
    (replacement_proper_nonsylow_card h d g hb hnsyl hne)
  apply map_injective hf
  rw [map_commutator,←map_inf_centralizer_of_injective f hf,hmU,hmT,hmB]
  exact hh


/-- The second displacement under the original normalizer is the overlap on
the full edge center, even when the covering kernel is nontrivial. -/
theorem replacement_field_sized_original_second_displacement
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    let S := stabilizer d.radical a
    let B := ((normalizer ((Q d.radical t).subgroupOf S : Set S)).pCoreIn 2).map S.subtype
    ⁅⁅U d.radical a,B⁆,B⁆ =
      ⁅Q d.radical t ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)),B⁆ := by
  dsimp only
  rw [replacement_field_sized_original_first_displacement h d path hb hat hzt hsize]
  exact (replacement_field_sized_shared_center_displacement h d path hb hat hzt hsize
    _ (map_subtype_le _)).symm

/-- In the exchanged-kernel branch, the original normalizer's second
displacement is exactly the complete opposite fixed kernel. -/
theorem replacement_field_sized_unequal_second_displacement
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n)
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    let S := stabilizer d.radical a
    let B := ((normalizer ((Q d.radical t).subgroupOf S : Set S)).pCoreIn 2).map S.subtype
    ⁅⁅U d.radical a,B⁆,B⁆ =
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
  dsimp only
  rw [replacement_field_sized_original_first_displacement h d path hb hat hzt hsize]
  exact (replacement_field_sized_opposite_fixed_eq_overlap h d path hb hat hzt hsize hne).symm

/-- The whole intrinsic core has a strict two-step displacement under the
ORIGINAL radical restricted to the replacement. The second term is the
shared-center overlap; it has order q, retains its entire fixed-kernel
complement, and the third displacement vanishes. -/
theorem original_proper_nonsylow_displacement_layers
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    let U := (blockU K).map K.subtype
    let B := R ⊓ d.overgroup
    let D := ⁅⁅U,B⁆,B⁆
    ⁅U,B⁆ = U ⊓ centralizer (d.ambient : Set H) ∧
      D = ⁅d.ambient ⊓ centralizer (d.ambient : Set H),B⁆ ∧
      Disjoint D (U ⊓ centralizer (K : Set H)) ∧ Nat.card D=2^n ∧
      D ⊔ (U ⊓ centralizer (K : Set H))=⁅U,d.ambient⁆ ∧ ⁅D,B⁆=⊥ := by
  let := h.component_normal
  have hperfect : IsPPerfect 2 K := by
    rw [←h.residual_eq]
    exact isPPerfect_pResidual 2
  have hmU := d.commutatorCore_eq_intrinsic_of_sup (original_sup h) hperfect
  have hmT : d.radical.map d.overgroup.subtype=d.ambient := map_subgroupOf_eq_of_le le_sup_right
  have hfirst := congrArg (fun A : Subgroup d.overgroup => A.map d.overgroup.subtype)
    (replacement_proper_nonsylow_original_first_displacement h d g hb hnsyl hne)
  rw [map_commutator,←map_inf_centralizer_of_injective _ d.overgroup.subtype_injective,
    hmU,hmT,subgroupOf_map_subtype] at hfirst
  have hcenter := congrArg (fun A : Subgroup d.overgroup => A.map d.overgroup.subtype)
    (replacement_field_sized_radical_center_displacement h d g hb
      (replacement_proper_nonsylow_card h d g hb hnsyl hne) (R.subgroupOf d.overgroup))
  rw [map_commutator,map_commutator,
    ←map_inf_centralizer_of_injective _ d.overgroup.subtype_injective,
    ←map_inf_centralizer_of_injective _ d.overgroup.subtype_injective,
    hmU,hmT,subgroupOf_map_subtype] at hcenter
  have hsecond : ⁅⁅(blockU K).map K.subtype,R ⊓ d.overgroup⁆,R ⊓ d.overgroup⁆ =
      ⁅d.ambient ⊓ centralizer (d.ambient : Set H),R ⊓ d.overgroup⁆ := by
    rw [hfirst]
    exact hcenter.symm
  dsimp only
  refine ⟨hfirst,hsecond,?_,?_,?_,?_⟩
  · rw [hsecond]
    exact (original_proper_nonsylow_center_overlap h d g hb hnsyl hne).1
  · rw [hsecond]
    exact (original_proper_nonsylow_center_overlap h d g hb hnsyl hne).2.1
  · rw [hsecond]
    exact (original_proper_nonsylow_center_overlap h d g hb hnsyl hne).2.2.2
  · rw [commutator_comm,commutator_eq_bot_iff_le_centralizer,hsecond]
    exact (original_proper_nonsylow_center_overlap_action h d g hb hnsyl hne).2.trans
      (centralizer_le (fun _ hx => mem_sup_left hx))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
