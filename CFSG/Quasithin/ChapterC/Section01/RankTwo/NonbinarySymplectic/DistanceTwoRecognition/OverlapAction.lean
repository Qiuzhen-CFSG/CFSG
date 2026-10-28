module
public import Theory.Representation.SymplecticFourOrthogonalCover.RootOverlap
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.OriginalAction

/-!
# The original radical selects a complement in the full displacement

In the field-sized branch the edge image is a long root on the natural
cover. Its full normalizer two-core acts on the root-fixed hyperplane with
a displacement of order q, disjoint from the entire component-fixed kernel.
Both lie in the common critical displacement. Its known index q over that
kernel therefore makes their product the whole displacement.

The normalizer core is transported through the actual free-amalgam embedding
and identified with the ORIGINAL radical restricted to the replacement,
using the original odd-index witness. In the original group, with
U = [O_2(K),K] and T the characteristic replacement, the subgroup
D = [C_U(T), R intersect M] has order q, meets C_U(K) trivially and satisfies
[U,T] = D C_U(K). The full fixed layer and the original field degree remain.

This supplies additional original-radical action for the fixed-kernel
comparison in MS93 (3.7)(4), printed p.875. Identifying the paired maximal
kernels, radical saturation, the original Sylow case and n = 2 still require
proof; the displayed splitting alone does not establish them.
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

theorem replacement_field_sized_overlap_displacement
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    let S := stabilizer d.radical a
    let T := (Q d.radical t).subgroupOf S
    let B := (normalizer (T : Set S)).pCoreIn 2
    let D := ⁅U d.radical a ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)),
      B.map S.subtype⁆
    Disjoint D (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))) ∧
      Nat.card D=2^n ∧ D ≤ ⁅U d.radical a,Q d.radical t⁆ := by
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
  have hh := embedded_root_normalizer_overlap hFc h.nonbinary U₀ T₀
    (MovedSection.coverProjection s e) he jS
    (fun x y hxy => hj (congrArg Subtype.val hxy)) hjSr γ haction hγonto hγp hγT
    (by rw [hTimage]; exact hβcard) (by rw [hTimage]; exact hβdim)
    (by rw [hTimage]; exact hβquad)
  let A := (MovedSection.coverProjection s e).toLinearMap.ker.toAddSubgroup.toSubgroup
  have hAm : (A.map jS).map S.subtype=U d.radical a ⊓
      centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) := by
    rw [Subgroup.map_map]
    change A.map j=_
    apply le_antisymm
    · rintro _ ⟨v,hv,rfl⟩
      exact ⟨hjr ▸ ⟨v,rfl⟩,(hker v.toAdd).mp hv⟩
    · rintro x ⟨hx,hxc⟩
      obtain ⟨v,rfl⟩ := hjr.symm ▸ hx
      exact ⟨v,(hker v.toAdd).mpr hxc,rfl⟩
  have hDm : (⁅U₀ ⊓ centralizer (T₀ : Set S),(normalizer (T₀ : Set S)).pCoreIn 2⁆).map
      S.subtype = ⁅U d.radical a ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)),
        ((normalizer (T₀ : Set S)).pCoreIn 2).map S.subtype⁆ := by
    rw [map_commutator,←map_inf_centralizer_of_injective S.subtype S.subtype_injective,
      map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hTS]
  dsimp only
  refine ⟨?_,?_,?_⟩
  · rw [←hAm,←hDm,disjoint_iff]
    rw [←map_inf _ _ _ S.subtype_injective,disjoint_iff.mp hh.1,Subgroup.map_bot]
  · rw [←hDm,card_map_of_injective S.subtype_injective,hh.2.1,hFc]
  · have hl := map_mono (f := S.subtype) hh.2.2
    rwa [hDm,map_commutator,map_subgroupOf_eq_of_le hUS,
      map_subgroupOf_eq_of_le hTS] at hl

/-- The extra original-normalizer action selects a complement to the ENTIRE
fixed kernel in the common critical displacement. -/
theorem replacement_field_sized_overlap_complement
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    let S := stabilizer d.radical a
    let T := (Q d.radical t).subgroupOf S
    let B := (normalizer (T : Set S)).pCoreIn 2
    let D := ⁅U d.radical a ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)),
      B.map S.subtype⁆
    let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
    D ⊔ A=⁅Z d.radical a,Z d.radical z⁆ := by
  let S := stabilizer d.radical a
  let T := (Q d.radical t).subgroupOf S
  let B := (normalizer (T : Set S)).pCoreIn 2
  let D := ⁅U d.radical a ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)),
    B.map S.subtype⁆
  let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
  obtain ⟨hdis,hcard,hle⟩ := replacement_field_sized_overlap_displacement h d path hb hat hzt hsize
  rw [replacement_field_sized_moving_edge_commutator h d path hb hat hzt hsize] at hle
  obtain ⟨_,hAW,hWU,hWcard,_⟩ := replacement_field_sized_paired_fixed_layers h d path hb hat hzt hsize
  have hA : A ≤ ⁅Z d.radical a,Z d.radical z⁆ := le_sup_left.trans hAW
  let := finite_Z d.radical a
  let : Finite (⁅Z d.radical a,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (hWU.trans inf_le_left |>.trans (U_le_Z a))) (inclusion_injective _)
  let := g.Z_elementary (by omega : 0 < g.b d.radical) a path.start_color
  have hn : A ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    (inf_le_left.trans (U_le_Z a)).trans ((Z d.radical a).le_centralizer.trans
      ((centralizer_le (hle.trans hWU |>.trans inf_le_left |>.trans (U_le_Z a))).trans
        (Subgroup.centralizer_le_normalizer _)))
  change D ⊔ A=_
  apply eq_of_le_of_card_ge (sup_le hle hA)
  rw [card_sup_eq_mul_of_normalizes_of_disjoint D A hn hdis,hcard,hWcard]

/-- The ORIGINAL odd-index witness supplies the proper nonsylow application,
with the full fixed kernel and the actual normalizer core retained. -/
theorem replacement_proper_nonsylow_overlap_displacement
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    let S := stabilizer d.radical a
    let T := (Q d.radical t).subgroupOf S
    let B := (normalizer (T : Set S)).pCoreIn 2
    let D := ⁅U d.radical a ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)),
      B.map S.subtype⁆
    Disjoint D (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))) ∧
      Nat.card D=2^n ∧ D ≤ ⁅U d.radical a,Q d.radical t⁆ :=
  replacement_field_sized_overlap_displacement h d path hb hat hzt
    (replacement_proper_nonsylow_card h d g hb hnsyl hne)


/-- The actor is the ORIGINAL radical restricted to the replacement, on
the whole intrinsic core and its full centralizer of the replacement. -/
theorem replacement_proper_nonsylow_original_overlap
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    let U := ⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆
    let D := ⁅U ⊓ centralizer (d.radical : Set d.overgroup),R.subgroupOf d.overgroup⁆
    Disjoint D (U ⊓ centralizer (K.subgroupOf d.overgroup : Set d.overgroup)) ∧
      Nat.card D=2^n ∧ D ≤ ⁅U,d.radical⁆ ∧
      D ⊔ (U ⊓ centralizer (K.subgroupOf d.overgroup : Set d.overgroup))=⁅U,d.radical⁆ := by
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
  have hmL : (K.subgroupOf d.overgroup).map f=Ltilde d.radical (alpha d.radical) := by
    dsimp only [f]
    rw [←Subgroup.map_map,←replacement_residual h d,←Ltilde_alpha,←Ltilde_act,hv]
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
  have hh := replacement_proper_nonsylow_overlap_displacement h d path hb hat hzt hnsyl hne
  dsimp only at hh ⊢
  have hmD := map_commutator
    (⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆ ⊓ centralizer (d.radical : Set d.overgroup))
    (R.subgroupOf d.overgroup) f
  rw [←map_inf_centralizer_of_injective f hf,hmU,hmT,hmB] at hmD
  have hmA := (map_inf_centralizer_of_injective f hf
    ⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆ (K.subgroupOf d.overgroup)).symm
  rw [hmU,hmL] at hmA
  rw [←hmD,←hmA] at hh
  refine ⟨?_,?_,?_,?_⟩
  · apply disjoint_iff.mpr
    apply map_injective hf
    rw [map_inf _ _ _ hf,Subgroup.map_bot]
    exact disjoint_iff.mp hh.1
  · simpa only [card_map_of_injective hf] using hh.2.1
  · have hm := map_commutator ⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆ d.radical f
    rw [hmU,hmT] at hm
    rw [←hm] at hh
    intro x hx
    exact (mem_map_iff_mem hf).mp (hh.2.2 (mem_map_of_mem f hx))
  · have hc := replacement_field_sized_overlap_complement h d path hb hat hzt
      (replacement_proper_nonsylow_card h d g hb hnsyl hne)
    rw [←replacement_field_sized_moving_edge_commutator h d path hb hat hzt
      (replacement_proper_nonsylow_card h d g hb hnsyl hne)] at hc
    dsimp only at hc
    apply map_injective hf
    rw [Subgroup.map_sup,hmD,hmA,map_commutator,hmU,hmT]
    exact hc

/-- In the original ambient group the complete overlap has a field-sized
original-radical displacement disjoint from the entire component-fixed kernel. -/
theorem original_proper_nonsylow_overlap_displacement
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    let U := (blockU K).map K.subtype
    let D := ⁅U ⊓ centralizer (d.ambient : Set H),R ⊓ d.overgroup⁆
    Disjoint D (U ⊓ centralizer (K : Set H)) ∧ Nat.card D=2^n ∧ D ≤ ⁅U,d.ambient⁆ ∧
      D ⊔ (U ⊓ centralizer (K : Set H))=⁅U,d.ambient⁆ := by
  let := h.component_normal
  have hperfect : IsPPerfect 2 K := by
    rw [←h.residual_eq]
    exact isPPerfect_pResidual 2
  have hmU := d.commutatorCore_eq_intrinsic_of_sup (original_sup h) hperfect
  have hmT : d.radical.map d.overgroup.subtype=d.ambient := map_subgroupOf_eq_of_le le_sup_right
  have hh := replacement_proper_nonsylow_original_overlap h d g hb hnsyl hne
  dsimp only at hh ⊢
  have hmD := map_commutator
    (⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆ ⊓ centralizer (d.radical : Set d.overgroup))
    (R.subgroupOf d.overgroup) d.overgroup.subtype
  rw [←map_inf_centralizer_of_injective _ d.overgroup.subtype_injective,hmU,hmT,
    subgroupOf_map_subtype] at hmD
  have hmA := (map_inf_centralizer_of_injective d.overgroup.subtype d.overgroup.subtype_injective
    ⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆ (K.subgroupOf d.overgroup)).symm
  rw [hmU,map_subgroupOf_eq_of_le (show K ≤ d.overgroup from le_sup_left)] at hmA
  refine ⟨?_,?_,?_,?_⟩
  · rw [←hmD,←hmA,disjoint_iff,←map_inf _ _ _ d.overgroup.subtype_injective,
      disjoint_iff.mp hh.1,Subgroup.map_bot]
  · rw [←hmD,card_map_of_injective d.overgroup.subtype_injective]
    exact hh.2.1
  · have hl := map_mono (f := d.overgroup.subtype) hh.2.2.1
    rwa [hmD,map_commutator,hmU,hmT] at hl
  · have he := congrArg (fun A : Subgroup d.overgroup => A.map d.overgroup.subtype) hh.2.2.2
    rwa [Subgroup.map_sup,hmD,hmA,map_commutator,hmU,hmT] at he

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
