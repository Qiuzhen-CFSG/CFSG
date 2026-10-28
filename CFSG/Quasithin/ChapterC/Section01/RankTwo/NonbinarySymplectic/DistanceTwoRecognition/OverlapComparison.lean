module
public import Theory.Representation.SymplecticFourOrthogonalCover.RootOverlapValues
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.OverlapAction


/-!
# The opposite full fixed kernel and the original radical overlap

At field-sized critical index, root coordinates describe every displacement
outside the complete fixed kernel: it is either a single critical commutator
or belongs to the overlap selected by the normalizer two-core. The literal
edge factorization replaces the actor by the opposite moving group. Fixed
lifting excludes individual commutators in the opposite fixed kernel.

Consequently, when the two full fixed kernels differ, the opposite kernel
is exactly the normalizer-selected overlap. Reversing the critical path
identifies both selected overlaps and proves that they are complementary.
The original odd-index witness supplies the actual proper nonsylow consumer.
No kernel is discarded, and the field degree remains arbitrary.

Source: MS93 (3.7)(4), printed p.875. Its subsequent shared-overlap comparison,
radical saturation, Sylow branch and degree-two restriction remain necessary
for final recognition; the exchanged-complement alternative is retained here.
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

theorem replacement_field_sized_value_or_overlap
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n)
    (x : FreeAmalgam d.radical) (hx : x ∈ ⁅Z d.radical a,Z d.radical z⁆)
    (hn : x ∉ U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))) :
    let S := stabilizer d.radical a
    let T := (Q d.radical t).subgroupOf S
    let B := (normalizer (T : Set S)).pCoreIn 2
    let D := ⁅U d.radical a ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)),
      B.map S.subtype⁆
    x ∈ D ∨ ∃ b ∈ U d.radical z, ∃ u ∈ U d.radical a, ⁅b,u⁆=x := by
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
  have hxUT : x ∈ ⁅U d.radical a,Q d.radical t⁆ := by
    rwa [replacement_field_sized_moving_edge_commutator h d path hb hat hzt hsize]
  have hWU : ⁅Z d.radical a,Z d.radical z⁆ ≤ U d.radical a :=
    (replacement_field_sized_paired_fixed_layers h d path hb hat hzt hsize).2.2.1.trans inf_le_left
  have hxS : x ∈ S := hUS (hWU hx)
  let xS : S := ⟨x,hxS⟩
  have hmUT : (⁅U₀,T₀⁆).map S.subtype=⁅U d.radical a,Q d.radical t⁆ := by
    rw [map_commutator,map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hTS]
  have hxSUT : xS ∈ ⁅U₀,T₀⁆ := (mem_map_iff_mem S.subtype_injective).mp
    (show S.subtype xS ∈ (⁅U₀,T₀⁆).map S.subtype from hmUT.symm ▸ hxUT)
  have hxSA : xS ∉ A.map jS := by
    intro hxA
    exact hn (hAm ▸ mem_map_of_mem S.subtype hxA)
  have hh := embedded_root_normalizer_value_or_overlap hFc h.nonbinary U₀ T₀
    (MovedSection.coverProjection s e) he jS hjSr γ haction hγonto hγp hγT
    (by rw [hTimage]; exact hβcard) (by rw [hTimage]; exact hβdim)
    (by rw [hTimage]; exact hβquad) xS hxSUT hxSA
  rcases hh with hh | hh
  · left
    exact hDm ▸ mem_map_of_mem S.subtype hh
  · obtain ⟨b,hbT,u,hu,he⟩ := hh
    have he' : ⁅b.val,u.val⁆=x := congrArg Subtype.val he
    have hbjoin : b.val ∈ Z d.radical z ⊔ Q d.radical a := by
      rw [sup_comm,hjoin]
      exact hbT
    have hZQ : Z d.radical z ≤ normalizer (Q d.radical a : Set (FreeAmalgam d.radical)) :=
      hZS.trans (Q_normalized d.radical a)
    rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _ hZQ] at hbjoin
    obtain ⟨v,hv,c,hc,hvc⟩ := hbjoin
    have hcu : Commute c u.val :=
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a path.start_color))) hc u.val (U_le_Z a hu)).symm
    rw [←hvc,commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_eq_one_iff_commute.mpr hcu] at he'
    simp only [mul_one,mul_inv_cancel,one_mul] at he'
    let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
    let := g.Z_elementary (by omega : 0 < g.b d.radical) a path.start_color
    have htz : Z d.radical t ≤ Z d.radical z := Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt
    have hta : Z d.radical t ≤ Z d.radical a := Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat
    have hcent : Z d.radical t ≤ centralizer (U d.radical z : Set (FreeAmalgam d.radical)) :=
      htz.trans ((Z d.radical z).le_centralizer.trans (centralizer_le (U_le_Z z)))
    have hvjoin : v ∈ U d.radical z ⊔ Z d.radical t := by
      rwa [←(replacement_field_sized_central_layers h d rev hb hzt hat hsize).2]
    rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _
      (hcent.trans (Subgroup.centralizer_le_normalizer _))] at hvjoin
    obtain ⟨w,hw,c,hc,rfl⟩ := hvjoin
    have hcu : Commute c u.val :=
      ((hta.trans ((Z d.radical a).le_centralizer.trans (centralizer_le (U_le_Z a)))) hc u.val hu).symm
    rw [commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_eq_one_iff_commute.mpr hcu] at he'
    exact Or.inr ⟨w,hw,u.val,hu,by simpa only [mul_one,mul_inv_cancel,one_mul] using he'⟩


/-- If the complete paired fixed kernels differ, the opposite kernel is
exactly the overlap selected by the original normalizer two-core. -/
theorem replacement_field_sized_opposite_fixed_eq_overlap
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n)
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    let S := stabilizer d.radical a
    let T := (Q d.radical t).subgroupOf S
    let B := (normalizer (T : Set S)).pCoreIn 2
    U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) =
      ⁅U d.radical a ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)),B.map S.subtype⁆ := by
  let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
  let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
  let S := stabilizer d.radical a
  let T := (Q d.radical t).subgroupOf S
  let B := (normalizer (T : Set S)).pCoreIn 2
  let D := ⁅U d.radical a ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)),B.map S.subtype⁆
  obtain ⟨hdis,hA,hA',hjoin⟩ :=
    (replacement_field_sized_fixed_kernels_dichotomy h d path hb hat hzt hsize).resolve_left hne
  obtain ⟨_,hD,hDW⟩ := replacement_field_sized_overlap_displacement h d path hb hat hzt hsize
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have hle : A' ≤ D := by
    intro x hx
    by_cases hxA : x ∈ A
    · have hx1 : x=1 := (disjoint_iff_inf_le.mp hdis) ⟨hxA,hx⟩
      exact hx1 ▸ D.one_mem
    have hxW : x ∈ ⁅Z d.radical a,Z d.radical z⁆ := hjoin ▸ mem_sup_right hx
    rcases replacement_field_sized_value_or_overlap h d path hb hat hzt hsize x hxW hxA with hd | hv
    · exact hd
    obtain ⟨b,hbU,u,hu,he⟩ := hv
    have hc : ⁅u,b⁆ ∈ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
      rw [←commutatorElement_inv,he]
      exact inv_mem hx.2
    have he1 := replacement_field_sized_value_in_fixed_eq_one h d rev hb hzt hat hsize
      u (U_le_Z a hu) b hbU hc
    have he2 : ⁅b,u⁆=1 := commutatorElement_eq_one_iff_commute.mpr
      (commutatorElement_eq_one_iff_commute.mp he1).symm
    exact (hxA (he.symm ▸ he2.symm ▸ A.one_mem)).elim
  let := finite_stabilizer d.radical a
  have hDS : D ≤ S := by
    rw [replacement_field_sized_moving_edge_commutator h d path hb hat hzt hsize] at hDW
    exact hDW.trans ((replacement_field_sized_paired_fixed_layers h d path hb hat hzt hsize).2.2.1.trans
      inf_le_left |>.trans (U_le_Z a) |>.trans (Z_le_stabilizer d.radical a))
  let : Finite D := Finite.of_injective (inclusion hDS) (inclusion_injective _)
  exact eq_of_le_of_card_ge hle (hD.trans hA'.symm).le

/-- The opposite full fixed kernel in the proper nonsylow branch is either
the first full kernel or its ORIGINAL-normalizer overlap. -/
theorem replacement_proper_nonsylow_fixed_kernel_alternatives
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
    let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
    let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
    A'=A ∨ A'=⁅U d.radical a ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)),B.map S.subtype⁆ := by
  classical
  dsimp only
  by_cases he : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
  · exact Or.inl he.symm
  exact Or.inr (replacement_field_sized_opposite_fixed_eq_overlap h d path hb hat hzt
    (replacement_proper_nonsylow_card h d g hb hnsyl hne) he)


/-- In the unequal case, the two ORIGINAL-normalizer overlaps are the
opposite complete fixed kernels; in particular they are disjoint. -/
theorem replacement_field_sized_unequal_paired_overlaps
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n)
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    let D := fun v : Vertex d.radical =>
      ⁅U d.radical v ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)),
        ((normalizer ((Q d.radical t).subgroupOf (stabilizer d.radical v) :
          Set (stabilizer d.radical v))).pCoreIn 2).map (stabilizer d.radical v).subtype⁆
    D a = U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) ∧
      D z = U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ∧
      Disjoint (D a) (D z) ∧ D a ⊔ D z=⁅Z d.radical a,Z d.radical z⁆ := by
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have ha := replacement_field_sized_opposite_fixed_eq_overlap h d path hb hat hzt hsize hne
  have hz := replacement_field_sized_opposite_fixed_eq_overlap h d rev hb hzt hat hsize (Ne.symm hne)
  obtain ⟨hd,_,_,hj⟩ :=
    (replacement_field_sized_fixed_kernels_dichotomy h d path hb hat hzt hsize).resolve_left hne
  dsimp only at ha hz ⊢
  refine ⟨ha.symm,hz.symm,?_,?_⟩
  · rw [←ha,←hz]
    exact hd.symm
  · rw [←ha,←hz,sup_comm]
    exact hj

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
