module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.CriticalFixedLayers

/-!
# The full fixed-core displacement bound in MS93 (3.7)(2)

The fixed core D acts quadratically on the opposite full cover U′. Its
commutator and the critical root commutator together have isotropic natural
displacement, hence dimension at most two. The full cover kernel lies in
the critical commutator, with index q. Multiplicativity of the literal
subgroup indices therefore bounds the additional displacement index by q.

Intersecting the displacement with the critical commutator puts it inside
A = U ∩ C(L), without deleting any fixed attachment. Thus the source's
full-group bound |[Z′,D]| ≤ q |A| follows, with the actual saturated
radical, original core kernels and natural-cover action. The same source
configuration discharges every premise of the embedded linear argument.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.7)(2), printed p.873. The following actor-order bound 2q,
point-radical exclusion and final whole-core contradiction remain separate
steps; this result does not assert the degree-two field restriction.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover Theory.SpecificGroups.SymplecticFour

private theorem cover_mixed_fixed
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U A B : Subgroup G) (j : Multiplicative W →* G) (hj : Function.Injective j)
    (hjr : j.range=U) (β : A →* L (K := F)) (γ : B →* L (K := F))
    (hactA : ∀ (a : A) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (hactB : ∀ (b : B) (w : W), j (Multiplicative.ofAdd (σ (γ b) w))=
      b.val*j (Multiplicative.ofAdd w)*b.val⁻¹)
    (htriple : ⁅⁅A,U⁆,B⁆=⊥) :
    displacementSpace (((commutator (Sp F)).subtype.comp β).range) ≤
      TwoLocalCover.fixedSpace (((commutator (Sp F)).subtype.comp γ).range) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨a,v⟩,rfl⟩ b hb
  change b • (a.val • v-v)=a.val • v-v
  obtain ⟨a,ha⟩ := a.property
  rw [←ha]
  obtain ⟨b,rfl⟩ := hb
  obtain ⟨w,rfl⟩ := hp.1 v
  have hval : j (Multiplicative.ofAdd (σ (β a) w-w)) =
      ⁅a.val,j (Multiplicative.ofAdd w)⁆ := by
    rw [ofAdd_sub,map_div,div_eq_mul_inv,hactA]
    rfl
  have hc : b.val*⁅a.val,j (Multiplicative.ofAdd w)⁆ =
      ⁅a.val,j (Multiplicative.ofAdd w)⁆*b.val :=
    commutator_eq_bot_iff_le_centralizer.mp htriple
      (commutator_mem_commutator a.property (show j (Multiplicative.ofAdd w) ∈ U from hjr ▸ ⟨_,rfl⟩)) b.val b.property
  have he : σ (γ b) (σ (β a) w-w)=σ (β a) w-w := by
    apply Multiplicative.ofAdd.injective
    apply hj
    rw [hactB,hval,hc,mul_inv_cancel_right]
  have hh := congrArg p he
  rw [p.isIntertwining,map_sub,p.isIntertwining] at hh
  exact hh

private theorem cover_quadratic_sup_index
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U A B : Subgroup G) [Finite U] [IsMulCommutative U]
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (hjr : j.range=U) (β : A →* L (K := F)) (γ : B →* L (K := F))
    (hactA : ∀ (a : A) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (hactB : ∀ (b : B) (w : W), j (Multiplicative.ofAdd (σ (γ b) w))=
      b.val*j (Multiplicative.ofAdd w)*b.val⁻¹)
    (hAU : A ≤ normalizer (U : Set G)) (hBU : B ≤ normalizer (U : Set G))
    (haa : ⁅⁅A,U⁆,A⁆=⊥) (hbb : ⁅⁅B,U⁆,B⁆=⊥) (hab : ⁅⁅A,U⁆,B⁆=⊥)
    (hkr : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j ≤ ⁅B,U⁆)
    (hki : (p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j).relIndex ⁅B,U⁆ = Nat.card F) :
    (⁅B,U⁆).relIndex ⁅A,U⁆ ≤ Nat.card F := by
  let C := ⁅A,U⁆
  let R := ⁅B,U⁆
  let K := p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j
  let α := (commutator (Sp F)).subtype.comp β
  let δ := (commutator (Sp F)).subtype.comp γ
  let P := displacementSpace α.range
  let Q := displacementSpace δ.range
  let S := P ⊔ Q
  have hPP : P ≤ (form F).orthogonal P := by
    rw [orthogonal_displacementSpace]
    exact cover_mixed_fixed σ p hp U A A j hj hjr β β hactA hactA haa
  have hQQ : Q ≤ (form F).orthogonal Q := by
    rw [orthogonal_displacementSpace]
    exact cover_mixed_fixed σ p hp U B B j hj hjr γ γ hactB hactB hbb
  have hPQ : P ≤ (form F).orthogonal Q := by
    rw [orthogonal_displacementSpace]
    exact cover_mixed_fixed σ p hp U A B j hj hjr β γ hactA hactB hab
  have hiso : ∀ v ∈ S, ∀ w ∈ S, form F v w=0 := by
    intro v hv w hw
    obtain ⟨r,hr,s,hs,rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨t,ht,u,hu,rfl⟩ := Submodule.mem_sup.mp hw
    simp only [map_add,LinearMap.add_apply,hPP ht r hr,
      TwoLocalCover.form_alternating.eq_iff.mp (hPQ hr u hu),
      hPQ ht s hs,hQQ hu s hs,add_zero]
  have hdim := TwoLocalCover.finrank_le_two_of_isotropic S hiso
  obtain ⟨π,hπ,hπj,hπact⟩ := exists_equivariant_embedded_projection U A hAU σ
    (binaryNatural (K := F)) j hj hjr p.toLinearMap hp.1
    (fun x w => LinearMap.congr_fun (p.isIntertwining' x) w) β hactA
  have hk : π.ker.map U.subtype=K := by
    apply le_antisymm
    · rintro x ⟨u,hu,rfl⟩
      obtain ⟨w,hw⟩ := (hjr.symm ▸ u.property : u.val ∈ j.range)
      have he : u=⟨j w,hjr ▸ ⟨w,rfl⟩⟩ := Subtype.ext hw.symm
      refine ⟨w,?_,hw⟩
      have hh : π u=1 := hu
      rw [he] at hh
      exact congrArg Multiplicative.toAdd ((hπj w.toAdd).symm.trans hh)
    · rintro x ⟨w,hw,rfl⟩
      refine ⟨⟨j w,hjr ▸ ⟨w,rfl⟩⟩,?_,rfl⟩
      exact (hπj w.toAdd).trans (congrArg Multiplicative.ofAdd hw)
  let M := S.toAddSubgroup.toSubgroup
  let N := (M.comap π).map U.subtype
  have hC : C ≤ U := le_normalizer_iff_commutator_le_right.mp hAU
  have hR : R ≤ U := le_normalizer_iff_commutator_le_right.mp hBU
  have hJ : C ⊔ R ≤ U := sup_le hC hR
  have hN (B : Subgroup G) (γ : B →* L (K := F))
      (hact : ∀ (b : B) (w : W), j (Multiplicative.ofAdd (σ (γ b) w))=
        b.val*j (Multiplicative.ofAdd w)*b.val⁻¹)
      (hle : displacementSpace (((commutator (Sp F)).subtype.comp γ).range) ≤ S) :
      ⁅B,U⁆ ≤ N := by
    apply commutator_le.mpr
    intro b hb u hu
    obtain ⟨w,rfl⟩ := (hjr.symm ▸ hu : u ∈ j.range)
    let v := σ (γ ⟨b,hb⟩) w.toAdd-w.toAdd
    refine ⟨⟨j (Multiplicative.ofAdd v),hjr ▸ ⟨_,rfl⟩⟩,?_,?_⟩
    · change (π ⟨j (Multiplicative.ofAdd v),_⟩).toAdd ∈ S
      rw [hπj]
      change p v ∈ S
      dsimp only [v]
      rw [map_sub,p.isIntertwining]
      apply hle
      exact Coinvariants.sub_mem_ker
        (ρ := (symplecticNatural 2).comp (((commutator (Sp F)).subtype.comp γ).range).subtype)
        ⟨(γ ⟨b,hb⟩).val,⟨_,rfl⟩⟩ (p w.toAdd)
    · change j (Multiplicative.ofAdd (σ (γ ⟨b,hb⟩) w.toAdd-w.toAdd))=⁅b,j w⁆
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
      rfl
  have hJN : C ⊔ R ≤ N := sup_le (hN A β hactA le_sup_left) (hN B γ hactB le_sup_right)
  have hm : ((C ⊔ R).subgroupOf U).map π ≤ M := by
    rintro v ⟨u,hu,rfl⟩
    obtain ⟨w,hw,he⟩ := hJN hu
    have he' : w=u := Subtype.ext he
    exact he' ▸ hw
  have hi : K.relIndex (C ⊔ R) ≤ Nat.card F^2 := by
    have he : K.relIndex (C ⊔ R) = Nat.card (((C ⊔ R).subgroupOf U).map π) := by
      rw [←relIndex_ker]
      have hh := relIndex_subgroupOf (H := K) hJ
      rw [←hk,subgroupOf_map_subtype_eq] at hh
      rw [hk] at hh
      exact hh.symm
    rw [he]
    apply (Nat.card_le_card_of_injective (inclusion hm) (inclusion_injective _)).trans
    let e : M ≃ S :=
      { toFun := fun x => ⟨x.val.toAdd,x.property⟩
        invFun := fun x => ⟨Multiplicative.ofAdd x.val,x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e,Module.natCard_eq_pow_finrank (K := F)]
    exact Nat.pow_le_pow_right Nat.card_pos hdim
  have hsup : R.relIndex (C ⊔ R)=R.relIndex C := by
    rw [←relIndex_subgroupOf hJ,subgroupOf_sup hC hR,relIndex_sup_right,
      relIndex_subgroupOf hC]
  have ht := relIndex_mul_relIndex K R (C ⊔ R) hkr le_sup_right
  rw [hki,hsup] at ht
  have hq : 0 < Nat.card F := Nat.card_pos
  change R.relIndex C ≤ Nat.card F
  nlinarith

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The source fixed-core displacement contains no contribution from the
common edge center, which is fixed by the whole incident radical. -/
theorem fixedCore_displacement_eq_moving
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t) :
    ⁅Z d.radical z,fixedCore d.radical a⁆ = ⁅U d.radical z,fixedCore d.radical a⁆ := by
  have hAT : fixedCore d.radical a ≤ Q d.radical t := inf_le_left.trans c.core_le_edge
  have ht : color d.radical t = true := by
    have hn := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all [path.start_color]
  have hc : Z d.radical t ≤ centralizer (fixedCore d.radical a : Set (FreeAmalgam d.radical)) := by
    have he : Z d.radical t = omegaCenter (Q d.radical t) := by simp [Z,ht,edgeOmega]
    rw [he]
    exact fun x hx y hy => (mem_omegaCenter_iff.mp hx).2.2 y (hAT hy)
  have hUzT : U d.radical z ≤ Q d.radical t :=
    (c'.componentRadical_inf_core g hb path.end_color).symm.le.trans
      (inf_le_left.trans inf_le_left)
  apply le_antisymm ?_ (commutator_mono (U_le_Z z) le_rfl)
  rw [commutator_comm (Z d.radical z),commutator_comm (U d.radical z)]
  apply commutator_le_moving_of_inner_mod_centralizer (fixedCore d.radical a)
    (U d.radical z) (Z d.radical z) (hUzT.trans c.fixedCore_normalized)
  rw [Z_eq_moving_sup_edge_of_distance_two h d g hb path.end_color hzt]
  exact sup_le_sup_left hc _

/-- In the large-movement branch the fixed-core displacement adds at most
q cosets to the actual critical commutator. The full cover kernel stays
inside that commutator throughout the quotient calculation. -/
theorem source_two_large_displacement_index
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)) :
    (⁅Z d.radical a,Z d.radical z⁆).relIndex ⁅Z d.radical z,fixedCore d.radical a⁆ ≤ 2^n := by
  let := replacementComponent_normal h d
  let := finite_Z d.radical z
  let : Finite (U d.radical z) := Finite.of_injective
    (inclusion (U_le_Z z)) (inclusion_injective _)
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
  let : IsElementaryAbelian 2 (U d.radical z) :=
    IsElementaryAbelian.of_injective (inclusion (U_le_Z z)) (inclusion_injective _)
  let s := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.end_color
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
  have haction (x : stabilizer d.radical z) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (γ x) w)) =
        x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC x))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj x w
  have hAS : fixedCore d.radical a ≤ stabilizer d.radical z :=
    (inf_le_left.trans c.core_le_edge).trans c'.edge_le
  have hBS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (g.exists_critical a path.start_color) path.critical.1.le
  let βA := γ.comp (inclusion hAS)
  let βB := γ.comp (inclusion hBS)
  have hk : (MovedSection.coverProjection s e).toLinearMap.ker.toAddSubgroup.toSubgroup.map j =
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · rintro x ⟨v,hv,rfl⟩
      exact ⟨hjr ▸ ⟨v,rfl⟩,(hker v.toAdd).mp hv⟩
    · rintro x ⟨hx,hc⟩
      obtain ⟨v,rfl⟩ := hjr.symm ▸ hx
      exact ⟨v,(hker v.toAdd).mpr hc,rfl⟩
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have hcrit := (source_two_large_movement_images h d g hb hsat path hat hzt c c' hlarge).2.2.1
  have hother := (replacement_critical_indices_eq_field_of_small h d path (by omega) (by
    rw [hcrit]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)).2
  have hf := critical_fixed_layer_index h d rev hb hzt hat hother
  have hR : ⁅Z d.radical a,Z d.radical z⁆ = ⁅Z d.radical a,U d.radical z⁆ := by
    rw [commutator_comm (Z d.radical a),critical_displacement_eq_moving h d rev hb hzt hat,
      commutator_comm]
  rw [commutator_comm (Z d.radical z),hR] at hf
  have haa : ⁅⁅fixedCore d.radical a,U d.radical z⁆,fixedCore d.radical a⁆=⊥ := by
    rw [commutator_comm (fixedCore d.radical a)]
    exact le_antisymm ((commutator_mono (commutator_mono (U_le_Z z) le_rfl) le_rfl).trans
      (source_two_fixedCore_quadratic h d g hb hsat path hat hzt c c').le) bot_le
  have hRZa : ⁅Z d.radical a,U d.radical z⁆ ≤ Z d.radical a := by
    rw [←hR,critical_displacement_eq_paired_moving h d path hb hat hzt]
    exact (le_normalizer_iff_commutator_le_left.mp ((U_le_Z z).trans
      (Sp4Four.SourceComparison.critical_reverse_actor_normalizes_moving path))).trans (U_le_Z a)
  let := g.Z_elementary (by omega : 0 < g.b d.radical) a path.start_color
  have hbb : ⁅⁅Z d.radical a,U d.radical z⁆,Z d.radical a⁆=⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hRZa.trans (Z d.radical a).le_centralizer)
  have hUD : ⁅fixedCore d.radical a,U d.radical z⁆ ≤ fixedCore d.radical a :=
    le_normalizer_iff_commutator_le_left.mp
      (((U_le_Z z).trans (Z_le_stabilizer_of_dist_le z
        (g.exists_critical z path.end_color) (by
          rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
            g.distance_constant z path.end_color]))).trans (fixedCore_normalized d.radical a))
  have hab : ⁅⁅fixedCore d.radical a,U d.radical z⁆,Z d.radical a⁆=⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply hUD.trans
    apply (show fixedCore d.radical a ≤ Q d.radical a from inf_le_left).trans
    rw [←commutator_eq_bot_iff_le_centralizer,commutator_comm]
    exact Z_centralizes_Q d.radical a path.start_color
  have hh := cover_quadratic_sup_index (MovedSection.coverAction s e)
    (MovedSection.coverProjection s e) he (U d.radical z)
    (fixedCore d.radical a) (Z d.radical a) j hj hjr βA βB
    (fun x => haction (inclusion hAS x)) (fun x => haction (inclusion hBS x))
    (hAS.trans (U_normalized z)) (hBS.trans (U_normalized z)) haa hbb hab
    (hk.symm ▸ hf.1) (by rw [hk]; simpa only [E.card_eq,hE] using hf.2)
  rw [fixedCore_displacement_eq_moving h d g hb path hat hzt c c',hR,
    commutator_comm (U d.radical z)]
  simpa only [E.card_eq,hE] using hh

/-- The next source estimate in (3.7)(2), printed p.873: the full
fixed-core displacement has order at most q times the first fixed
attachment. The attachment is retained as an actual subgroup. -/
theorem source_two_large_displacement_card
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)) :
    Nat.card (⁅Z d.radical z,fixedCore d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) ≤
      2^n * Nat.card (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) : Subgroup (FreeAmalgam d.radical)) := by
  let W := ⁅Z d.radical a,Z d.radical z⁆
  let C := ⁅Z d.radical z,fixedCore d.radical a⁆
  let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
  let := finite_Z d.radical a
  let : Finite A := Finite.of_injective (inclusion (inf_le_left.trans (U_le_Z a))) (inclusion_injective _)
  have hi := critical_commutator_inf_fixedCore_displacement h d path hb hat hzt c
  let f : W.subgroupOf C → A := fun x => ⟨x.val.val,hi ⟨x.property,x.val.property⟩⟩
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun x : A => x.val) he))
  have hc := Nat.card_le_card_of_injective f hf
  have hindex := source_two_large_displacement_index h d g hb hsat path hat hzt c c' hlarge
  have hmul : Nat.card (W.subgroupOf C) * W.relIndex C = Nat.card C :=
    (W.subgroupOf C).card_mul_index
  change Nat.card C ≤ 2^n * Nat.card A
  rw [←hmul,mul_comm (2^n)]
  exact Nat.mul_le_mul hc hindex

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
