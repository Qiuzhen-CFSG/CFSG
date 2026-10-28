module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourCommonOverlap
public import Theory.Representation.SymplecticFourOrthogonalCover.RootOverlapValues
public import Theory.SpecificGroups.SymplecticFour.PointSupplement
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# Equality of the full fixed attachments at critical index q

The long-root action belongs to the actual subgroup Q_alpha Z_alpha',
whose image has order q; the full saturated radical has larger order.
The universal-cover commutator-value calculation identifies an unequal
opposite fixed attachment with the overlap moved by the two-core of this
root subgroup's normalizer. This retains the entire covering kernel.

Intersect that normalizer actor with the actual common radical. Its
movement is contained in the opposite attachment, while the common-section
centralizer calculation makes the same movement disjoint from that
attachment. It is therefore trivial. In point-local coordinates this
forces the radical intersection into the central root. The SL2 quotient
then bounds the full radical image by q squared, contradicting genuine
saturation, which gives order q cubed or q to the fourth power.

This proves the order-q branch of MS93 (3.7)(4), printed p.875, and its
full-Sylow specialization. The proof uses the literal endpoint markings
and both complete fixed attachments. The order-q-squared branch, source
(5)/(6), and the field restriction remain separate obligations.

The root-normalizer transport adapts the existing RootOverlapValues and
DistanceTwoRecognition.OverlapComparison proofs; only the actual critical
root preimage replaces their field-sized whole-radical premise.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition
section Model
open Matrix Representation Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
open Representation.SymplecticFourOrthogonalCover
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] {σ : Representation (ZMod 2) (L (K := F)) W}
private theorem root_overlap_actor_bound
    {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (U T J : Subgroup G)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j) (hjr : j.range=U)
    (γ : G →* L (K := F))
    (hact : ∀ (g : G) (w : W), j (Multiplicative.ofAdd (σ (γ g) w)) =
      g*j (Multiplicative.ofAdd w)*g⁻¹)
    (honto : Function.Surjective γ) (hk : IsPGroup 2 γ.ker) (hkT : γ.ker ≤ T)
    (hc : Nat.card (T.map γ)=Nat.card F)
    (hd : Module.finrank F (displacementSpace ((T.map γ).map (commutator (Sp F)).subtype))=1)
    (hq : ∀ x ∈ (T.map γ).map (commutator (Sp F)).subtype,
      ∀ y ∈ (T.map γ).map (commutator (Sp F)).subtype,
        ∀ v : Vector F, x • (y • v-v)=y • v-v)
    (hJ : IsPGroup 2 J) (hJT : ⁅J,T⁆ ≤ γ.ker)
    (hzero : ⁅U ⊓ centralizer (T : Set G),
      (normalizer (T : Set G)).pCoreIn 2 ⊓ J⁆=⊥) :
    Nat.card (J.map γ) ≤ Nat.card F^2 := by
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact Nat.pow_lt_pow_right (by decide : 1<2) hn
  have hcard : Nat.card ((T.map γ).map (commutator (Sp F)).subtype)=Nat.card F := by
    rw [card_map_of_injective (commutator (Sp F)).subtype_injective,hc]
  obtain ⟨g,hg⟩ := FourLongRoots.exists_conjugate_root_of_displacement_one _ hcard hd hq
  let gl : L (K := F) := ⟨g,by rw [LargeField.commutator_eq_top hlarge]; trivial⟩
  let γ' := (MulAut.conj gl).toMonoidHom.comp γ
  let ψ := (commutator (Sp F)).subtype.comp γ'
  let j' := j.comp (σ gl⁻¹).toAddMonoidHom.toMultiplicative
  have hj'r : j'.range=U := by
    apply le_antisymm
    · rintro _ ⟨w,rfl⟩
      exact hjr ▸ ⟨_,rfl⟩
    · intro u hu
      obtain ⟨w,rfl⟩ := hjr.symm ▸ hu
      obtain ⟨v,hv⟩ := (σ.apply_bijective gl⁻¹).2 w.toAdd
      exact ⟨Multiplicative.ofAdd v,congrArg j (congrArg Multiplicative.ofAdd hv)⟩
  have hj'act (x : G) (w : W) : j' (Multiplicative.ofAdd (σ (γ' x) w))=
      x*j' (Multiplicative.ofAdd w)*x⁻¹ := by
    change j (Multiplicative.ofAdd (σ gl⁻¹ (σ (gl*γ x*gl⁻¹) w)))=_
    have he : σ gl⁻¹ (σ (gl*γ x*gl⁻¹) w)=σ (γ x) (σ gl⁻¹ w) := by
      simp only [map_mul,Module.End.mul_apply,inv_self_apply]
    rw [he,hact]
    rfl
  have hψker : ψ.ker=γ.ker := by
    ext x
    change ((MulAut.conj gl) (γ x)).val=1 ↔ γ x=1
    exact (show ((MulAut.conj gl) (γ x)).val=1 ↔ (MulAut.conj gl) (γ x)=1 from
      ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩).trans
        (MulAut.conj gl).map_eq_one_iff
  have hψonto : Function.Surjective ψ := by
    intro x
    have hx : x ∈ commutator (Sp F) := by rw [LargeField.commutator_eq_top hlarge]; trivial
    obtain ⟨y,hy⟩ := honto ((MulAut.conj gl).symm ⟨x,hx⟩)
    exact ⟨y,congrArg Subtype.val (congrArg (MulAut.conj gl) hy |>.trans
      ((MulAut.conj gl).apply_symm_apply _))⟩
  have hψT : T.map ψ=RootSubgroup.group 0 := by
    change T.map (((commutator (Sp F)).subtype.comp (MulAut.conj gl).toMonoidHom).comp γ)=_
    rw [←Subgroup.map_map]
    have he : (commutator (Sp F)).subtype.comp (MulAut.conj gl).toMonoidHom=
        (MulAut.conj g).toMonoidHom.comp (commutator (Sp F)).subtype := by ext; rfl
    rw [he,←Subgroup.map_map]
    exact hg
  have hψP : ((normalizer (T : Set G)).pCoreIn 2).map ψ=pointRadicalAmbient := by
    have hN : (normalizer (T : Set G)).map ψ=normalizer (T.map ψ : Set (Sp F)) := by
      have he : (normalizer (T.map ψ : Set (Sp F))).comap ψ=normalizer (T : Set G) := by
        rw [comap_normalizer_eq_of_surjective _ hψonto,
          comap_map_eq_self (hψker.trans_le hkT)]
      rw [←he,map_comap_eq_self_of_surjective hψonto]
    rw [map_pCoreIn_of_ker_isPGroup ψ (hψker ▸ hk),hN,hψT,
      RootNormalizerResidual.normalizer_zero_eq]
    exact pointParabolic_core_map_eq_radical hF hn
  let P := (normalizer (T : Set G)).pCoreIn 2
  have hkP : ψ.ker ≤ P := by
    apply le_pCoreIn_of_normalizes (hψker ▸ hk)
      ((hψker.trans_le hkT).trans T.le_normalizer)
    exact le_normalizer_of_normal
  have hJP : J.map ψ ≤ pointLocal := by
    rw [←RootNormalizerResidual.centralizer_zero_eq,←hψT]
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [←map_commutator,map_le_iff_le_comap]
    exact hJT.trans_eq hψker.symm
  let J₀ := (J.map ψ).subgroupOf pointLocal
  have hcentral : J₀ ⊓ pointRadical ≤ center (pointLocal (F := F)) := by
    intro x hx
    have hxmap : x.val ∈ J.map ψ := hx.1
    obtain ⟨b,hb,hbx⟩ := hxmap
    have hbP : b ∈ P := by
      have hh : ψ b ∈ P.map ψ := by
        rw [hψP,hbx]
        exact mem_map_of_mem _ hx.2
      have hh' : b ∈ (P.map ψ).comap ψ := hh
      rwa [comap_map_eq_self hkP] at hh'
    have hxroot : x.val ∈ RootSubgroup.group 0 := by
      rw [←PointRadicalAction.hyperplane_fixer]
      apply (mem_fixingSubgroup_iff _).mpr
      intro v hv
      obtain ⟨w,rfl⟩ := hp.1 v
      have hw : j' (Multiplicative.ofAdd w) ∈ U ⊓ centralizer (T : Set G) := by
        refine ⟨hj'r ▸ ⟨_,rfl⟩,?_⟩
        intro t ht
        obtain ⟨a,ha⟩ := (RootSubgroup.mem_group_iff 0 _).mp
          (show ψ t ∈ RootSubgroup.group 0 from hψT ▸ mem_map_of_mem ψ ht)
        have hw0 : (p w) (.inr 0)=0 := by
          have hh := hv (e 0) (Submodule.subset_span (Set.mem_singleton _))
          simpa [form_apply,Theory.SpecificGroups.SymplecticFour.e] using hh
        have hfix : σ (γ' t) w=w := by
          apply cover_fixed_of_projection_fixed p hp
          change (γ' t).val.val *ᵥ p w=p w
          change rootElement 0 a=(γ' t).val at ha
          rw [←ha,Roots.natural_root,hw0,mul_zero,zero_smul,add_zero]
        have he := congrArg (fun u => j' (Multiplicative.ofAdd u)) hfix
        rw [hj'act,mul_inv_eq_iff_eq_mul] at he
        exact he
      have he : ⁅j' (Multiplicative.ofAdd w),b⁆=1 := by
        have hh := commutator_mem_commutator hw (show b ∈ P ⊓ J from ⟨hbP,hb⟩)
        change ⁅j' (Multiplicative.ofAdd w),b⁆ ∈ ⁅U ⊓ centralizer (T : Set G),
          (normalizer (T : Set G)).pCoreIn 2 ⊓ J⁆ at hh
        rwa [hzero,mem_bot] at hh
      have hfix : σ (γ' b) w=w := by
        apply Multiplicative.ofAdd.injective
        apply (show Function.Injective j' from hj.comp
          (fun x y hxy => Multiplicative.toAdd.injective
            ((σ.apply_bijective gl⁻¹).1 (congrArg Multiplicative.toAdd hxy))))
        rw [hj'act,←(commutatorElement_eq_one_iff_commute.mp he).eq,mul_inv_cancel_right]
      have hh := congrArg p hfix
      rw [p.isIntertwining] at hh
      change (γ' b).val • p w=p w at hh
      exact hbx ▸ hh
    have hm : x.val ∈ (center (pointLocal (F := F))).map pointLocal.subtype := by
      rwa [PointRadicalAction.center_eq_root hF hn]
    exact (mem_map_iff_mem pointLocal.subtype_injective).mp hm
  have hh := PointSupplement.central_kernel_pgroup_card_bound hF hn J₀ J₀
    hcentral le_rfl ((hJ.map ψ).comap_subtype)
  have hjcard : Nat.card J₀=Nat.card (J.map γ) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hJP).toEquiv]
    change Nat.card (J.map ((commutator (Sp F)).subtype.comp
      ((MulAut.conj gl).toMonoidHom.comp γ)))=_
    rw [←Subgroup.map_map,←Subgroup.map_map,card_map_of_injective (commutator (Sp F)).subtype_injective,
      card_map_of_injective (MulAut.conj gl).injective]
  rwa [hjcard] at hh
end Model

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h
open ChapterB.QuasisimpleSource
open Representation Representation.BinaryOffender Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour

/-- The actual root preimage Q Z' selects a field-sized overlap, and every
critical displacement outside the full fixed attachment is either in this
overlap or is one individual commutator of the actual moving groups. -/
theorem critical_root_overlap_geometry
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = 2^n)
    :
    let S := stabilizer d.radical a
    let T := (Q d.radical a ⊔ Z d.radical z).subgroupOf S
    let B := (normalizer (T : Set S)).pCoreIn 2
    let D := ⁅U d.radical a ⊓ centralizer ((Q d.radical a ⊔ Z d.radical z : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)),
      B.map S.subtype⁆
    (Disjoint D (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))) ∧
      Nat.card D=2^n ∧ D ≤ ⁅Z d.radical a,Z d.radical z⁆) ∧
    ∀ x ∈ ⁅Z d.radical a,Z d.radical z⁆,
      x ∉ U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) →
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
  obtain ⟨haq,hzq⟩ := replacement_critical_indices_eq_field_of_small h d path (by omega) (by
    rw [hcritical]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)
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
  have hTS : Q d.radical a ⊔ Z d.radical z ≤ S := sup_le hQS hZS
  let U₀ := (U d.radical a).subgroupOf S
  let T₀ := (Q d.radical a ⊔ Z d.radical z).subgroupOf S
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
    change ((Q d.radical a ⊔ Z d.radical z).subgroupOf S).map γ=β.range
    rw [subgroupOf_sup hQS hZS,Subgroup.map_sup,hQker,
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
    exact (show Q d.radical a ≤ Q d.radical a ⊔ Z d.radical z from le_sup_left) hx
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
      S.subtype = ⁅U d.radical a ⊓ centralizer ((Q d.radical a ⊔ Z d.radical z : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)),
        ((normalizer (T₀ : Set S)).pCoreIn 2).map S.subtype⁆ := by
    rw [map_commutator,←map_inf_centralizer_of_injective S.subtype S.subtype_injective,
      map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hTS]
  have hUT : ⁅U d.radical a,Q d.radical a ⊔ Z d.radical z⁆=⁅Z d.radical a,Z d.radical z⁆ := by
    rw [←commutator_eq_of_centralizing_sup (B := Q d.radical a ⊔ Z d.radical z) rfl
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a path.start_color))).trans (centralizer_le (U_le_Z a)))
      (hZS.trans (U_normalized a))]
    exact (critical_displacement_eq_moving h d path hb hat hzt).symm
  have hgeom := embedded_root_normalizer_overlap hFc h.nonbinary U₀ T₀
    (MovedSection.coverProjection s e) he jS
    (fun x y hxy => hj (congrArg Subtype.val hxy)) hjSr γ haction hγonto hγp hγT
    (by rw [hTimage]; exact hβcard) (by rw [hTimage]; exact hβdim)
    (by rw [hTimage]; exact hβquad)
  dsimp only
  constructor
  · refine ⟨?_,?_,?_⟩
    · rw [←hAm,←hDm,disjoint_iff]
      rw [←map_inf _ _ _ S.subtype_injective,disjoint_iff.mp hgeom.1,Subgroup.map_bot]
    · rw [←hDm,card_map_of_injective S.subtype_injective,hgeom.2.1,hFc]
    · have hl := map_mono (f := S.subtype) hgeom.2.2
      rwa [hDm,map_commutator,map_subgroupOf_eq_of_le hUS,
        map_subgroupOf_eq_of_le hTS,hUT] at hl
  intro x hx hn
  have hxUT : x ∈ ⁅U d.radical a,Q d.radical a ⊔ Z d.radical z⁆ := by
    apply commutator_mono le_rfl le_sup_right
    rwa [←critical_displacement_eq_moving h d path hb hat hzt]
  have hWU : ⁅Z d.radical a,Z d.radical z⁆ ≤ U d.radical a :=
    (critical_paired_fixed_layers h d path hb hat hzt hcritical).2.2.1.trans inf_le_left
  have hxS : x ∈ S := hUS (hWU hx)
  let xS : S := ⟨x,hxS⟩
  have hmUT : (⁅U₀,T₀⁆).map S.subtype=⁅U d.radical a,Q d.radical a ⊔ Z d.radical z⁆ := by
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
      rw [sup_comm]
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
      rwa [←Z_eq_moving_sup_edge_of_distance_two h d g hb path.end_color hzt]
    rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _
      (hcent.trans (Subgroup.centralizer_le_normalizer _))] at hvjoin
    obtain ⟨w,hw,c,hc,rfl⟩ := hvjoin
    have hcu : Commute c u.val :=
      ((hta.trans ((Z d.radical a).le_centralizer.trans (centralizer_le (U_le_Z a)))) hc u.val hu).symm
    rw [commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_eq_one_iff_commute.mpr hcu] at he'
    exact Or.inr ⟨w,hw,u.val,hu,by simpa only [mul_one,mul_inv_cancel,one_mul] using he'⟩



/-- If the complete paired fixed kernels differ, the opposite kernel is
exactly the overlap selected by the critical-root normalizer two-core. -/
theorem critical_opposite_fixed_eq_root_overlap
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = 2^n)
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    let S := stabilizer d.radical a
    let T := (Q d.radical a ⊔ Z d.radical z).subgroupOf S
    let B := (normalizer (T : Set S)).pCoreIn 2
    U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) =
      ⁅U d.radical a ⊓ centralizer ((Q d.radical a ⊔ Z d.radical z : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)),B.map S.subtype⁆ := by
  let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
  let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
  let S := stabilizer d.radical a
  let T := (Q d.radical a ⊔ Z d.radical z).subgroupOf S
  let B := (normalizer (T : Set S)).pCoreIn 2
  let D := ⁅U d.radical a ⊓ centralizer ((Q d.radical a ⊔ Z d.radical z : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)),B.map S.subtype⁆
  obtain ⟨hdis,hA,hA',hjoin⟩ :=
    (critical_fixed_kernels_dichotomy h d path hb hat hzt hcritical).resolve_left hne
  obtain ⟨⟨_,hD,hDW⟩,hvalues⟩ := critical_root_overlap_geometry h d path hb hat hzt hcritical
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
    rcases hvalues x hxW hxA with hd | hv
    · exact hd
    obtain ⟨b,hbU,u,hu,he⟩ := hv
    have hc : ⁅u,b⁆ ∈ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
      rw [←commutatorElement_inv,he]
      exact inv_mem hx.2
    have he1 := critical_value_in_fixed_eq_one h d rev hb hzt
      u (U_le_Z a hu) b hbU hc
    have he2 : ⁅b,u⁆=1 := commutatorElement_eq_one_iff_commute.mpr
      (commutatorElement_eq_one_iff_commute.mp he1).symm
    exact (hxA (he.symm ▸ he2.symm ▸ A.one_mem)).elim
  let := finite_stabilizer d.radical a
  have hDS : D ≤ S := by
    exact hDW.trans ((critical_paired_fixed_layers h d path hb hat hzt hcritical).2.2.1.trans
      inf_le_left |>.trans (U_le_Z a) |>.trans (Z_le_stabilizer d.radical a))
  let : Finite D := Finite.of_injective (inclusion hDS) (inclusion_injective _)
  exact eq_of_le_of_card_ge hle (hD.trans hA'.symm).le


private theorem critical_root_overlap_actor_bound
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = 2^n)
    (hzero :
      let S := stabilizer d.radical a
      let T := (Q d.radical a ⊔ Z d.radical z).subgroupOf S
      let B := ((normalizer (T : Set S)).pCoreIn 2).map S.subtype
      ⁅U d.radical a ⊓ centralizer
        ((Q d.radical a ⊔ Z d.radical z : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)),
        B ⊓ Q d.radical t⁆=⊥) :
    (Q d.radical a).relIndex (Q d.radical t) ≤ (2^n)^2 := by
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
  obtain ⟨haq,hzq⟩ := replacement_critical_indices_eq_field_of_small h d path (by omega) (by
    rw [hcritical]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)
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
  have hTS : Q d.radical a ⊔ Z d.radical z ≤ S := sup_le hQS hZS
  let U₀ := (U d.radical a).subgroupOf S
  let T₀ := (Q d.radical a ⊔ Z d.radical z).subgroupOf S
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
    change ((Q d.radical a ⊔ Z d.radical z).subgroupOf S).map γ=β.range
    rw [subgroupOf_sup hQS hZS,Subgroup.map_sup,hQker,
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
    exact (show Q d.radical a ≤ Q d.radical a ⊔ Z d.radical z from le_sup_left) hx
  let J := (Q d.radical t).subgroupOf S
  have hJ : IsPGroup 2 J := by
    have hh : IsPGroup 2 (Q d.radical t) := by
      rw [←c.radical_eq]
      exact (replacement_isPGroup h d).map c.embedding
    exact hh.comap_subtype
  have hJT : ⁅J,T₀⁆ ≤ γ.ker := by
    rw [←hQker]
    apply (map_le_map_iff_of_injective S.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le c.edge_le,
      map_subgroupOf_eq_of_le hTS,map_subgroupOf_eq_of_le hQS,commutator_comm]
    exact commutator_sup_le_of_relative_normal S (Q d.radical a) (Z d.radical z)
      (Q d.radical t) (Q d.radical a) (Q_normalized d.radical a) hQS hZS
      (le_normalizer_iff_commutator_le_left.mp (c.edge_le.trans (Q_normalized d.radical a)))
      (full_radical_centralizes_critical_root h d path hb c c' hcritical).1
  have hz : ⁅U₀ ⊓ centralizer (T₀ : Set S),(normalizer (T₀ : Set S)).pCoreIn 2 ⊓ J⁆=⊥ := by
    apply map_injective S.subtype_injective
    rw [map_commutator,←map_inf_centralizer_of_injective S.subtype S.subtype_injective,
      map_inf _ _ _ S.subtype_injective,
      map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hTS,
      map_subgroupOf_eq_of_le c.edge_le,Subgroup.map_bot]
    exact hzero
  have hh := root_overlap_actor_bound hFc h.nonbinary U₀ T₀ J
    (MovedSection.coverProjection s e) he jS
    (fun x y hxy => hj (congrArg Subtype.val hxy)) hjSr γ haction hγonto hγp hγT
    (by rw [hTimage]; exact hβcard) (by rw [hTimage]; exact hβdim)
    (by rw [hTimage]; exact hβquad) hJ hJT hz
  have hc : Nat.card (J.map γ)=(Q d.radical a).relIndex (Q d.radical t) := by
    have hh := Sp4Four.SourceComparison.quotient_image_card _ _ _ c.edge_le γ
      (by rw [hγker,hκQ])
    rwa [MonoidHom.range_comp,inclusion_range] at hh
  rwa [hc,hFc] at hh

/-- Source (3.7)(4) for an actual critical image of order q: the two
complete moving-cover attachments agree under genuine radical saturation. -/
theorem source_four_of_field_critical
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a)=2^n) :
    U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
  classical
  by_contra hne
  let S := stabilizer d.radical a
  let T := (Q d.radical a ⊔ Z d.radical z).subgroupOf S
  let B := ((normalizer (T : Set S)).pCoreIn 2).map S.subtype
  let P := B ⊓ Q d.radical t
  let V := Z d.radical a ⊓ Z d.radical z
  let W := ⁅Z d.radical a,Z d.radical z⁆
  let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
  have hC : U d.radical a ⊓ centralizer
      ((Q d.radical a ⊔ Z d.radical z : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) =
      U d.radical a ⊓ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm (inf_le_inf_left _ (centralizer_le
      (show Z d.radical z ≤ Q d.radical a ⊔ Z d.radical z from le_sup_right)))
    apply le_inf inf_le_left
    apply le_centralizer_iff.mpr
    refine sup_le ?_ (le_centralizer_iff.mp inf_le_right)
    exact le_centralizer_iff.mp ((inf_le_left.trans (U_le_Z a)).trans
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a path.start_color)))
  have he : A' = ⁅U d.radical a ⊓ centralizer
      (Z d.radical z : Set (FreeAmalgam d.radical)),B⁆ := by
    have hh := critical_opposite_fixed_eq_root_overlap h d path hb hat hzt hcritical hne
    dsimp only at hh
    rwa [hC] at hh
  obtain ⟨⟨_,_,hDW⟩,_⟩ := critical_root_overlap_geometry h d path hb hat hzt hcritical
  rw [hC] at hDW
  have hm : ⁅U d.radical a ⊓ centralizer
      (Z d.radical z : Set (FreeAmalgam d.radical)),P⁆ ≤ W :=
    (commutator_mono le_rfl inf_le_left).trans hDW
  have hVm : ⁅V,P⁆=⁅U d.radical a ⊓ centralizer
      (Z d.radical z : Set (FreeAmalgam d.radical)),P⁆ :=
    critical_common_overlap_movement h d g hb hsat path hat hzt c c' hcritical P inf_le_right
  obtain ⟨B₀,hB₀,hmem,_,_,hdis⟩ :=
    source_four_common_overlap_centralizer h d g hb hsat path hat hzt c c' hcritical
  have hPB : P ≤ B₀ := by
    intro b hbP
    refine (hmem b).mpr ⟨hbP.2,?_⟩
    have hh : ⁅P,V⁆ ≤ W := by rw [commutator_comm,hVm]; exact hm
    exact fun v hv => commutator_le.mp hh b hbP v hv
  have hdisP : Disjoint ⁅V,P⁆ A' := hdis.mono_left (commutator_mono le_rfl hPB)
  have hleA : ⁅V,P⁆ ≤ A' := by
    rw [hVm,he]
    exact commutator_mono le_rfl inf_le_left
  have hz : ⁅V,P⁆=⊥ := by
    apply le_bot_iff.mp
    exact (le_inf le_rfl hleA).trans (disjoint_iff_inf_le.mp hdisP)
  have hbnd := critical_root_overlap_actor_bound h d path hb c c' hcritical (by
    dsimp only
    rw [hC]
    exact hVm.symm ▸ hz)
  have hindex : (Q d.radical a).relIndex (Q d.radical t) =
      Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) := by
    rw [relIndex,←c.action_kernel,index_ker,c.action_range]
  rw [hindex] at hbnd
  have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  rcases marked_radical_card h d g (by omega) hsat with hh | hh
  · rw [hh,h.field_card] at hbnd
    exact (not_le_of_gt (Nat.pow_lt_pow_right hq (by decide : 2 < 3))) hbnd
  · rw [hh,h.field_card] at hbnd
    exact (not_le_of_gt (Nat.pow_lt_pow_right hq (by decide : 2 < 4))) hbnd

/-- The full-Sylow branch discharges the critical-image premise and gives
equality of the two complete fixed attachments. -/
theorem source_four_of_full_sylow
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (S : Sylow 2 (Sp F)) (hS : (S : Subgroup (Sp F))=c.action.range) :
    U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) :=
  source_four_of_field_critical h d g hb hsat path hat hzt c c'
    (critical_indices_eq_field_of_full_sylow h d path hb hat hzt c c' S hS).1

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
