module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorPointRadical
public import Theory.Representation.BinaryTensorThree.WreathCoordinates

/-!
# Coordinates at every original Sylow-fixed tensor point

An identification of the image of the original L₀T action with the concrete
tensor group constructs its surjective wreath marking. Sylow conjugacy then
aligns the original T-image with the paired flag subgroup. The one-dimensional
fixed space forces every prescribed nonidentity T-fixed vector to become the
marked pure tensor. Thus neither a chosen point marking nor radical coordinates
are additional hypotheses of the original weak-closure consumer.

The tensor-image recognition, the ambient point-core inclusion and the strict
r bound remain source obligations. This does not assert quiet tensor exclusion
or FixedSupportRowsAt. Their discharge remains with the selected-module owner;
final point control remains with its existing assembly owner.
Source: Aschbacher--Smith H.4.4 and 8.3.11--14, pp.383--385,724--727.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- The original L₀T conjugation action in the supplied binary coordinates.
Its kernel is retained; no abstract identification of the acting group is used. -/
def quietTensorLinearAction
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space) :
    localJoin T L →* (BinaryTensorThree.Space ≃ₗ[ZMod 2] BinaryTensorThree.Space) :=
  let hHN : localJoin T L ≤ normalizer (D.fullModule : Set G) :=
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)).trans
      D.maximalLocal_normalizes_fullModule
  let ρ : Representation (ZMod 2) (localJoin T L) (Additive D.fullModule) :=
    (automizerRepresentation D.fullModule).comp
    (D.fullModule.normalizerMonoidHom.rangeRestrict.comp (inclusion hHN))
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) BinaryTensorThree.Space).toMonoidHom.comp
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv e).toMonoidHom.comp ρ.asGroupHom)

theorem quietTensorLinearAction_apply
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (a : localJoin T L) (v : Additive D.fullModule) :
    quietTensorLinearAction D e a (e v) =
      e (Additive.ofMul
        (D.fullModule.normalizerMonoidHom
          ⟨a,D.maximalLocal_normalizes_fullModule
            ((sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)) a.property)⟩
          v.toMul)) := by
  have hN : localJoin T L ≤ normalizer (D.fullModule : Set G) :=
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)).trans
      D.maximalLocal_normalizes_fullModule
  change e (Additive.ofMul
    (D.fullModule.normalizerMonoidHom ⟨a,hN a.property⟩ (e.symm (e v)).toMul)) = _
  rw [e.symm_apply_apply]

/-- The coordinate action retains exactly the centralizer of the original
full module inside L₀T. -/
theorem quietTensorLinearAction_ker
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space) :
    (quietTensorLinearAction D e).ker =
      centralizer (D.fullModule.subgroupOf (localJoin T L) : Set (localJoin T L)) := by
  let H := localJoin T L
  have hVH : D.fullModule ≤ H := D.fullModule_le_orbit.trans le_sup_left
  ext a
  change quietTensorLinearAction D e a = 1 ↔ _
  constructor
  · intro ha v hv
    have hh := congrArg (fun f : BinaryTensorThree.Space ≃ₗ[ZMod 2] BinaryTensorThree.Space =>
      f (e (Additive.ofMul ⟨v,hv⟩))) ha
    rw [quietTensorLinearAction_apply] at hh
    have he := congrArg (fun w : Additive D.fullModule => (w.toMul : G)) (e.injective hh)
    change (a : G)*(v : G)*(a : G)⁻¹ = (v : G) at he
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro ha
    apply LinearEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := e.surjective w
    rw [quietTensorLinearAction_apply]
    apply congrArg e
    apply congrArg Additive.ofMul
    apply Subtype.ext
    change (a : G)*(v.toMul : G)*(a : G)⁻¹ = (v.toMul : G)
    have he := congrArg H.subtype (ha ⟨v.toMul,hVH v.toMul.property⟩ v.toMul.property)
    change (v.toMul : G)*(a : G) = (a : G)*(v.toMul : G) at he
    rw [←he,mul_inv_cancel_right]

/-- Recognition of the actual linear image constructs the surjective matrix
wreath marking and its exact conjugation formula. -/
theorem quiet_exists_tensor_marking_of_action_image
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (himage : (quietTensorLinearAction D e).range = BinaryTensorThree.tensorGroup) :
    ∃ q : localJoin T L →* BinaryTensorThree.PointParabolic.Actor,
      Function.Surjective q ∧
      ∀ (a : localJoin T L) (v : Additive D.fullModule),
        e (Additive.ofMul
          (D.fullModule.normalizerMonoidHom
            ⟨a,D.maximalLocal_normalizes_fullModule
              ((sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)) a.property)⟩
            v.toMul)) =
          BinaryTensorThree.action (BinaryTensorThree.PointParabolic.tensorHom (q a)) (e v) := by
  let f := quietTensorLinearAction D e
  let p : localJoin T L →* BinaryTensorThree.Group :=
    f.codRestrict _ (fun a => himage ▸ (show f a ∈ f.range from ⟨a,rfl⟩))
  have hp : Function.Surjective p := by
    intro y
    obtain ⟨a,ha⟩ := himage.ge y.property
    exact ⟨a,Subtype.ext ha⟩
  let q := BinaryTensorThree.PointParabolic.actorEquiv.symm.toMonoidHom.comp p
  refine ⟨q,BinaryTensorThree.PointParabolic.actorEquiv.symm.surjective.comp hp,?_⟩
  intro a v
  rw [←BinaryTensorThree.PointParabolic.actorEquiv_apply]
  change _ = BinaryTensorThree.action
    (BinaryTensorThree.PointParabolic.actorEquiv
      (BinaryTensorThree.PointParabolic.actorEquiv.symm (p a))) (e v)
  rw [MulEquiv.apply_symm_apply]
  exact (quietTensorLinearAction_apply D e a v).symm

/-- Conjugate the given full tensor action to the source flag, without replacing
any prescribed nonidentity fixed vector of the original Sylow subgroup. -/
theorem quiet_tensor_marking_at_original_fixed_point
    (q : localJoin T L →* BinaryTensorThree.PointParabolic.Actor)
    (hq : Function.Surjective q)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (he : ∀ (a : localJoin T L) (v : Additive D.fullModule),
      e (Additive.ofMul
        (D.fullModule.normalizerMonoidHom
          ⟨a,D.maximalLocal_normalizes_fullModule
            ((sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)) a.property)⟩
          v.toMul)) =
        BinaryTensorThree.action (BinaryTensorThree.PointParabolic.tensorHom (q a)) (e v)) :
    ∃ (p : localJoin T L →* BinaryTensorThree.PointParabolic.Actor)
      (b : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space),
      Function.Surjective p ∧
      (∀ (a : localJoin T L) (v : Additive D.fullModule),
        b (Additive.ofMul
          (D.fullModule.normalizerMonoidHom
            ⟨a,D.maximalLocal_normalizes_fullModule
              ((sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)) a.property)⟩
            v.toMul)) =
          BinaryTensorThree.action (BinaryTensorThree.PointParabolic.tensorHom (p a)) (b v)) ∧
      (∀ (z : G) (hz : z ∈ D.fullModule), z ≠ 1 →
        (T : Subgroup G) ≤ centralizer ({z} : Set G) →
        b (Additive.ofMul ⟨z,hz⟩) = BinaryTensorThree.point) := by
  let H := localJoin T L
  let S := (T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)).mapSurjective hq
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq BinaryTensorThree.PointParabolic.Actor S
    Matrix.PSL3Two.WreathPair.sylow
  let p := (MulAut.conj c).toMonoidHom.comp q
  have hp : Function.Surjective p := (MulAut.conj c).surjective.comp hq
  let f := BinaryTensorThree.PointParabolic.tensorHom
  let b := e.trans (LinearEquiv.ofBijective (BinaryTensorThree.action (f c))
    (BinaryTensorThree.action.apply_bijective (f c)))
  have hb (a : H) (v : Additive D.fullModule) :
      b (Additive.ofMul
        (D.fullModule.normalizerMonoidHom
          ⟨a,D.maximalLocal_normalizes_fullModule
            ((sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)) a.property)⟩
          v.toMul)) = BinaryTensorThree.action (f (p a)) (b v) := by
    change BinaryTensorThree.action (f c) (e _) =
      BinaryTensorThree.action (f (c*q a*c⁻¹)) (BinaryTensorThree.action (f c) (e v))
    rw [he]
    simp only [map_mul,map_inv,Module.End.mul_apply]
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,mul_one]
    rw [f.map_mul]
  refine ⟨p,b,hp,hb,?_⟩
  intro z hz hz1 hzT
  have hmap : ((T : Subgroup G).subgroupOf H).map p = Matrix.PSL3Two.WreathPair.borel := by
    have hh := congrArg Sylow.toSubgroup hc
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hh
    dsimp only [S] at hh
    rw [Sylow.coe_mapSurjective, Sylow.coe_subtype, Matrix.PSL3Two.WreathPair.sylow_eq] at hh
    change (((T : Subgroup G).subgroupOf H).map q).map (MulAut.conj c).toMonoidHom =
      Matrix.PSL3Two.WreathPair.borel at hh
    simpa only [map_map] using hh
  have hfix : ∀ a ∈ Matrix.PSL3Two.WreathPair.borel,
      BinaryTensorThree.action (f a) (b (Additive.ofMul ⟨z,hz⟩)) = b (Additive.ofMul ⟨z,hz⟩) := by
    intro a ha
    obtain ⟨s,hs,rfl⟩ := hmap.ge ha
    have hz' : Additive.ofMul
        (D.fullModule.normalizerMonoidHom
          ⟨s,D.maximalLocal_normalizes_fullModule
            ((sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)) s.property)⟩
          ⟨z,hz⟩) = Additive.ofMul ⟨z,hz⟩ := by
      apply congrArg Additive.ofMul
      apply Subtype.ext
      change (s : G)*z*(s : G)⁻¹ = z
      have hsz : (s : G)*z = z*(s : G) := mem_centralizer_singleton_iff.mp (hzT hs)
      rw [hsz,mul_inv_cancel_right]
    exact (hb s (Additive.ofMul ⟨z,hz⟩)).symm.trans (congrArg b hz')
  rcases BinaryTensorThree.PointParabolic.sylow_fixed_eq_zero_or_point
      (b (Additive.ofMul ⟨z,hz⟩)) hfix with hz0 | hp
  · have hh := b.injective (hz0.trans b.map_zero.symm)
    exact (hz1 (congrArg (fun v : Additive D.fullModule => (v.toMul : G)) hh)).elim
  · exact hp

/-- The literal weak-closure statement at any prescribed nonidentity original
Sylow-fixed point; its pure-tensor marking is constructed, not assumed. -/
theorem quiet_tensor_weakClosure_two_at_original_fixed_point
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
    (q : localJoin T L →* BinaryTensorThree.PointParabolic.Actor)
    (hq : Function.Surjective q)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (he : ∀ (a : localJoin T L) (v : Additive D.fullModule),
      e (Additive.ofMul
        (D.fullModule.normalizerMonoidHom
          ⟨a,D.maximalLocal_normalizes_fullModule
            ((sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)) a.property)⟩
          v.toMul)) =
        BinaryTensorThree.action (BinaryTensorThree.PointParabolic.tensorHom (q a)) (e v))
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcore : D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (hr : (3 : ℕ∞) < globalR D.fullModule) :
    indexedWeakClosure D.fullModule (CentralizerSetup.S ⟨T,localOrbit T L,z⟩) 2 ≤
      centralizer (D.fullModule : Set G) := by
  obtain ⟨p,b,hp,hb,hpoint⟩ := quiet_tensor_marking_at_original_fixed_point D q hq e he
  exact quiet_original_tensor_weakClosure_two_of_marked_localJoin D hJ p hp b hb hzV
    (hpoint z hzV hz1 hzT) hzT hcore hr

/-- The source weak-closure application from recognition of the original
linear image, with its point, Sylow and radical markings all constructed. -/
theorem quiet_tensor_weakClosure_two_of_action_image
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (himage : (quietTensorLinearAction D e).range = BinaryTensorThree.tensorGroup)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcore : D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (hr : (3 : ℕ∞) < globalR D.fullModule) :
    indexedWeakClosure D.fullModule (CentralizerSetup.S ⟨T,localOrbit T L,z⟩) 2 ≤
      centralizer (D.fullModule : Set G) := by
  obtain ⟨q,hq,he⟩ := quiet_exists_tensor_marking_of_action_image D e himage
  exact quiet_tensor_weakClosure_two_at_original_fixed_point D hJ q hq e he hzV hz1 hzT hcore hr

/-- The original local-Thompson consumer with all coordinate choices
constructed from the actual linear image. The ambient 8.3.11--12 premises
and image recognition remain with the selected-module source argument. -/
theorem tensor_weakClosure_two_of_local_centralization_three_action_image
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (himage : (quietTensorLinearAction D e).range = BinaryTensorThree.tensorGroup)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcore : D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (hr : (3 : ℕ∞) < globalR D.fullModule) :
    indexedWeakClosure D.fullModule (CentralizerSetup.S ⟨T,localOrbit T L,z⟩) 2 ≤
      centralizer (D.fullModule : Set G) :=
  quiet_tensor_weakClosure_two_of_action_image D
    (full_thompson_centralizes_of_local_three D hn hd hJ) e himage hzV hz1 hzT hcore hr

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
