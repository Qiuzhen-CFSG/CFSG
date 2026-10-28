module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorNormalizer
public import Theory.Representation.BinaryTensorThree.Irreducible

/-!
# The original seed and full automizer in the binary tensor row

Irreducibility of the tensor base makes the original nonzero homogeneous
seed equal to the local and full modules. Consequently its ambient
normalizer is the original maximal local subgroup, and the kernel of the
L₀T action is precisely O₂(L₀T). Normality of L₀ puts every full-normalizer
action in the computed tensor normalizer. The original exchanger already
supplies that whole image, giving equivariant coordinates on Aut_G(V).

The parameter consumer uses these coordinates on the actual automizer.
Recognition of the original tensor base, the strict r bound and the
point-core inclusion are still source obligations of the selected-module
owner. These results do not establish quiet tensor exclusion or fixed support.
Source: Aschbacher--Smith 3.2.6(2), H.4.4 and the opening of §8.3,
printed pp.581,383,723--724.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- Tensor irreducibility forces the original nonzero seed to be the whole
full module. No minimality or identification of the seed is assumed. -/
theorem quiet_tensor_seed_eq_fullModule
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range) :
    D.seed = D.fullModule := by
  have hSF : D.seed ≤ D.fullModule := (le_componentOrbit D.seed T).trans
    (le_componentOrbit D.moduleSubgroup D.maximalLocal)
  let A : AddSubgroup (Additive D.fullModule) := (D.seed.subgroupOf D.fullModule).toAddSubgroup
  let S : AddSubgroup BinaryTensorThree.Space := A.map e.toAddMonoidHom
  have hstable (g : BinaryTensorThree.Factor × BinaryTensorThree.Factor)
      (X : BinaryTensorThree.Space) (hX : X ∈ S) : BinaryTensorThree.baseAction g X ∈ S := by
    obtain ⟨v,hv,rfl⟩ := hX
    obtain ⟨a,ha,he⟩ := hbase.ge (show BinaryTensorThree.baseAction g ∈
      BinaryTensorThree.baseAction.range from ⟨g,rfl⟩)
    change BinaryTensorThree.baseAction g (e v) ∈ S
    rw [←he,quietTensorLinearAction_apply]
    refine ⟨_,?_,rfl⟩
    exact (mem_normalizer_iff.mp (D.orbit_normalizes_seed ha) _).mp hv
  rcases BinaryTensorThree.additive_invariant_eq_bot_or_top S hstable with hz | ht
  · exfalso
    apply D.seed_ne_bot
    apply bot_unique
    intro s hs
    let v : Additive D.fullModule := Additive.ofMul ⟨s,hSF hs⟩
    have hv : e v ∈ S := ⟨v,hs,rfl⟩
    rw [hz,AddSubgroup.mem_bot] at hv
    have h0 : v = 0 := e.injective (hv.trans e.map_zero.symm)
    exact congrArg (fun w : Additive D.fullModule => (w.toMul : G)) h0
  · apply le_antisymm hSF
    intro v hv
    have hh : e (Additive.ofMul (⟨v,hv⟩ : D.fullModule)) ∈ S := ht.symm ▸ AddSubgroup.mem_top _
    obtain ⟨w,hw,he⟩ := hh
    have he' : w = Additive.ofMul (⟨v,hv⟩ : D.fullModule) := e.injective he
    change (w.toMul : G) ∈ D.seed at hw
    have hh := congrArg (fun a : Additive D.fullModule => (a.toMul : G)) he'
    rwa [hh] at hw

/-- The original local module and full module coincide in the tensor row,
as used before the centralizer arguments of source §8.3. -/
theorem quiet_tensor_fullModule_eq_module
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range) :
    D.fullModule = D.moduleSubgroup :=
  le_antisymm ((quiet_tensor_seed_eq_fullModule D e hbase).symm.le.trans
    (le_componentOrbit D.seed T)) (le_componentOrbit D.moduleSubgroup D.maximalLocal)

/-- The normalizer in the tensor source is the actual ambient N_G(V). -/
theorem quiet_tensor_module_normalizer
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range) :
    normalizer (D.moduleSubgroup : Set G) = D.maximalLocal := by
  rw [←quiet_tensor_fullModule_eq_module D e hbase]
  exact source_fullModule_normalizer D

/-- The original tensor action has precisely the source two-core kernel. -/
theorem quiet_tensor_kernel_eq_twoCore
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range) :
    (quietTensorLinearAction D e).ker = pCore 2 (localJoin T L) := by
  rw [quietTensorLinearAction_ker,quiet_tensor_fullModule_eq_module D e hbase]
  exact local_module_kernel_eq_twoCore D hn


/-- The action of the full original normalizer in the same tensor coordinates. -/
def quietTensorNormalizerAction
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space) :
    normalizer (D.fullModule : Set G) →*
      (BinaryTensorThree.Space ≃ₗ[ZMod 2] BinaryTensorThree.Space) :=
  let ρ : Representation (ZMod 2) (normalizer (D.fullModule : Set G)) (Additive D.fullModule) :=
    (automizerRepresentation D.fullModule).comp
    D.fullModule.normalizerMonoidHom.rangeRestrict
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) BinaryTensorThree.Space).toMonoidHom.comp
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv e).toMonoidHom.comp ρ.asGroupHom)

theorem quietTensorNormalizerAction_apply
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (a : normalizer (D.fullModule : Set G)) (v : Additive D.fullModule) :
    quietTensorNormalizerAction D e a (e v) =
      e (Additive.ofMul (D.fullModule.normalizerMonoidHom a v.toMul)) := by
  change e (Additive.ofMul (D.fullModule.normalizerMonoidHom a
    (e.symm (e v)).toMul)) = _
  rw [e.symm_apply_apply]

/-- The full ambient automizer has exactly the same tensor image as L₀T.
Normality of L₀ and the computed linear normalizer exclude any larger image. -/
theorem quiet_tensor_normalizer_image
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range) :
    (quietTensorNormalizerAction D e).range = BinaryTensorThree.tensorGroup := by
  let N := normalizer (D.fullModule : Set G)
  let R := (localOrbit T L).subgroupOf N
  let f := quietTensorNormalizerAction D e
  have hHN : localJoin T L ≤ N :=
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)).trans
      D.maximalLocal_normalizes_fullModule
  have hact (a : localJoin T L) : f (inclusion hHN a) = quietTensorLinearAction D e a := by
    apply LinearEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := e.surjective w
    rw [quietTensorLinearAction_apply]
    exact quietTensorNormalizerAction_apply D e (inclusion hHN a) v
  have hrestrict : f.comp (inclusion hHN) = quietTensorLinearAction D e :=
    MonoidHom.ext hact
  have hN : N ≤ normalizer (localOrbit T L : Set G) := (source_fullModule_normalizer D).le
  let : R.Normal := normal_subgroupOf_of_le_normalizer hN
  have hb : R.map f = BinaryTensorThree.baseAction.range := by
    apply le_antisymm
    · rintro x ⟨a,ha,rfl⟩
      exact hbase.le ⟨⟨a,(show localOrbit T L ≤ localJoin T L from le_sup_left) ha⟩,ha,(hact _).symm⟩
    · intro x hx
      obtain ⟨a,ha,rfl⟩ := hbase.ge hx
      exact ⟨inclusion hHN a,ha,hact a⟩
  apply le_antisymm
  · have hh := R.le_normalizer_map f
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,hb,
      BinaryTensorThree.normalizer_baseAction_range] at hh
    exact hh
  · rw [←quiet_tensor_action_image_of_orbit_image D hn e hbase,←hrestrict]
    rintro x ⟨a,rfl⟩
    exact ⟨inclusion hHN a,rfl⟩

/-- Literal equivariant coordinates on Aut_G(V), with its action kernel
already removed by the original automizer construction. -/
theorem quiet_tensor_automizer_coordinates
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range) :
    ∃ f : Automizer D.fullModule ≃* BinaryTensorThree.Group,
      ∀ a v, e (automizerRepresentation D.fullModule a v) =
        BinaryTensorThree.action (f a) (e v) := by
  let N := normalizer (D.fullModule : Set G)
  let q := D.fullModule.normalizerMonoidHom.rangeRestrict
  let k : N →* BinaryTensorThree.Group := (quietTensorNormalizerAction D e).codRestrict
    BinaryTensorThree.tensorGroup (fun a =>
      (quiet_tensor_normalizer_image D hn e hbase).le ⟨a,rfl⟩)
  have hk : Function.Surjective k := by
    intro a
    obtain ⟨b,hb⟩ := (quiet_tensor_normalizer_image D hn e hbase).ge a.property
    exact ⟨b,Subtype.ext hb⟩
  obtain ⟨f,hf,he,hcomp⟩ := Representation.BinaryOffender.faithful_action_factor
    (automizerRepresentation D.fullModule) BinaryTensorThree.action
    (automizerRepresentation_injective D.fullModule) BinaryTensorThree.action_faithful
    q D.fullModule.normalizerMonoidHom.rangeRestrict_surjective k e
    (fun a v => (quietTensorNormalizerAction_apply D e a v).symm)
  have hfs : Function.Surjective f := by
    intro a
    obtain ⟨b,rfl⟩ := hk a
    exact ⟨q b,hcomp b⟩
  exact ⟨MulEquiv.ofBijective f ⟨hf,hfs⟩,he⟩

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
