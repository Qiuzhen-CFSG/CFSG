module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorMarking
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.ThompsonComparison
public import Theory.Representation.BinaryTensorThree.PointParabolic
public import Theory.GroupTheory.PResidual.SylowCentralizer

/-!
# Radical coordinates on the original tensor centralizer core

A surjective tensor marking of the original L₀T action identifies the
preimage of the pure-tensor stabilizer with C_{L₀T}(z). The residual/Sylow
identity proves this is the source's actual XT. Its two-core therefore maps
into the two marked line-parabolic radicals. Injectivity of their embedding
constructs the radical-coordinate homomorphism, preserving the original
module, action kernel and point.

The weak-closure application now needs only one marked L₀T action; neither
a separate Sylow map nor a radical map is assumed. Recognition of this
original tensor action, V ≤ O₂(C_G(z)), and r(G,V) > 3 remain genuine source
obligations in 3.2.6 and 8.3.11--12. Neither quiet tensor exclusion nor
FixedSupportRowsAt is asserted here. Their final discharge stays with the
selected-module owner, and final point control with its existing owner.
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

/-- The residual in the original centralizer setup, supplemented by T,
is the whole point centralizer inside L₀T. -/
theorem quiet_XT_eq_point_centralizer {z : G}
    (hz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    CentralizerSetup.XT ⟨T,localOrbit T L,z⟩ =
      localJoin T L ⊓ centralizer ({z} : Set G) :=
  embedded_pointResidual_sup_sylow T (localOrbit T L)
    (le_normalizer_componentOrbit L T) z hz

/-- A surjective marking of the original L₀T tensor action constructs the
radical coordinates on S = O₂(XT), preserving its original marked point.
No radical-coordinate map or point-parabolic identification is assumed. -/
theorem quiet_exists_original_radical_coordinates
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
    {z : G} (hzV : z ∈ D.fullModule)
    (hez : e (Additive.ofMul ⟨z,hzV⟩) = BinaryTensorThree.point)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let S := CentralizerSetup.S ⟨T,localOrbit T L,z⟩
    let hSN : S ≤ normalizer (D.fullModule : Set G) :=
      (CentralizerSetup.S_le_T ⟨T,localOrbit T L,z⟩).trans
        ((le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule)
    ∃ r : S →* BinaryTensorThree.Radical × BinaryTensorThree.Radical,
      ∀ (s : S) (v : Additive D.fullModule),
        e (Additive.ofMul
          (D.fullModule.normalizerMonoidHom ⟨s,hSN s.property⟩ v.toMul)) =
          BinaryTensorThree.action (BinaryTensorThree.radicalPair (r s)) (e v) := by
  dsimp only
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  have hXT : d.XT = localJoin T L ⊓ centralizer ({z} : Set G) :=
    quiet_XT_eq_point_centralizer (L := L) hzT
  have hXH : d.XT ≤ localJoin T L := hXT.le.trans inf_le_left
  have hSH : d.S ≤ localJoin T L := d.S_le_T.trans le_sup_right
  have hfix (a : localJoin T L) :
      q a ∈ BinaryTensorThree.PointParabolic.PairP ↔
        (a : G) ∈ centralizer ({z} : Set G) := by
    rw [← BinaryTensorThree.PointParabolic.fixes_point_iff]
    have hh := he a (Additive.ofMul ⟨z,hzV⟩)
    rw [hez] at hh
    constructor
    · intro hf
      have hz := e.injective (hh.trans (hf.trans hez.symm))
      have hz' := congrArg (fun v : Additive D.fullModule => (v.toMul : G)) hz
      change (a : G)*z*(a : G)⁻¹ = z at hz'
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hz')
    · intro ha
      have hz : Additive.ofMul
          (D.fullModule.normalizerMonoidHom
            ⟨a,D.maximalLocal_normalizes_fullModule
              ((sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)) a.property)⟩
            ⟨z,hzV⟩) = Additive.ofMul ⟨z,hzV⟩ := by
        apply congrArg Additive.ofMul
        apply Subtype.ext
        change (a : G)*z*(a : G)⁻¹ = z
        rw [mem_centralizer_singleton_iff.mp ha,mul_inv_cancel_right]
      exact hh.symm.trans ((congrArg e hz).trans hez)
  let f : d.XT →* BinaryTensorThree.PointParabolic.PairP :=
    (q.comp (inclusion hXH)).codRestrict _ (fun x =>
      (hfix (inclusion hXH x)).mpr ((hXT.le x.property).2))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,hx⟩ := hq y
    have hz : (x : G) ∈ centralizer ({z} : Set G) :=
      (hfix x).mp (hx ▸ y.property)
    refine ⟨⟨x,hXT.ge ⟨x.property,hz⟩⟩,?_⟩
    exact Subtype.ext hx
  have hcore : (pCore 2 d.XT).map f ≤ pCore 2 BinaryTensorThree.PointParabolic.PairP :=
    le_sSup ⟨(inferInstance : (pCore 2 d.XT).Normal).map _ hf,pCore_isPGroup.map f⟩
  let a : d.S →* BinaryTensorThree.Group :=
    BinaryTensorThree.PointParabolic.tensorHom.comp (q.comp (inclusion hSH))
  have ha (s : d.S) : a s ∈ BinaryTensorThree.radicalPair.range := by
    apply BinaryTensorThree.PointParabolic.core_tensor_mem_radical
    obtain ⟨x,hx,hxs⟩ := s.property
    refine ⟨f x,hcore (mem_map_of_mem f hx),?_⟩
    change q (inclusion hXH x) = q (inclusion hSH s)
    congr 1
    exact Subtype.ext hxs
  let r : d.S →* BinaryTensorThree.Radical × BinaryTensorThree.Radical :=
    (MonoidHom.ofInjective BinaryTensorThree.radicalPair_injective).symm.toMonoidHom.comp
      (a.codRestrict _ ha)
  have hr (s : d.S) : BinaryTensorThree.radicalPair (r s) = a s :=
    congrArg Subtype.val
      ((MonoidHom.ofInjective BinaryTensorThree.radicalPair_injective).apply_symm_apply
        ⟨a s,ha s⟩)
  refine ⟨r,fun s v => ?_⟩
  rw [hr]
  exact he (inclusion hSH s) v

/-- The original weak-closure consumer with both Sylow and radical
coordinates constructed from one marked L₀T action. The ambient point-core
inclusion and the strict global-r inequality remain source premises. -/
theorem quiet_original_tensor_weakClosure_two_of_marked_localJoin
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
    {z : G} (hzV : z ∈ D.fullModule)
    (hez : e (Additive.ofMul ⟨z,hzV⟩) = BinaryTensorThree.point)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcore : D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (hr : (3 : ℕ∞) < globalR D.fullModule) :
    indexedWeakClosure D.fullModule (CentralizerSetup.S ⟨T,localOrbit T L,z⟩) 2 ≤
      centralizer (D.fullModule : Set G) := by
  obtain ⟨r,her⟩ := quiet_exists_original_radical_coordinates D q hq e he hzV hez hzT
  let qT := BinaryTensorThree.PointParabolic.tensorHom.comp
    (q.comp (inclusion (show (T : Subgroup G) ≤ localJoin T L from le_sup_right)))
  exact quiet_original_tensor_weakClosure_two_of_original_action D hJ qT e
    (fun s v => he (inclusion le_sup_right s) v) hzV hcore hr r e her hez

/-- Apply the constructed original radical coordinates with only local
Thompson centralization, as in the source selection branch. -/
theorem tensor_weakClosure_two_of_local_centralization_three_marked_localJoin
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
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
    {z : G} (hzV : z ∈ D.fullModule)
    (hez : e (Additive.ofMul ⟨z,hzV⟩) = BinaryTensorThree.point)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcore : D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (hr : (3 : ℕ∞) < globalR D.fullModule) :
    indexedWeakClosure D.fullModule (CentralizerSetup.S ⟨T,localOrbit T L,z⟩) 2 ≤
      centralizer (D.fullModule : Set G) := by
  exact quiet_original_tensor_weakClosure_two_of_marked_localJoin D
    (full_thompson_centralizes_of_local_three D hn hd hJ) q hq e he hzV hez hzT hcore hr

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
