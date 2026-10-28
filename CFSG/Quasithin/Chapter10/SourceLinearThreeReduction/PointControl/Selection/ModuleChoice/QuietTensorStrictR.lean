module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorSmallCentralizer
public import Theory.Representation.BinaryTensorThree.NearOffenderFixedSpaces
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneThompson
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.Source

/-!
# The strict global-r bound for the original binary tensor

A moving higher-Thompson generator fixing a subspace of corank at most
three is a near-offender. The actual tensor geometry puts a conjugate of
the controlled plane-radical four-space in that subspace. Lifting its
conjugator through the original full action forces the ambient centralizer
into the original maximal local subgroup.

The small-subspace action has odd Cartan parameter one, and the full
ambient action kernel is a two-group by 8.3.10(2). E.6.27 therefore rules
out an escaping subspace of corank three, giving r(G,V)>3. The Source
application discharges the ambient equalities and plane-centralizer bound;
actual tensor coordinates and base-image recognition remain explicit.

Source: Aschbacher--Smith 8.3.11, printed p.726 (refs/quasithin.pdf),
using H.4.10(3), H.4.12(3), E.6.27 and the preceding 8.3.8,8.3.10(2).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Representation.BinaryOffender
open ChapterB ChapterE.Section06 ChapterE.Section06.FixedPointBounds
open BinaryTensorThree.PlaneFixed
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

private theorem full_hypothesis :
    HypothesisE61 KnownSimple.IsKnownSimple T D.maximalLocal D.fullModule := by
  have hu := D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)
  have hTM : (T : Subgroup G) ≤ D.maximalLocal := le_sup_right.trans hu.2.1
  have hVN := D.maximalLocal_normalizes_fullModule
  have hVT := D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D)
  refine ⟨D.simpleQTKE,hu.1,hTM,?_,inferInstance,hVT,
    (normal_subgroupOf_iff_le_normalizer hVT).mpr (hTM.trans hVN),?_,?_⟩
  · intro he
    exact D.module_ne_bot (bot_unique ((le_componentOrbit D.moduleSubgroup D.maximalLocal).trans_eq he))
  · intro g hg
    exact Or.inr (mem_normalizer_iff_map_conj_eq.mp (hVN hg))
  · intro N hN hle
    apply hu.2.2 N hN
    apply le_trans _ hle
    exact le_inf (le_inf hu.2.1 (hu.2.1.trans hVN))
      (source_join_normalizes_full_sylow_centralizer D (source_module_nonsolvable_uniqueness D))

private theorem full_coordinates
    (hM : D.maximalLocal = localJoin T L)
    (q : localJoin T L →* Actor) (hq : Function.Surjective q)
    (b : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hb : ∀ (a : localJoin T L) (v : Additive D.fullModule),
      quietTensorLinearAction D b a (b v) =
        BinaryTensorThree.action (BinaryTensorThree.PointParabolic.tensorHom (q a)) (b v)) :
    ∃ f : Automizer D.fullModule ≃* BinaryTensorThree.Group,
      ∀ a v, b (automizerRepresentation D.fullModule a v) =
        BinaryTensorThree.action (f a) (b v) := by
  have hHN : localJoin T L ≤ normalizer (D.fullModule : Set G) :=
    hM.symm.le.trans D.maximalLocal_normalizes_fullModule
  let a : localJoin T L →* Automizer D.fullModule :=
    D.fullModule.normalizerMonoidHom.rangeRestrict.comp (inclusion hHN)
  have ha : Function.Surjective a := by
    intro x
    obtain ⟨n,hn⟩ := D.fullModule.normalizerMonoidHom.rangeRestrict_surjective x
    exact ⟨⟨n,hM.le ((source_fullModule_normalizer D).le n.property)⟩,hn⟩
  let k := BinaryTensorThree.PointParabolic.tensorHom.comp q
  have hk : Function.Surjective k := by
    intro x
    obtain ⟨c,hc⟩ := BinaryTensorThree.PointParabolic.actorEquiv.surjective x
    obtain ⟨d,hd⟩ := hq c
    refine ⟨d,?_⟩
    change BinaryTensorThree.PointParabolic.tensorHom (q d) = x
    rw [hd,←BinaryTensorThree.PointParabolic.actorEquiv_apply,hc]
  obtain ⟨f,hf,he,hcomp⟩ := faithful_action_factor
    (automizerRepresentation D.fullModule) BinaryTensorThree.action
    (automizerRepresentation_injective D.fullModule) BinaryTensorThree.action_faithful
    a ha k b (by
      intro c v
      have hh := hb c v
      rw [quietTensorLinearAction_apply] at hh
      exact hh)
  have hsur : Function.Surjective f := by
    intro x
    obtain ⟨c,rfl⟩ := hk x
    exact ⟨a c,hcomp c⟩
  exact ⟨MulEquiv.ofBijective f ⟨hf,hsur⟩,he⟩

private theorem fixed_six_space
    {U : Subgroup G} (hUV : U ≤ D.fullModule) (hc : subgroupCorank D.fullModule U ≤ 3)
    (b : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space) :
    ∃ W : Submodule (ZMod 2) BinaryTensorThree.Space,
      6 ≤ Module.finrank (ZMod 2) W ∧
      ∀ v : Additive D.fullModule, b v ∈ W ↔ (v.toMul : G) ∈ U := by
  let S : Submodule (ZMod 2) (Additive D.fullModule) :=
    AddSubgroup.toZModSubmodule 2 (U.subgroupOf D.fullModule).toAddSubgroup
  let W := S.map b.toLinearMap
  have hm (v : Additive D.fullModule) : b v ∈ W ↔ (v.toMul : G) ∈ U := by
    constructor
    · rintro ⟨w,hw,he⟩
      exact b.injective he ▸ hw
    · intro hv
      exact ⟨v,hv,rfl⟩
  let eS : S ≃ U :=
    { toFun := fun v => ⟨v.val.toMul,v.property⟩
      invFun := fun u => ⟨Additive.ofMul ⟨u,hUV u.property⟩,u.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hs : Module.finrank (ZMod 2) S = rank U := by
    rw [rank,←Nat.card_congr eS,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      Nat.log_pow Nat.one_lt_two]
  have hw : Module.finrank (ZMod 2) S = Module.finrank (ZMod 2) W :=
    (S.equivMapOfInjective b.toLinearMap b.injective).finrank_eq
  have hdim : rank D.fullModule=9 := by
    rw [rank,show Nat.card D.fullModule = Nat.card (Additive D.fullModule) from rfl,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,b.finrank_eq,
      Module.finrank_matrix]
    norm_num
  have hd := offender_corank_add (W := D.fullModule) (A := U) bot_le hUV
  have hd' : rank D.fullModule = rank U + subgroupCorank D.fullModule U := by
    simpa only [subgroupCorank,relIndex_bot_left,rank,Nat.add_comm] using hd
  exact ⟨W,by omega,hm⟩

/-- A moving higher-Thompson generator fixing U forces its ambient centralizer
into M, by lifting the actual tensor conjugator of the controlled four-space. -/
theorem quiet_tensor_near_fixed_centralizer_le
    (hM : D.maximalLocal = localJoin T L)
    (q : localJoin T L →* Actor) (hq : Function.Surjective q)
    (b : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hb : ∀ (a : localJoin T L) (v : Additive D.fullModule),
      quietTensorLinearAction D b a (b v) =
        BinaryTensorThree.action (BinaryTensorThree.PointParabolic.tensorHom (q a)) (b v))
    (hcontrol : centralizer (originalFixed D.fullModule (localJoin T L) q : Set G) ≤ D.maximalLocal)
    {U A : Subgroup G} (hUV : U ≤ D.fullModule) (hc : subgroupCorank D.fullModule U ≤ 3)
    (hA : A ∈ thompsonFamily (D.maximalLocal ⊓ centralizer (U : Set G)) 1)
    (hmove : ¬ A ≤ centralizer (D.fullModule : Set G)) :
    centralizer (U : Set G) ≤ D.maximalLocal := by
  let V := D.fullModule
  have hAN : A ≤ normalizer (V : Set G) :=
    (hA.1.trans inf_le_left).trans D.maximalLocal_normalizes_fullModule
  have hVX : V ≤ D.maximalLocal ⊓ centralizer (U : Set G) :=
    le_inf ((D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D)).trans
      (le_normalizer_componentOrbit L T)) (V.le_centralizer.trans (centralizer_le hUV))
  let : IsElementaryAbelian 2 A := hA.2.1
  let I := inducedAutomizer V A
  let : IsElementaryAbelian 2 I := inducedAutomizer_elementary V A hAN
  have hI : IsElementaryTwo I := ⟨fun hz => hmove ((inducedAutomizer_eq_bot_iff hAN).mp hz),inferInstance⟩
  have hnear := Chapter7.NormalizedSource.thompson_family_fixedCodim_le V _ hVX
    (inf_le_left.trans D.maximalLocal_normalizes_fullModule) A hA
  obtain ⟨f,hf⟩ := full_coordinates D hM q hq b hb
  let B := I.map f.toMonoidHom
  have hB : IsElementaryTwo B :=
    ⟨fun hz => hI.1 ((map_eq_bot_iff_of_injective I f.injective).mp hz),IsElementaryAbelian.map _⟩
  have hcod := fixedCodim_map_equivariant (automizerRepresentation V)
    BinaryTensorThree.action f.toMonoidHom b hf I
  have hnearB : fixedCodim BinaryTensorThree.action B ≤ rank B+1 := by
    rw [←hcod,rank_map_injective _ f.injective]
    exact hnear
  obtain ⟨W,hW,hm⟩ := fixed_six_space D hUV hc b
  have hfix : W ≤ fixedSpace BinaryTensorThree.action B := by
    intro X hX a
    obtain ⟨v,rfl⟩ := b.surjective X
    obtain ⟨c,hc,he⟩ := a.property
    change BinaryTensorThree.action a.val (b v) = b v
    rw [←he]
    change BinaryTensorThree.action (f c) (b v) = b v
    rw [←hf]
    have hv := (mem_fixedSpace_inducedAutomizer V A hAN v).mpr
      (le_centralizer_iff.mp (hA.1.trans inf_le_right) ((hm v).mp hX))
    exact congrArg b (hv ⟨c,hc⟩)
  obtain ⟨g,hg⟩ := BinaryTensorThree.near_offender_fixed_contains_square B hB hnearB W hW hfix
  obtain ⟨c,hcg⟩ := BinaryTensorThree.PointParabolic.actorEquiv.surjective g
  obtain ⟨k,hk⟩ := hq c
  have hkg : BinaryTensorThree.PointParabolic.tensorHom (q k) = g := by
    rw [hk,←BinaryTensorThree.PointParabolic.actorEquiv_apply,hcg]
  have hHN : localJoin T L ≤ normalizer (V : Set G) :=
    hM.symm.le.trans D.maximalLocal_normalizes_fullModule
  have hequiv (a : localJoin T L) (v : Additive V) :
      b (Additive.ofMul (V.normalizerMonoidHom ⟨a,hHN a.property⟩ v.toMul)) =
        BinaryTensorThree.action (BinaryTensorThree.PointParabolic.tensorHom (q a)) (b v) := by
    rw [←quietTensorLinearAction_apply]
    exact hb a v
  let F := originalFixed V (localJoin T L) q
  have hFU : F.map (MulAut.conj (k : G)).toMonoidHom ≤ U := by
    rintro _ ⟨x,hx,rfl⟩
    let v : Additive V := Additive.ofMul ⟨x,hx.1⟩
    have hs : b v ∈ BinaryTensorThree.PlaneFixed.square :=
      (mem_originalFixed V (localJoin T L) hHN q hq b hequiv v.toMul).mp hx
    have hh := hg (b v) hs
    rw [←hkg,←hequiv] at hh
    exact (hm _).mp hh
  intro x hx
  have hxc : (k : G)⁻¹*x*k ∈ centralizer (F : Set G) := by
    intro y hy
    have hh := hx ((MulAut.conj (k : G)) y) (hFU (mem_map_of_mem _ hy))
    have hc := congrArg (MulAut.conj (k : G)⁻¹) hh
    simpa only [map_mul,MulAut.conj_apply,mul_assoc,inv_mul_cancel_left,
      mul_inv_cancel_left,inv_inv,inv_mul_cancel,mul_inv_cancel,mul_one,one_mul] using hc
  have hkm : (k : G) ∈ D.maximalLocal := hM.symm.le k.property
  have hh := D.maximalLocal.mul_mem
    (D.maximalLocal.mul_mem hkm (hcontrol hxc)) (D.maximalLocal.inv_mem hkm)
  simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using hh

/-- The strict source bound r(G,V)>3, from the proved ambient equalities
and the controlled original plane-radical fixed subgroup. -/
theorem quiet_tensor_strictR
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    (hM : D.maximalLocal = localJoin T L)
    (hk : IsPGroup 2 (centralizer (D.fullModule.subgroupOf D.maximalLocal : Set D.maximalLocal)))
    (q : localJoin T L →* Actor) (hq : Function.Surjective q)
    (b : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hb : ∀ (a : localJoin T L) (v : Additive D.fullModule),
      quietTensorLinearAction D b a (b v) =
        BinaryTensorThree.action (BinaryTensorThree.PointParabolic.tensorHom (q a)) (b v))
    (hcontrol : centralizer (originalFixed D.fullModule (localJoin T L) q : Set G) ≤ D.maximalLocal) :
    (3 : ℕ∞) < globalR D.fullModule := by
  have hr := (quiet_tensor_source_parameters D hn e hbase).2.1
  apply lt_of_le_of_ne hr
  intro he
  obtain ⟨U,hUV,hescape,hcor⟩ := globalR_attained (V := D.fullModule)
    (by rw [←he]; decide)
  have hc : subgroupCorank D.fullModule U = 3 := by exact_mod_cast hcor.trans he.symm
  have hUne : U ≠ ⊥ := by
    intro hz
    rw [hz,corank_bot,e.finrank_eq,Module.finrank_matrix] at hc
    norm_num at hc
  have h := full_hypothesis D
  have hN : D.maximalLocal ⊓ centralizer (U : Set G) ≤ normalizer (D.fullModule : Set G) :=
    inf_le_left.trans D.maximalLocal_normalizes_fullModule
  have hJ : thompsonJ (D.maximalLocal ⊓ centralizer (U : Set G)) 1 ≤
      D.maximalLocal ⊓ centralizer (D.fullModule : Set G) := by
    refine le_inf ((thompsonJ_le _ _).trans inf_le_left) ?_
    apply sSup_le
    intro A hA
    by_contra hmove
    have hh := quiet_tensor_near_fixed_centralizer_le D hM q hq b hb hcontrol hUV hc.le hA hmove
    exact hescape ((h.centralizer_le_iff hUne hUV).mp hh)
  have hp : IsPGroup 2 (D.maximalLocal ⊓ centralizer (D.fullModule : Set G) : Subgroup G) :=
    quiet_tensor_small_local_centralizer_isTwoGroup D hn e hbase hk le_rfl
      (by simp [subgroupCorank])
  have hodd (X : Subgroup G) (hX : X ≠ ⊥)
      (hle : X ≤ D.maximalLocal ⊓ centralizer (D.fullModule : Set G))
      (ho : Odd (Nat.card X)) : normalizer (X : Set G) ≤ D.maximalLocal := by
    obtain ⟨n,hn⟩ := (hp.to_le hle).exists_card_eq
    have hn0 : n = 0 := by
      rw [hn] at ho
      by_contra hne
      exact (by decide : ¬ Odd (2 : ℕ)) ((Nat.odd_pow_iff hne).mp ho)
    have hcard : Nat.card X = 1 := by rw [hn,hn0,pow_zero]
    exact (hX (Subgroup.card_eq_one.mp hcard)).elim
  have hsmall := quiet_tensor_small_fixed_nPrime_eq_one D hn e hbase hUV hN inf_le_right hc.le
  have hC := source_proposition_E_6_27 h hUne hUV (j := 1) (by decide)
    ((by decide : (1 : ℕ∞)<3).trans_le hr) hsmall.le hJ hodd
  exact hescape ((h.centralizer_le_iff hUne hUV).mp hC)

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
