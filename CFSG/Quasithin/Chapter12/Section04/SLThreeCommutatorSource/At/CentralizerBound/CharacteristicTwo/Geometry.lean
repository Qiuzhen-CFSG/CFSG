module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.Components.CubicAction
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.CharacteristicTwo.Action
public import Theory.Representation.SLThreeCentralExtension.HyperplaneStabilizer
public import Theory.GroupTheory.SubgroupCoverTransport
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.CharacteristicTwo.Contracts

/-!
# The original escaping L₃ hyperplane stabilizer

This is the same-G,T version of the corresponding CentralizerBound proof.
Its configuration carries only Structural1222At at the original Sylow;
every subgroup, action and relative component map is unchanged.

Choose the binary functional whose kernel is the original U. It is nonzero
on the fixed line. The dual stabilizer theorem gives a maximal subgroup of
SL₃(2) of index eight. The marked LT action identifies its full preimage
with the literal local normalizer of U. The existing cubic element in L
has prime order and acts nontrivially on U, so its cyclic action is faithful.

These are all the geometric hypotheses used by E.6.14 in the first case of
Aschbacher--Smith, 12.4.8, printed p.815. Block selection and the local index
argument remain separate obligations.
-/

public section
open CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G}
open ChapterE.Section06 ChapterE.Section06.InvariantSubspaces

/-- The literal normalizer of U in LT is maximal of index eight. -/
theorem Configuration.hyperplane_normalizer (c : Configuration T L V U) :
    localNormalizer (L ⊔ (T : Subgroup G)) U ⋖ L ⊔ (T : Subgroup G) ∧
      (localNormalizer (L ⊔ (T : Subgroup G)) U).relIndex (L ⊔ (T : Subgroup G)) = 8 := by
  classical
  let _ := c.chosen.elementary
  let E := c.extension
  let W : Submodule (ZMod 2) (Additive V) :=
    AddSubgroup.toZModSubmodule (n := 2) ((U.subgroupOf V).toAddSubgroup)
  have hg := escaping_subspaces c.hypothesis c.structural E
    c.fixed_nontrivial c.normalizer_action c.le_module c.corank c.escape
  obtain ⟨z,hz,hzU⟩ := SetLike.not_le_iff_exists.mp hg.2.1
  let zV : Additive V := Additive.ofMul ⟨z,hz.1⟩
  have hzW : zV ∉ W := hzU
  obtain ⟨f,hfz,hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hzW inferInstance
  have hf : f ≠ 0 := by intro he; exact hfz (he ▸ rfl)
  have hWker : W ≤ f.ker := by
    intro w hw
    have hh : f w ∈ W.map f := ⟨w,hw,rfl⟩
    change f w = 0
    simpa only [hfW,Submodule.mem_bot] using hh
  have hWdim : Module.finrank (ZMod 2) W = 3 := by
    let e : W ≃ U := {
      toFun w := ⟨w.val.toMul,w.property⟩
      invFun u := ⟨Additive.ofMul ⟨u,c.le_module u.property⟩,u.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    have hc : Nat.card W = 8 := (Nat.card_congr e).trans hg.1
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) (by simpa using hc)
  have hker : W = f.ker := by
    apply Submodule.eq_of_le_of_finrank_eq hWker
    have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    rw [module_finrank_four E c.fixed_nontrivial] at hk
    omega
  obtain ⟨S,hi,_,hmax,hS⟩ := SLThreeCentralExtension.dual_hyperplane_stabilizer E.action
    (module_finrank_four E c.fixed_nontrivial) zV
    (fun b => (E.mem_fixed_iff zV).mpr hz.2 b)
    (fun b hb => (involution_linear_plane E c.fixed_nontrivial b hb).1) f hfz
  obtain ⟨q,hq,hconj⟩ := c.exists_marked_join_action
  let A := L ⊔ (T : Subgroup G)
  have hstab : S.comap q = (localNormalizer A U).subgroupOf A := by
    ext n
    rw [mem_comap,hS]
    change f.comp (E.action (q n)) = f ↔ (n : G) ∈ A ∧ (n : G) ∈ normalizer (U : Set G)
    rw [and_iff_right n.property]
    constructor
    · intro he
      apply mem_normalizer_iff_map_conj_eq.mpr
      apply eq_of_le_of_card_ge
      · rintro y ⟨v,hv,rfl⟩
        let w : Additive V := Additive.ofMul ⟨v,c.le_module hv⟩
        have hw : w ∈ W := hv
        have hnw : E.action (q n) w ∈ W := by
          rw [hker] at hw ⊢
          change f (E.action (q n) w) = 0
          exact (LinearMap.congr_fun he w).trans hw
        change ((E.action (q n) w).toMul : G) ∈ U at hnw
        rw [hconj] at hnw
        exact hnw
      · rw [card_map_of_injective (MulAut.conj (n : G)).injective]
    · intro hn
      ext v
      have bit : ∀ x y : ZMod 2, (x=0 ↔ y=0) → x=y := by decide
      apply bit
      change f (E.action (q n) v) = 0 ↔ f v = 0
      change E.action (q n) v ∈ f.ker ↔ v ∈ f.ker
      rw [← hker]
      change ((E.action (q n) v).toMul : G) ∈ U ↔ (v.toMul : G) ∈ U
      rw [hconj]
      exact (mem_normalizer_iff.mp hn (v.toMul : G)).symm
  have hco : IsCoatom ((localNormalizer A U).subgroupOf A) :=
    hstab ▸ isCoatom_comap_of_surjective hq hmax
  have hcov := (covBy_map_subtype_iff A _ _).mpr hco.covBy_top
  have hm : ((localNormalizer A U).subgroupOf A).map A.subtype = localNormalizer A U :=
    map_subgroupOf_eq_of_le inf_le_left
  rw [hm,←MonoidHom.range_eq_map,range_subtype] at hcov
  refine ⟨hcov, ?_⟩
  change ((localNormalizer A U).subgroupOf A).index = 8
  rw [← hstab,index_comap_of_surjective S hq,hi]

/-- The actual order-three subgroup supplied inside L acts faithfully on U. -/
theorem Configuration.faithful_three (c : Configuration T L V U) : HasFaithfulThreeAction U := by
  obtain ⟨x,_,hx,hxn,hxc⟩ := c.exists_cubic_hyperplane_actor
  let A := zpowers x
  have hA : Nat.card A = 3 := (Nat.card_zpowers x).trans hx
  have hAN : A ≤ normalizer (U : Set G) := zpowers_le.mpr hxn
  let f : A →* MulAut U := U.normalizerMonoidHom.comp (inclusion hAN)
  refine ⟨A,hAN,hA,?_⟩
  change Function.Injective f
  apply f.ker_eq_bot_iff.mp
  let : IsSimpleGroup A := isSimpleGroup_of_prime_card hA
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with he | he
  · exact he
  · have hk : (⟨x,mem_zpowers x⟩ : A) ∈ f.ker := he ▸ mem_top _
    have hf : f ⟨x,mem_zpowers x⟩ = 1 := hk
    apply (hxc ?_).elim
    intro u hu
    have hh := congrArg (fun a : MulAut U => (a ⟨u,hu⟩ : G)) hf
    change x * u * x⁻¹ = u at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The complete stabilizer input to the literal E.6.14 application. -/
theorem Configuration.stabilizer_geometry (c : Configuration T L V U) :
    CharacteristicTwo.StabilizerGeometry T L U := by
  obtain ⟨hmax,hi⟩ := c.hyperplane_normalizer
  exact ⟨c.faithful_three,hmax,by rw [hi]; decide⟩

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound
