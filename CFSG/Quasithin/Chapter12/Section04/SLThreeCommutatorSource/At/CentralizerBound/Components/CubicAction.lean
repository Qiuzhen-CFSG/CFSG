module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.Preparation
public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Theory.GroupTheory.PrimeOrderLift
public import Theory.GroupTheory.PRegularLift

/-!
# A faithful cubic actor on the escaping L₃ hyperplane

This is the same-G,T version of the corresponding CentralizerBound proof.
Its configuration carries only Structural1222At at the original Sylow;
every subgroup, action and relative component map is unchanged.

The dual functional with kernel U has an odd-order stabilizer: an involution
fixing it would put the original fixed line in its displacement, hence in U.
The dual has order 16 and SL₃(2) has order 168, so orbit–stabilizer forces a
cubic in this stabilizer. A prime-regular lift through O₂(L) gives an actual
order-three element of L normalizing U; the pointwise stabilizer calculation
shows that it acts faithfully on U.

Source: Aschbacher–Smith, Lemma 12.4.8, printed p.815 (`refs/quasithin.pdf`).
-/

public section
open CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound

private theorem dual_cubic_stabilizer
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) BinaryLinearThree.Group W)
    (hdim : Module.finrank (ZMod 2) W = 4)
    (z : W) (hz : ∀ b, ρ b z = z)
    (hi : ∀ b, orderOf b = 2 →
      LinearMap.range (ρ b - LinearMap.id) = BinaryOffender.fixedSpace ρ (zpowers b))
    (f : Module.Dual (ZMod 2) W) (hf : f z ≠ 0) :
    ∃ b : BinaryLinearThree.Group, orderOf b = 3 ∧ f.comp (ρ b) = f := by
  classical
  let : MulAction BinaryLinearThree.Group (Module.Dual (ZMod 2) W) := {
    smul b φ := ρ.dual b φ
    one_smul φ := by
      change ρ.dual 1 φ = φ
      rw [map_one]; rfl
    mul_smul b c φ := by
      change ρ.dual (b*c) φ = ρ.dual b (ρ.dual c φ)
      rw [map_mul]; rfl }
  let S := MulAction.stabilizer BinaryLinearThree.Group f
  have hodd : ¬ 2 ∣ Nat.card S := by
    intro hdiv
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 2 hdiv
    have hb' : orderOf (b : BinaryLinearThree.Group) = 2 := (orderOf_coe b).trans hb
    have hfix : f.comp (ρ (b : BinaryLinearThree.Group)⁻¹) = f := b.property
    have hinv : (b : BinaryLinearThree.Group)⁻¹ = b := by
      have hpow : (b : BinaryLinearThree.Group) ^ 2 = 1 := by
        simpa only [hb'] using pow_orderOf_eq_one (b : BinaryLinearThree.Group)
      exact inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hpow)
    rw [hinv] at hfix
    have hzfix : z ∈ BinaryOffender.fixedSpace ρ (zpowers (b : BinaryLinearThree.Group)) :=
      fun a => hz a
    rw [← hi _ hb'] at hzfix
    obtain ⟨w, hw⟩ := hzfix
    apply hf
    rw [← hw]
    change f (ρ (b : BinaryLinearThree.Group) w - w) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (LinearMap.congr_fun hfix w)
  let : Finite (Module.Dual (ZMod 2) W) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) W => (f : W → ZMod 2)) DFunLike.coe_injective
  have hbound : S.index ≤ 16 := by
    rw [MulAction.index_stabilizer]
    have hc : Nat.card (Module.Dual (ZMod 2) W) = 16 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
        Subspace.dual_finrank_eq, hdim]
      decide
    exact hc ▸ Set.ncard_le_card _
  have hcard := S.card_mul_index
  rw [Matrix.PSL3Two.card_SL] at hcard
  have hdiv : S.index ∈ Nat.divisors 168 :=
    Nat.mem_divisors.mpr ⟨hcard ▸ dvd_mul_left _ _, by decide⟩
  have hd : Nat.divisors 168 = {1,2,3,4,6,7,8,12,14,21,24,28,42,56,84,168} := by decide
  rw [hd] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have hthree : 3 ∣ Nat.card S := by
    rcases hdiv with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals rw [h] at hcard
    all_goals omega
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' 3 hthree
  refine ⟨(b : BinaryLinearThree.Group)⁻¹, ?_, b.property⟩
  rw [orderOf_inv]
  exact (orderOf_coe b).trans hb


/-- An actual cubic element of L normalizes the escaping hyperplane and acts
nontrivially on it. Since its order is prime, its cyclic action is faithful. -/
theorem Configuration.exists_cubic_hyperplane_actor
    {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V U : Subgroup G}
    (c : Configuration T L V U) :
    ∃ x : G, x ∈ L ∧ orderOf x = 3 ∧
      x ∈ normalizer (U : Set G) ∧ x ∉ centralizer (U : Set G) := by
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
  obtain ⟨b,hb,hbf⟩ := dual_cubic_stabilizer E.action
    (module_finrank_four E c.fixed_nontrivial) zV
    (fun b => (E.mem_fixed_iff zV).mpr hz.2 b)
    (fun b hb => (involution_linear_plane E c.fixed_nontrivial b hb).1) f hfz
  let q : L →* BinaryLinearThree.Group :=
    E.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q :=
    E.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 q.ker := by
    change IsPGroup 2 (E.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))).ker
    rw [MonoidHom.ker_comp_of_injective _ _ E.quotientEquiv.injective,
      QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨x,hxo,hxb⟩ := q.exists_pRegular_lift hq 2 Nat.prime_two b (by rw [hb]; decide)
  have hx3 : orderOf x = 3 :=
    (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hk x
      (Nat.prime_two.coprime_iff_not_dvd.mpr hxo)).symm.trans (hxb ▸ hb)
  have hconj (v : Additive V) :
      ((E.action b v).toMul : G) = (x : G) * (v.toMul : G) * (x : G)⁻¹ := by
    rw [← hxb]
    exact E.conjugation x v
  have hmap : U.map (MulAut.conj (x : G)).toMonoidHom ≤ U := by
    rintro y ⟨v,hv,rfl⟩
    let w : Additive V := Additive.ofMul ⟨v,c.le_module hv⟩
    have hw : w ∈ W := hv
    have hbw : E.action b w ∈ W := by
      rw [hker] at hw ⊢
      change f (E.action b w) = 0
      exact (LinearMap.congr_fun hbf w).trans hw
    have he := hconj w
    change (x : G) * v * (x : G)⁻¹ ∈ U
    change ((E.action b w).toMul : G) ∈ U at hbw
    rw [he] at hbw
    exact hbw
  have hnorm : (x : G) ∈ normalizer (U : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge hmap
    rw [card_map_of_injective (MulAut.conj (x : G)).injective]
  refine ⟨x,x.property,(orderOf_coe x).trans hx3,hnorm,?_⟩
  intro hxU
  have hxV : (x : G) ∈ centralizer (V : Set G) :=
    hg.2.2.1.le ⟨c.chosen.normalizes x.property,hxU⟩
  have he : E.action b = E.action 1 := by
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [map_one]
    change ((E.action b v).toMul : G) = (v.toMul : G)
    rw [hconj,← hxV v.toMul v.toMul.property,mul_inv_cancel_right]
  have hb1 : b = 1 := action_injective E he
  rw [hb1,orderOf_one] at hb
  omega

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound
