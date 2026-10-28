module

public import Theory.GroupTheory.QuaternionCentralProductNineAction
public import Theory.GroupTheory.SpecificGroups.QuaternionEightCubicCentralizer
/-!
# Centralizers of independent cubics on a quaternion central product

An actor centralizing both independent cubic actions preserves each intrinsic
quaternion factor. On each factor its restriction is a power of the corresponding
cubic action. Matching the two powers leaves an actor centralizing the product.
This proves the local centralizer step in Aschbacher (1994), Lemma 45.7.
-/

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
private theorem factor_normalized_of_centralizes_cubic
    (B C : Subgroup G) (hB : Nonempty (B≃*QuaternionGroup 2))
    (hC : Nonempty (C≃*QuaternionGroup 2)) (hi : Nat.card (B⊓C : Subgroup G)=2)
    (hc : ∀b∈B,∀c∈C,b*c=c*b)
    (x g : G) (a : MulAut B) (ha : ∀b:B,(a b:G)=x*b*x⁻¹)
    (ha1 : a≠1) (hxC : x∈centralizer (C:Set G))
    (hg : g∈normalizer (B⊔C : Subgroup G)) (hgx : Commute g x) :
    g∈normalizer (B:Set G) := by
  have hj := mem_normalizer_iff_map_conj_eq.mp hg
  have hl : B.map (MulAut.conj g).toMonoidHom≤B⊔C := by
    rw [←hj]
    exact map_mono le_sup_left
  have hm : Nonempty ((B.map (MulAut.conj g).toMonoidHom)≃*QuaternionGroup 2) :=
    ⟨((MulAut.conj g).subgroupMap B).symm.trans hB.some⟩
  rcases quaternion_subgroup_eq_factor B C _ hB hC hi hc hm hl with he | he
  · exact mem_normalizer_iff_map_conj_eq.mpr he
  · exfalso
    apply ha1
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [ha]
    have hbC : g*(b:G)*g⁻¹∈C := he ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom b.property
    have hcomm : Commute (g*x*g⁻¹) (g*(b:G)*g⁻¹) := by
      rw [hgx.eq,mul_inv_cancel_right]
      exact (hxC _ hbC).symm
    exact (mul_inv_eq_iff_eq_mul.mpr (Commute.conj_iff g |>.mp hcomm).eq)

omit [Finite G] in
private theorem restriction_commutes (B : Subgroup G) (g x : G)
    (hg : g∈normalizer (B:Set G)) (a : MulAut B)
    (ha : ∀b:B,(a b:G)=x*b*x⁻¹) (hcomm : Commute g x) :
    Commute (B.normalizerMonoidHom ⟨g,hg⟩) a := by
  apply MulEquiv.ext
  intro b
  apply Subtype.ext
  change g*(a b:G)*g⁻¹ = (a (B.normalizerMonoidHom ⟨g,hg⟩ b):G)
  rw [ha,ha]
  exact DFunLike.congr_fun (hcomm.map (MulAut.conj : G→*MulAut G)).eq (b:G)

/-- An actor centralizing the independent cubics differs from one of them by
an element centralizing the whole quaternion central product. -/
public theorem QuaternionIndependentCubics.normalizer_inf_centralizer_le
    {B C : Subgroup G} (actors : QuaternionIndependentCubics B C)
    (hB : Nonempty (B≃*QuaternionGroup 2)) (hC : Nonempty (C≃*QuaternionGroup 2))
    (hi : Nat.card (B⊓C : Subgroup G)=2) (hc : ∀b∈B,∀c∈C,b*c=c*b) :
    normalizer (B⊔C : Subgroup G) ⊓ centralizer (actors.A:Set G) ≤
      actors.A ⊔ centralizer (B⊔C : Subgroup G) := by
  intro g hg
  have hgx : Commute g (actors.x:G) := (hg.2 _ actors.x.property).symm
  have hgy : Commute g (actors.y:G) := (hg.2 _ actors.y.property).symm
  have hgB := factor_normalized_of_centralizes_cubic B C hB hC hi hc
    actors.x g (actors.actionB actors.x) (actors.actionB_apply actors.x)
    actors.x_actionB_ne_one actors.x_centralizes hg.1 hgx
  have hgC := factor_normalized_of_centralizes_cubic C B hC hB
    (by simpa only [inf_comm] using hi) (fun c hc' b hb=>(hc b hb c hc').symm)
    actors.y g (actors.actionC actors.y) (actors.actionC_apply actors.y)
    actors.y_actionC_ne_one actors.y_centralizes (by rw [sup_comm]; exact hg.1) hgy
  have hx3 : actors.x^3=1 := by
    apply Subtype.ext
    simpa only [coe_pow,coe_one,actors.x_order] using pow_orderOf_eq_one (actors.x:G)
  have hy3 : actors.y^3=1 := by
    apply Subtype.ext
    simpa only [coe_pow,coe_one,actors.y_order] using pow_orderOf_eq_one (actors.y:G)
  obtain ⟨i,hiB⟩ := QuaternionGroup.exists_pow_eq_of_commute_cubic_of_equiv hB.some
    (actors.actionB actors.x) (B.normalizerMonoidHom ⟨g,hgB⟩)
    (by rw [←map_pow,hx3,map_one]) actors.x_actionB_ne_one
    (restriction_commutes B g actors.x hgB _ (actors.actionB_apply actors.x) hgx)
  obtain ⟨j,hjC⟩ := QuaternionGroup.exists_pow_eq_of_commute_cubic_of_equiv hC.some
    (actors.actionC actors.y) (C.normalizerMonoidHom ⟨g,hgC⟩)
    (by rw [←map_pow,hy3,map_one]) actors.y_actionC_ne_one
    (restriction_commutes C g actors.y hgC _ (actors.actionC_apply actors.y) hgy)
  let a : actors.A := actors.x^i.val*actors.y^j.val
  have haB : actors.actionB a=B.normalizerMonoidHom ⟨g,hgB⟩ := by
    rw [map_mul,map_pow,map_pow,actors.y_actionB_eq_one,one_pow,mul_one,hiB]
  have haC : actors.actionC a=C.normalizerMonoidHom ⟨g,hgC⟩ := by
    rw [map_mul,map_pow,map_pow,actors.x_actionC_eq_one,one_pow,one_mul,hjC]
  have heB (b:B) : (a:G)*b*(a:G)⁻¹=g*b*g⁻¹ := by
    rw [←actors.actionB_apply a,haB]
    rfl
  have heC (c:C) : (a:G)*c*(a:G)⁻¹=g*c*g⁻¹ := by
    rw [←actors.actionC_apply a,haC]
    rfl
  have hd : (a:G)⁻¹*g∈centralizer (B⊔C : Subgroup G) := by
    have hfix (b:G) (hb : (a:G)*b*(a:G)⁻¹=g*b*g⁻¹) :
        b*((a:G)⁻¹*g)=((a:G)⁻¹*g)*b := by
      have ht := congrArg (fun x:G=>(a:G)⁻¹*x*g) hb
      simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel_right,inv_mul_cancel,mul_one] using ht
    have hl : B⊔C≤centralizer {((a:G)⁻¹*g)} := sup_le
      (fun b hb=>mem_centralizer_singleton_iff.mpr (hfix b (heB ⟨b,hb⟩)))
      (fun c hc=>mem_centralizer_singleton_iff.mpr (hfix c (heC ⟨c,hc⟩)))
    exact fun b hb=>mem_centralizer_singleton_iff.mp (hl hb)
  have hm := (actors.A⊔centralizer (B⊔C : Subgroup G)).mul_mem
    (show (a:G)∈actors.A⊔centralizer (B⊔C : Subgroup G) from mem_sup_left a.property)
    (mem_sup_right hd)
  simpa only [mul_inv_cancel_left] using hm
end Subgroup
