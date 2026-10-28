module
public import Theory.GroupTheory.QuaternionCentralProductHyperbolicFrame
public import Theory.GroupTheory.QuaternionCentralProductTransport

/-!
# Involution frames transported through intrinsic quaternion products

The explicit frame in Q₈ * Q₈ transfers to any intrinsic quaternion central
product once an ambient orbit carries the standard noncentral involution
to the marked one. It supplies the exact generating pair required by the
hyperbolic recognition input. Source: Aschbacher, *Sporadic Groups* (1994),45.3.
-/

open Subgroup
namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q]
open QuaternionCentralProduct

public theorem exists_hyperbolic_generators (d : QuaternionCentralProductData Q)
    (z u : Q) (hz : z ∈ center Q) (hz1 : z ≠ 1)
    (horbit : ∀ x : Q, orderOf x = 2 → x ∉ center Q →
      ∃ a : MulAut Q, a x = u) :
    ∃ a b : Q, a^2=1 ∧ b^2=1 ∧ Commute a u ∧ Commute b u ∧
      b*a=a*b*z ∧
      ∀ D : Subgroup Q, z ∈ D → u ∈ D → a ∈ D → b ∈ D →
        ∀ x : Q, Commute x u → x ∈ D := by
  obtain ⟨e⟩ := d.nonempty_model_equiv
  have hv2 : orderOf (e.symm frameU) = 2 := by
    rw [e.symm.orderOf_eq]
    exact orderOf_eq_prime frameU_square frameU_ne_one
  have hvZ : e.symm frameU ∉ center Q := by
    intro hh
    apply frameU_not_central
    rw [← e.apply_symm_apply frameU]
    exact (centerCongr e ⟨e.symm frameU,hh⟩).property
  obtain ⟨α,hα⟩ := horbit _ hv2 hvZ
  let f := e.symm.trans α
  have hfu : f frameU = u := hα
  have hfz : f frameZ = z := by
    have hfZ : f frameZ ∈ center Q := (centerCongr f ⟨frameZ,frameZ_central⟩).property
    have hf1 : f frameZ ≠ 1 := by
      intro he
      exact frameZ_ne_one (f.injective (he.trans f.map_one.symm))
    obtain ⟨w,_,hw⟩ := (Nat.card_eq_two_iff' (1 : center Q)).mp d.center_card
    exact congrArg Subtype.val ((hw ⟨f frameZ,hfZ⟩ (fun he => hf1 (congrArg Subtype.val he))).trans
      (hw ⟨z,hz⟩ (fun he => hz1 (congrArg Subtype.val he))).symm)
  refine ⟨f frameB,f frameA,?_,?_,?_,?_,?_,?_⟩
  · rw [← map_pow,frameB_square,map_one]
  · rw [← map_pow,frameA_square,map_one]
  · rw [← hfu]
    exact frameB_commute.map f.toMonoidHom
  · rw [← hfu]
    exact frameA_commute.map f.toMonoidHom
  · rw [← hfz,← map_mul,← map_mul,← map_mul,frame_swap]
  · intro D hzD huD haD hbD x hx
    have hx' : Commute (f.symm x) frameU := by
      apply f.injective
      simpa only [map_mul,f.apply_symm_apply,hfu] using hx.eq
    obtain ⟨a,b,c,d,he⟩ := frame_centralizer_words (f.symm x) hx'
    have he' := congrArg f he
    simp only [map_mul,map_pow,f.apply_symm_apply,hfz,hfu] at he'
    rw [he']
    exact D.mul_mem (D.mul_mem (D.mul_mem (D.pow_mem hzD _) (D.pow_mem huD _))
      (D.pow_mem hbD _)) (D.pow_mem haD _)

end Subgroup.QuaternionCentralProductData
