module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.WeakClosure
public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.InvolutionOrbit

/-!
# Fusion and actual normalizer transitivity in the source planes

The three genuine reflection words move every root-product involution into
the original core. The original core fusion and weak closure then give actual
normalizer conjugators between every two nonidentity points of each plane.
Source: Aschbacher, Sporadic Groups (1994), 45.3(4),45.5–45.6, pp.243–244.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z:G}
namespace CentralizerHypothesis
variable (h : CentralizerHypothesis z)
include h in
theorem core_involution_fused_all (x:G) (hx:x∈core z) (hx2:orderOf x=2) : IsConj z x := by
  by_cases hxZ:x∈zpowers z
  · have hc : Nat.card (zpowers z)=2 := by rw [Nat.card_zpowers,h.involution]
    have he := (Nat.card_eq_two_iff' (1:zpowers z)).mp hc
    obtain ⟨a,ha,hall⟩ := he
    have hxne:x≠1 := by intro he; simp [he] at hx2
    have hzne:z≠1 := by intro he; have hh:=h.involution; simp [he] at hh
    have hx':(⟨x,hxZ⟩:zpowers z)=a := (hall ⟨x,hxZ⟩) (fun he=>hxne (congrArg Subtype.val he))
    have hz':(⟨z,mem_zpowers z⟩:zpowers z)=a := (hall ⟨z,mem_zpowers z⟩) (fun he=>hzne (congrArg Subtype.val he))
    have he : z=x := congrArg Subtype.val (hz'.trans hx'.symm)
    rw [←he]
  · exact h.core_involution_fused x hx hx2 hxZ
end CentralizerHypothesis
namespace RootPair
variable (P:RootPair z)
theorem R_involution_fused (h:IsType z) (x:G) (hx:x∈P.R) (hx2:orderOf x=2) : IsConj z x := by
  obtain ⟨a,_,b,_,hw⟩:=P.exists_involution_first_factor_words h
  have hxpow:x^2=1 := hx2 ▸ pow_orderOf_eq_one x
  rcases hw x hx hxpow with hc | hc | hc
  · exact h.toCentralizerHypothesis.core_involution_fused_all x hc.1 hx2
  · have he : IsConj x (b*x*b⁻¹) := isConj_iff.mpr ⟨b,rfl⟩
    exact (h.toCentralizerHypothesis.core_involution_fused_all _ hc.1 ((MulAut.conj b).orderOf_eq x |>.trans hx2)).trans he.symm
  · have he : IsConj x ((b*a)*x*(b*a)⁻¹) := isConj_iff.mpr ⟨b*a,rfl⟩
    exact (h.toCentralizerHypothesis.core_involution_fused_all _ hc.1 ((MulAut.conj (b*a)).orderOf_eq x |>.trans hx2)).trans he.symm

theorem plane_nonidentity_fused (h:IsType z) (V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16) (x:G) (hx:x∈V) (hxne:x≠1) :
    IsConj z x := by
  let := hV.2.1
  have hx2 : x^2=1 := elemPow_eq_one_of_isElementaryAbelian x hx
  exact P.R_involution_fused h x (P.large_elementary_le_R h V hV.1 hV.2.2.ge hx)
    (orderOf_eq_prime hx2 hxne)

theorem plane_nonidentity_transitive (h:IsType z) (V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16)
    (x y:G) (hx:x∈V) (hy:y∈V) (hxne:x≠1) (hyne:y≠1) :
    ∃ n∈normalizer (V:Set G),n*x*n⁻¹=y := by
  exact P.plane_controls_fusion h V hV hx hy
    ((P.plane_nonidentity_fused h V hV x hx hxne).symm.trans
      (P.plane_nonidentity_fused h V hV y hy hyne))
end RootPair
end Theory.GroupTheory.Recognition.UnitaryFourThree
