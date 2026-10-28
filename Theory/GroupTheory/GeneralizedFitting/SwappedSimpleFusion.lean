module
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormFixedSeed

/-! An involution in the full norm diagonal of two exchanged simple
components is a coboundary for the swapping involution.  The source
prime-cover argument supplies the simplicity of the actual factors.
Source: Aschbacher–Smith 2.5.19(4), printed p.561. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
variable {G : Type*} [Group G]

theorem fixed_involution_fusion_of_exchanged_simple_pair
    {L K : Subgroup G} [IsSimpleGroup L] (t : G) (ht : t ^ 2 = 1)
    (hL : IsComponent G L) (hm : L.map (MulAut.conj t).toMonoidHom ≠ L)
    (hK : IsComponentIn K (centralizer ({t} : Set G)))
    (hKP : K ≤ L ⊔ L.map (MulAut.conj t).toMonoidHom)
    (k : G) (hk : k ∈ K) (hk2 : k ^ 2 = 1) : IsConj t (t * k) := by
  have hkt : k * t = t * k := mem_centralizer_singleton_iff.mp (hK.1 hk)
  have hnorm := NormPair.fixed_component_eq_norm hL hm ht hK hKP
  rw [hnorm] at hk
  obtain ⟨x,hx⟩ := hk
  have hx2 : x ^ 2 = 1 := NormPair.norm_injective_of_simple hL hm (by
    rw [map_pow,hx,hk2,map_one])
  have hxi : (x : G)⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [Subgroup.coe_pow,Subgroup.coe_one,pow_two,Subgroup.coe_mul] using congrArg Subtype.val hx2
  apply isConj_iff.mpr
  refine ⟨(x : G),?_⟩
  rw [← hkt,← hx,componentSwapNorm_apply,hxi]
  group
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
