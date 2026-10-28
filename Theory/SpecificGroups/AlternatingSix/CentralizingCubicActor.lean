module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic
public import Theory.GroupTheory.SolvableOuterQuotient
/-!
# Cubic actors centralizing an alternating-six subgroup

Suppose K is an A₆ subgroup commuting with V. An element normalizing both
and inducing an automorphism of order three on V can be adjusted to centralize K
without changing that action. Its fourth power acts inner on K because the
outer automorphism quotient has order four. Multiplication by the inverse
inner conjugator leaves the action on V unchanged, and 4 is 1 modulo 3.

Source application: Aschbacher–Smith F.5.5, printed p.302, the elementary
residual-centralizer contradiction. No lift of order three is required.
-/
@[expose] public noncomputable section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

private theorem cubic_centralizing_actor_of_fourth_inner (V K : Subgroup G)
    (hKV : K ≤ centralizer (V : Set G))
    (hinner : ∀ a : MulAut K, ∃ k : K, a ^ 4 = MulAut.conj k)
    (g : normalizer (V : Set G)) (hgK : (g:G) ∈ normalizer (K : Set G))
    (hg3 : orderOf (V.normalizerMonoidHom g) = 3) :
    ∃ d : normalizer (V : Set G),
      (d:G) ∈ centralizer (K : Set G) ∧
      orderOf (V.normalizerMonoidHom d) = 3 := by
  let gK : normalizer (K : Set G) := ⟨g,hgK⟩
  obtain ⟨k,hk⟩ := hinner (K.normalizerMonoidHom gK)
  let kV : normalizer (V : Set G) :=
    ⟨k,centralizer_le_normalizer _ (hKV k.property)⟩
  have hkV : V.normalizerMonoidHom kV = 1 := by
    ext x
    change (k:G)*(x:G)*(k:G)⁻¹=(x:G)
    rw [←hKV k.property x x.property,mul_inv_cancel_right]
  let d : normalizer (V : Set G) := kV⁻¹*g^4
  refine ⟨d,?_,?_⟩
  · intro x hx
    have hxk := congrArg (fun a : MulAut K => (a ⟨x,hx⟩ : G)) hk
    rw [←map_pow] at hxk
    change (g:G)^4*x*((g:G)^4)⁻¹=(k:G)*x*(k:G)⁻¹ at hxk
    have he : (g:G)^4*x=(k:G)*x*(k:G)⁻¹*(g:G)^4 :=
      (mul_inv_eq_iff_eq_mul).mp hxk
    change x*((k:G)⁻¹*(g:G)^4)=((k:G)⁻¹*(g:G)^4)*x
    rw [mul_assoc,he]
    group
  · have he : V.normalizerMonoidHom d=V.normalizerMonoidHom g := by
      change V.normalizerMonoidHom (kV⁻¹*g^4)=_
      rw [map_mul,map_inv,hkV,inv_one,one_mul,map_pow]
      calc
        (V.normalizerMonoidHom g)^4=(V.normalizerMonoidHom g)^3*
          V.normalizerMonoidHom g := pow_succ _ 3
        _ = V.normalizerMonoidHom g := by
          rw [←hg3,pow_orderOf_eq_one,one_mul]
    rw [he,hg3]
end Subgroup
namespace AlternatingSix.ShadowLocal

theorem automorphism_fourth_inner (a : AutA6) : ∃ k : A6,a^4=MulAut.conj k := by
  have hcard : Nat.card (AutA6 ⧸ inner)=4 := inner_index
  have hp := pow_card_eq_one' (x := QuotientGroup.mk' inner a)
  rw [hcard,←map_pow] at hp
  obtain ⟨k,hk⟩ := (QuotientGroup.eq_one_iff _).mp hp
  exact ⟨k,hk.symm⟩
end AlternatingSix.ShadowLocal

namespace AlternatingSix
/-- Preserve the cubic action on V while removing the action on the commuting A₆. -/
theorem centralizing_cubic_actor {G : Type*} [Group G] (V K : Subgroup G)
    (eK : K ≃* alternatingGroup (Fin 6)) (hKV : K ≤ centralizer (V : Set G))
    (g : normalizer (V : Set G)) (hgK : (g:G) ∈ normalizer (K : Set G))
    (hg3 : orderOf (V.normalizerMonoidHom g) = 3) :
    ∃ d : normalizer (V : Set G),
      (d:G) ∈ centralizer (K : Set G) ∧
      orderOf (V.normalizerMonoidHom d) = 3 := by
  apply Subgroup.cubic_centralizing_actor_of_fourth_inner V K hKV ?_ g hgK hg3
  intro a
  apply (MulAut.congr_inner_iff eK (a^4)).mp
  rw [map_pow]
  exact ShadowLocal.automorphism_fourth_inner (MulAut.congr eK a)
end AlternatingSix
