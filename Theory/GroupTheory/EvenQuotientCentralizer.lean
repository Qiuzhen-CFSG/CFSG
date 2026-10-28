module
public import Theory.GroupTheory.CentralCoprimeLiftUnique
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.ElementaryAbelian.Basic
/-! A nontrivial elementary displacement of a cubic lying in a quasisimple
subgroup survives its central two-core quotient. Uniqueness of coprime torsion
lifts proves this without any splitting or multiplier theorem. If the
normalized elementary group and cubic centralize L, this produces an actual
involution in the centralizer of its quotient image.
Source application: Aschbacher--Smith 2.4.25, printed p.543. -/
public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace Theory.GroupTheory
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]

omit [Finite D] in
theorem even_quotient_centralizer_of_moved_elementary
    (K L U : Subgroup G) [IsQuasisimple K]
    (_hLK : L ≤ K) (hUK : U ≤ normalizer (K : Set G))
    (hUL : U ≤ centralizer (L : Set G)) (hU : IsElementaryAbelian 2 U)
    (b : K) (hb : orderOf b = 3) (hbL : (b : G) ∈ centralizer (L : Set G))
    (hbU : ¬ (b : G) ∈ centralizer (U : Set G))
    (hbN : (b : G) ∈ normalizer (U : Set G))
    (e : (K ⧸ pCore 2 K) ≃* D) :
    2 ∣ Nat.card (centralizer ((L.subgroupOf K).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) : Set D)) := by
  classical
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hker : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hkc : q.ker ≤ center K := hker ▸ IsQuasisimple.pCore_le_center 2
  have hkp : IsPGroup 2 q.ker := hker ▸ pCore_isPGroup
  have hbp : b^3=1 := hb ▸ pow_orderOf_eq_one b
  have hnot : ∃ u : U, ¬ Commute (u : G) (b : G) := by
    by_contra hh
    push Not at hh
    apply hbU
    intro u hu
    exact hh ⟨u,hu⟩
  obtain ⟨u,hu⟩ := hnot
  let b' : K := ⟨u * (b : G) * u⁻¹,
    (mem_normalizer_iff.mp (hUK u.property) b).mp b.property⟩
  have hb'p : b'^3=1 := by
    let f := K.normalizerMonoidHom ⟨(u:G),hUK u.property⟩
    change (f b)^3=1
    rw [←map_pow,hbp,map_one]
  have hne : q (b' * b⁻¹) ≠ 1 := by
    intro hh
    have heq : q b'=q b := by
      rw [map_mul,map_inv] at hh
      exact mul_inv_eq_one.mp hh
    have heq' := q.eq_of_map_eq_of_pow_eq_one_of_central_pgroup_ker hkc hkp
      (by decide : Nat.Coprime 2 3) heq hb'p hbp
    have heqG := congrArg K.subtype heq'
    change (u:G)*(b:G)*(u:G)⁻¹=(b:G) at heqG
    exact hu (mul_inv_eq_iff_eq_mul.mp heqG)
  have hcU : ((b' * b⁻¹ : K):G) ∈ U := by
    change ⁅(u:G),(b:G)⁆ ∈ U
    exact (le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hbN))
      (commutator_mem_commutator u.property (mem_zpowers (b:G)))
  have hpow : (b' * b⁻¹)^2=1 := by
    have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hU.exponent_dvd_p
      (⟨_,hcU⟩ : U)
    exact Subtype.ext (congrArg U.subtype hh)
  let C := centralizer ((L.subgroupOf K).map q : Set D)
  have hcC : q (b' * b⁻¹) ∈ C := by
    rintro _ ⟨l,hl,rfl⟩
    have hb'C : (b':G) ∈ centralizer (L : Set G) :=
      (centralizer (L:Set G)).mul_mem
        ((centralizer (L:Set G)).mul_mem (hUL u.property) hbL)
        ((centralizer (L:Set G)).inv_mem (hUL u.property))
    have hc := (centralizer (L:Set G)).mul_mem hb'C
      ((centralizer (L:Set G)).inv_mem hbL)
    have hh : l * (b'*b⁻¹) = (b'*b⁻¹)*l := Subtype.ext (hc l hl)
    simpa only [map_mul] using congrArg q hh
  let z : C := ⟨q (b' * b⁻¹),hcC⟩
  have hz : orderOf z=2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      change q (b' * b⁻¹)^2 = 1
      simpa only [map_pow,map_one] using congrArg q hpow
    · intro hh
      exact hne (congrArg Subtype.val hh)
  have hd : orderOf z ∣ Nat.card C := orderOf_dvd_natCard z
  rw [hz] at hd
  exact hd
end Theory.GroupTheory
