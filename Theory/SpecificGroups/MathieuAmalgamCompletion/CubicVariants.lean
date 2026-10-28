module

public import Theory.SpecificGroups.MathieuAmalgamCompletion.MixedRelation
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Changing the exterior cubic inside the same original elementary nine

Multiplication by a power of the retained torus, and inversion, preserve the
source cubic and mixed-commutator conditions. They also preserve the generated
overgroup of the same endpoint. This permits a later quotient marking to select
one of the six exterior cubics without replacing the endpoint or linear group.
-/

public section
namespace Theory.SpecificGroups.MathieuAmalgamCompletion
open Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G]

private theorem shift (P : Subgroup G) (t n r ell : G)
    (ht : t∈P) (ht3 : t^3=1) (hn3 : n^3=1) (hnt : Commute n t)
    (hnT : n∉zpowers t) (hrt : r*t*r⁻¹=t⁻¹) (hrn : r*n*r⁻¹=n⁻¹)
    (helt : Commute ell t) (hcross : ⁅ell,n⁆^2=1) (k : Nat) :
    Commute (n*t^k) t ∧ orderOf (n*t^k)=3 ∧ n*t^k∉zpowers t ∧
      r*(n*t^k)*r⁻¹=(n*t^k)⁻¹ ∧ ⁅ell,n*t^k⁆^2=1 ∧
      P⊔zpowers (n*t^k)=P⊔zpowers n := by
  have htP : t^k∈P := P.pow_mem ht k
  have htT : t^k∈zpowers t := pow_mem (mem_zpowers t) k
  have hntk := hnt.pow_right k
  have hnT' : n*t^k∉zpowers t := by
    intro hm
    have hh := (zpowers t).mul_mem hm ((zpowers t).inv_mem htT)
    apply hnT
    simpa only [mul_inv_cancel_right] using hh
  have hm3 : (n*t^k)^3=1 := by
    rw [hntk.mul_pow,hn3,one_mul,←pow_mul, Nat.mul_comm k 3,pow_mul,ht3,one_pow]
  have hrpow : r*t^k*r⁻¹=(t^k)⁻¹ := by
    have hh := congrArg (fun x : G => x^k) hrt
    simpa only [conj_pow,inv_pow] using hh
  have hrm : r*(n*t^k)*r⁻¹=(n*t^k)⁻¹ := by
    calc
      _=(r*n*r⁻¹)*(r*t^k*r⁻¹) := by group
      _=n⁻¹*(t^k)⁻¹ := by rw [hrn,hrpow]
      _=(n*t^k)⁻¹ := by rw [mul_inv_rev]; exact hntk.inv_left.inv_right.eq
  have hcc : ⁅ell,n*t^k⁆=⁅ell,n⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_eq_one_iff_commute.mpr (helt.pow_right k),mul_one,mul_inv_cancel_right]
  have hjoin : P⊔zpowers (n*t^k)=P⊔zpowers n := by
    apply le_antisymm
    · apply sup_le le_sup_left
      apply zpowers_le.mpr
      exact (P⊔zpowers n).mul_mem (mem_sup_right (mem_zpowers n)) (mem_sup_left htP)
    · apply sup_le le_sup_left
      apply zpowers_le.mpr
      have hh := (P⊔zpowers (n*t^k)).mul_mem
        (mem_sup_right (mem_zpowers (n*t^k)))
        ((P⊔zpowers (n*t^k)).inv_mem (mem_sup_left htP))
      simpa only [mul_inv_cancel_right] using hh
  exact ⟨hnt.mul_left (Commute.refl t |>.pow_left k),
    orderOf_eq_prime hm3 (fun hh => hnT' (hh ▸ (zpowers t).one_mem)),
    hnT',hrm,by rwa [hcc],hjoin⟩

/-- All six choices `n^(±1)*t^k` preserve the original source relations and
its generated endpoint overgroup. The same `t`, `r`, and `ell` are retained. -/
theorem cubic_variants_preserve_source (P : Subgroup G) (t n r ell : G)
    (ht : t∈P) (ht3 : orderOf t=3) (hn3 : orderOf n=3) (hnt : Commute n t)
    (hnT : n∉zpowers t) (hrt : r*t*r⁻¹=t⁻¹) (hrn : r*n*r⁻¹=n⁻¹)
    (helt : Commute ell t) (hcross : ⁅ell,n⁆^2=1) (b : Bool) (k : Nat) :
    let m := (if b then n⁻¹ else n)*t^k
    Commute m t ∧ orderOf m=3 ∧ m∉zpowers t ∧
      r*m*r⁻¹=m⁻¹ ∧ ⁅ell,m⁆^2=1 ∧ P⊔zpowers m=P⊔zpowers n := by
  have ht3' : t^3=1 := ht3 ▸ pow_orderOf_eq_one t
  have hn3' : n^3=1 := hn3 ▸ pow_orderOf_eq_one n
  cases b
  · exact shift P t n r ell ht ht3' hn3' hnt hnT hrt hrn helt hcross k
  · have hni3 : (n⁻¹)^3=1 := by rw [inv_pow,hn3',inv_one]
    have hniT : n⁻¹∉zpowers t := by
      intro hn
      exact hnT (by simpa using (zpowers t).inv_mem hn)
    have hrni : r*n⁻¹*r⁻¹=(n⁻¹)⁻¹ := by
      have hh := congrArg Inv.inv hrn
      simpa only [mul_inv_rev,inv_inv,mul_assoc] using hh
    have hcross' : ⁅ell,n⁻¹⁆^2=1 := by
      rw [commutatorElement_inv_right,←commutatorElement_inv]
      have hh := congrArg (MulAut.conj n⁻¹) (show (⁅ell,n⁆⁻¹)^2=1 by
        rw [inv_pow,hcross,inv_one])
      simpa only [map_pow,map_one,MulAut.conj_apply,inv_inv] using hh
    obtain ⟨hc,ho,hn,hr,hx,hj⟩ :=
      shift P t n⁻¹ r ell ht ht3' hni3 hnt.inv_left hniT hrt hrni helt hcross' k
    exact ⟨hc,ho,hn,hr,hx,by simpa only [zpowers_inv,if_true] using hj⟩

end Theory.SpecificGroups.MathieuAmalgamCompletion
