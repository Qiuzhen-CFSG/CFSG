module
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupAction.Defs
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Odd centralizers are faithful on binary involution fixed points

Let t square to one on an elementary abelian two-group V. An odd-order
subgroup A of its automorphism group centralizing t acts faithfully on the
fixed subgroup C_V(t): the pointwise fixing subgroup of A is trivial.
The statement uses the literal automorphisms and their existing actions,
without choosing an additional invariance or restriction-action instance.
The identity involution is included.

The displacement v⁻¹t(v) lies in C_V(t). If r commutes with t and fixes
C_V(t), equivariance of this displacement shows that v⁻¹r(v) also lies in
C_V(t). Thus r fixes its own displacement. Expanding that identity in
characteristic two gives r²=1. Since r belongs to an odd-order group,
its order divides both two and an odd number and is therefore one.

This source-neutral faithfulness lemma is used on the actual elementary
quotient in Stellmacher (8.6)(20), Journal of Algebra 190 (1997), printed
p.45; refs/files/stellmacher-n-group.pdf.
-/


namespace MulAut
open scoped IsMulCommutative

private theorem square_eq_one_of_fixes_involution_fixed
    {V : Type*} [Group V] [IsElementaryAbelian 2 V]
    (t r : MulAut V) (ht : t^2=1) (hcomm : t*r=r*t)
    (hfix : ∀ v ∈ FixedPoints.subgroup (Subgroup.zpowers t) V, r v=v) :
    r^2=1 := by
  have hinv (v : V) : v⁻¹=v := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) v
  have htiter (v : V) : t (t v)=v := by
    have hh := congrArg (fun f : MulAut V => f v) ht
    simpa only [pow_two,MulAut.mul_apply,MulAut.one_apply] using hh
  have hcomm_apply (v : V) : t (r v)=r (t v) :=
    congrArg (fun f : MulAut V => f v) hcomm
  let d : V →* V := (MonoidHom.id V)⁻¹ * t.toMonoidHom
  have hd (v : V) : d v=v⁻¹*t v := rfl
  have hdFix (v : V) : d v ∈ FixedPoints.subgroup (Subgroup.zpowers t) V := by
    intro mover
    apply smul_eq_self_of_mem_zpowers mover.property
    change t (v⁻¹*t v)=v⁻¹*t v
    rw [map_mul,map_inv,htiter,hinv,hinv,mul_comm]
  have hdComm (v : V) : d (r v)=r (d v) := by
    simp only [hd,map_mul,map_inv,hcomm_apply]
  have hkerFixed (v : V) (hv : d v=1) :
      v ∈ FixedPoints.subgroup (Subgroup.zpowers t) V := by
    intro mover
    apply smul_eq_self_of_mem_zpowers mover.property
    exact (inv_mul_eq_one.mp hv).symm
  have hrDelta (v : V) : v⁻¹*r v ∈ FixedPoints.subgroup (Subgroup.zpowers t) V := by
    apply hkerFixed
    rw [map_mul,map_inv,hdComm,hfix _ (hdFix v),inv_mul_cancel]
  ext v
  have hh := hfix _ (hrDelta v)
  change r (v⁻¹*r v)=v⁻¹*r v at hh
  simp only [map_mul,hinv] at hh
  change r (r v)=v
  apply mul_left_cancel (a := r v)
  exact hh.trans (mul_comm _ _)

public theorem odd_centralizer_fixed_action_faithful
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (t : MulAut V) (ht : t^2=1) (A : Subgroup (MulAut V))
    (hodd : Odd (Nat.card A))
    (hcentral : A ≤ Subgroup.centralizer (Subgroup.zpowers t : Set (MulAut V))) :
    fixingSubgroup A (FixedPoints.subgroup (Subgroup.zpowers t) V : Set V)=⊥ := by
  apply bot_unique
  intro r hr
  have hcomm : t*(r:MulAut V)=(r:MulAut V)*t :=
    Subgroup.mem_centralizer_iff.mp (hcentral r.property) t (Subgroup.mem_zpowers t)
  have hfix : ∀ v ∈ FixedPoints.subgroup (Subgroup.zpowers t) V, (r:MulAut V) v=v :=
    (mem_fixingSubgroup_iff (M := A)).mp hr
  have hsquare : r^2=1 := Subtype.ext
    (square_eq_one_of_fixes_involution_fixed t r ht hcomm hfix)
  have horder : orderOf r=1 := Nat.eq_one_of_dvd_coprimes hodd.coprime_two_right
    (orderOf_dvd_natCard r) (orderOf_dvd_of_pow_eq_one hsquare)
  exact orderOf_eq_one_iff.mp horder

end MulAut
