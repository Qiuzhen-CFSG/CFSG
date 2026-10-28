module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Linarith

/-!
# An elementary nine with a faithful cyclic-four normalizer quotient

If a normalizer of order36 contains an actor whose fourth power is one and
whose square inverts its elementary subgroup of order9, the actor image has
order4. The conjugation kernel contains the elementary nine, so counting
forces equality. The same actor generates the faithful quotient of order4.
The actual cubic normalizer in Aschbacher (1994),45.9 supplies the actor.
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
theorem elementary_nine_cyclic_four_normalizer (S:Subgroup G) [IsElementaryAbelian 3 S]
    (hS:Nat.card S=9) (hN:Nat.card (normalizer (S:Set G))=36)
    (r:G) (hr:r∈normalizer (S:Set G)) (hr4:r^4=1)
    (hinv:∀s∈S,r^2*s*(r^2)⁻¹=s⁻¹) :
    centralizer (S:Set G)≤S ∧
      Nonempty ((normalizer (S:Set G) ⧸ S.subgroupOf (normalizer (S:Set G)))≃*Multiplicative (ZMod 4)) := by
  let N:=normalizer (S:Set G)
  let f:=S.normalizerMonoidHom
  let rn:N:=⟨r,hr⟩
  have hSker:S.subgroupOf N≤f.ker:=by
    rw [normalizerMonoidHom_ker]
    exact subgroupOf_mono N S.le_centralizer
  have hn:Nontrivial S:=Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let :Nontrivial S:=hn
  obtain ⟨s,hs⟩:=exists_ne (1:S)
  have hsq:(f rn)^2≠1:=by
    intro hh
    have hh':f (rn^2) s=s:=by rw [map_pow,hh];rfl
    have hhG:r^2*(s:G)*(r^2)⁻¹=(s:G):=congrArg Subtype.val hh'
    rw [hinv s s.property] at hhG
    have h2:s^2=1:=by
      apply Subtype.ext
      change (s:G)^2=1
      calc
        (s:G)^2=(s:G)*(s:G) := pow_two _
        _=(s:G)*(s:G)⁻¹ := congrArg ((s:G)*·) hhG.symm
        _=1 := mul_inv_cancel _
    have h3:s^3=1:=Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 3 S) s
    exact hs (by
      calc
        s=s^3*(s^2)⁻¹ := by group
        _=1 := by rw[h2,h3];simp)
  have hrn4:rn^4=1:=Subtype.ext hr4
  have ho:orderOf (f rn)=4:=orderOf_eq_prime_pow (p:=2) (n:=1) hsq (by change (f rn)^4=1;rw[←map_pow,hrn4,map_one])
  let a:f.range:=⟨f rn,⟨rn,rfl⟩⟩
  have hoa:orderOf a=4:=(Subgroup.orderOf_coe a).symm.trans ho
  have hd:4∣Nat.card f.range:=hoa ▸ _root_.orderOf_dvd_natCard a
  have hSk:9∣Nat.card f.ker:=by
    have hh:=card_dvd_of_le hSker
    rwa [Nat.card_congr (subgroupOfEquivOfLe S.le_normalizer).toEquiv,hS] at hh
  have hprod:Nat.card f.ker*Nat.card f.range=36:=by
    rw [←index_ker,f.ker.card_mul_index,hN]
  have hk:Nat.card f.ker=9:=by
    have h9:=Nat.le_of_dvd (Nat.card_pos (α:=f.ker)) hSk
    have h4:=Nat.le_of_dvd (Nat.card_pos (α:=f.range)) hd
    have hh:=Nat.mul_le_mul_left (Nat.card f.ker) h4
    nlinarith
  have heq:f.ker=S.subgroupOf N:=
    (eq_of_le_of_card_ge hSker (by rw[hk,Nat.card_congr (subgroupOfEquivOfLe S.le_normalizer).toEquiv,hS])).symm
  have hc:centralizer (S:Set G)≤S:=by
    intro x hx
    have hxN:x∈N:=centralizer_le_normalizer _ hx
    have hxk:(⟨x,hxN⟩:N)∈f.ker:=by rw[normalizerMonoidHom_ker];exact hx
    exact heq.le hxk
  have hfc:Nat.card f.range=4:=by rw[hk] at hprod;omega
  let :IsCyclic f.range:=isCyclic_iff_exists_orderOf_eq_natCard.mpr ⟨a,hoa.trans hfc.symm⟩
  have ee: f.range≃*Multiplicative (ZMod 4):=mulEquivOfCyclicCardEq (by simpa using hfc)
  exact ⟨hc,⟨(QuotientGroup.quotientMulEquivOfEq heq.symm).trans ((QuotientGroup.quotientKerEquivRange f).trans ee)⟩⟩
end Subgroup
