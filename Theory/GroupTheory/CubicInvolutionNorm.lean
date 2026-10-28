module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.Index
/-!
# A cubic norm and an elementary fixed subgroup

For three cyclically permuted involutions with the same nontrivial central
commutator, their product is fixed and has that commutator as its square.
An involution fixed by the cubic and centralizing the triple therefore cannot
lie outside an invariant subgroup of index two whose fixed elements square
to one: its product with this norm would be a fixed element inside that
subgroup with nontrivial square.

This supplies the involution-placement argument used with the literal core
sections in DGS, Groups and Graphs (1985), (10.8), printed p.161.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]
private theorem three_involution_product (a b c z : G)
    (ha : a^2=1) (hb : b^2=1) (hc : c^2=1)
    (hab : ⁅a,b⁆=z) (hbc : ⁅b,c⁆=z) (hca : ⁅c,a⁆=z)
    (hzb : Commute z b) :
    b*c*a=a*b*c ∧ (a*b*c)^2=z := by
  have hac : ⁅a,c⁆=z⁻¹ := by rw [←commutatorElement_inv,hca]
  have he : Commute a (b*c) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [commutatorElement_mul_right_eq_mul_conj,hab,hac]
    rw [hzb.eq]
    group
  refine ⟨by simpa only [mul_assoc] using he.eq.symm,?_⟩
  rw [mul_assoc,he.mul_pow,ha,one_mul]
  have bi : b⁻¹=b := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hb)
  have ci : c⁻¹=c := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hc)
  simpa only [commutatorElement_def,bi,ci,pow_two,mul_assoc] using hbc

/-- A fixed involution centralizing a cyclic triple lies in the index-two
subgroup when its fixed elements have exponent two. -/
theorem cubic_fixed_involution_mem_index_two
    (I : Subgroup G) (hi : I.index=2)
    (f : MulAut G) (hf : f^3=1) (hfI : ∀ a, f a∈I ↔ a∈I)
    (hfixed : ∀ a∈I, f a=a → a^2=1)
    (x a z : G) (hx : x^2=1) (hfx : f x=x) (hxa : Commute x a)
    (ha : a^2=1) (haI : a∉I) (hz : z≠1)
    (hab : ⁅a,f a⁆=z) (hfz : f z=z) (hza : Commute z (f a)) : x∈I := by
  have hf3 (v : G) : f (f (f v))=v := by
    have hh := DFunLike.congr_fun hf v
    simpa only [pow_succ,pow_zero,MulAut.mul_apply,MulAut.one_apply] using hh
  have hbc : ⁅f a,f (f a)⁆=z := by rw [←map_commutatorElement,hab,hfz]
  have hca : ⁅f (f a),a⁆=z := by
    have hh := congrArg f hbc
    simpa only [map_commutatorElement,hf3,hfz] using hh
  have hb : (f a)^2=1 := by rw [←map_pow,ha,map_one]
  have hc : (f (f a))^2=1 := by rw [←map_pow,hb,map_one]
  obtain ⟨hcycle,hsq⟩ := three_involution_product a (f a) (f (f a)) z ha hb hc hab hbc hca hza
  let n := a*f a*f (f a)
  have hfn : f n=n := by simpa only [n,map_mul,hf3] using hcycle
  have hn : n∉I := by
    have hbI : f a∉I := fun h => haI ((hfI a).mp h)
    have hcI : f (f a)∉I := fun h => hbI ((hfI (f a)).mp h)
    have habI : a*f a∈I := (I.mul_mem_iff_of_index_two hi).mpr (iff_of_false haI hbI)
    intro hn
    exact hcI ((I.mul_mem_iff_of_index_two hi).mp hn |>.mp habI)
  have hxb : Commute x (f a) := by
    apply (commute_iff_eq _ _).mpr
    simpa only [map_mul,hfx] using congrArg f hxa.eq
  have hxc : Commute x (f (f a)) := by
    apply (commute_iff_eq _ _).mpr
    simpa only [map_mul,hfx] using congrArg f hxb.eq
  have hxn : Commute x n := (hxa.mul_right hxb).mul_right hxc
  by_contra hxI
  have hxnI : x*n∈I := (I.mul_mem_iff_of_index_two hi).mpr (iff_of_false hxI hn)
  have hh := hfixed (x*n) hxnI (by rw [map_mul,hfx,hfn])
  rw [hxn.mul_pow,hx,one_mul] at hh
  exact hz (hsq.symm.trans hh)
end Subgroup
