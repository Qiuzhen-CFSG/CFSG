module

public import Theory.Frattini.BinarySquares
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.ElementaryAbelian.Basic

/-!
# Frattini bounds for conjugate spans of elementary two-subgroups

If the conjugate span W of an elementary two-subgroup is a two-group,
any bound [W,W]≤Z also bounds Φ(W). Each generator is an involution;
the identity (xy)²=x²[x⁻¹,y]y² propagates square membership in Z through
the closure. The binary Frattini generation theorem then applies.
Source application: Campbell, *Pushing up in Finite Groups* (1979), II.6.1,
printed p.29. No centrality or normality of Z is required.
-/

public section
open Subgroup
open scoped Pointwise IsMulCommutative commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem frattini_conjugateSpan_le_of_commutator (Y K Z : Subgroup G) [IsElementaryAbelian 2 Y]
    (hW : IsPGroup 2 (conjugateSpanBy Y K))
    (hc : ⁅conjugateSpanBy Y K,conjugateSpanBy Y K⁆ ≤ Z) :
    (frattini (conjugateSpanBy Y K)).map (conjugateSpanBy Y K).subtype ≤ Z := by
  let W := conjugateSpanBy Y K
  have hsq : ∀ x ∈ W, x^2 ∈ Z := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k,hk,y,hy,rfl⟩ := hy
      rw [conj_pow,elemPow_eq_one_of_isElementaryAbelian y hy,mul_one,mul_inv_cancel]
      exact Z.one_mem
    | one => simp
    | inv x _ ih => simpa only [inv_pow] using Z.inv_mem ih
    | mul x y hx hy ihx ihy =>
      have hi : (x*y)^2=x^2*⁅x⁻¹,y⁆*y^2 := by simp [commutatorElement_def,pow_two,mul_assoc]
      rw [hi]
      exact Z.mul_mem (Z.mul_mem ihx (hc (commutator_mem_commutator (W.inv_mem hx) hy))) ihy
  rw [map_le_iff_le_comap,hW.frattini_eq_closure_squares]
  apply (closure_le _).mpr
  rintro x ⟨y,rfl⟩
  exact hsq y y.property
end Subgroup
