module
public import Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers.NormalForms
public import Mathlib.GroupTheory.PGroup

/-!
# A symplectic involution with an odd centralizer element

The first hyperbolic-plane transvection commutes with an order-three element
on the second plane. This explicit pair rules out the assertion that every
involution centralizer is a two-group, over every field of characteristic two.
It removes the symplectic carrier row in the all-c2 part of
Aschbacher--Smith E.2.7, printed p.220.
-/

public section
open Subgroup Matrix
namespace Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour InvolutionTypes
variable {F : Type*} [Field F] [CharP F 2]
private theorem root_order_three :
    orderOf (rootElement (K := F) 2 1 * rootElement 3 1)=3 := by
  apply orderOf_eq_prime_iff.mpr
  constructor
  · apply Subtype.ext
    ext i j
    rcases i with i|i <;> rcases j with j|j <;> fin_cases i <;> fin_cases j <;>
      simp [pow_succ,rootElement,rootMatrix,Matrix.mul_apply,Fintype.sum_sum_type,
        Fin.sum_univ_two,Matrix.fromBlocks,Matrix.single,CharTwo.add_self_eq_zero]
  · intro h
    have hh := congrArg (fun x : Sp F => x.val (.inl 1) (.inr 1)) h
    simp [rootElement,rootMatrix,Matrix.mul_apply,Fintype.sum_sum_type,
      Matrix.fromBlocks,Matrix.single] at hh

omit [CharP F 2] in
private theorem root_commute :
    Commute (rootElement (K := F) 2 1 * rootElement 3 1) (rootElement 0 1) := by
  change _ * _ = _ * _
  apply Subtype.ext
  ext i j
  rcases i with i|i <;> rcases j with j|j <;> fin_cases i <;> fin_cases j <;>
    simp [rootElement,rootMatrix,Matrix.mul_apply,Fintype.sum_sum_type,
      Fin.sum_univ_two,Matrix.fromBlocks,Matrix.single]

theorem not_all_involution_centralizers_two :
    ¬∀ t : Sp F, orderOf t=2 → IsPGroup 2 (centralizer ({t} : Set (Sp F))) := by
  intro h
  let r := rootElement (K := F) 2 1 * rootElement 3 1
  let t := rootElement (K := F) 0 1
  have hr : orderOf r=3 := root_order_three
  have ht : orderOf t=2 := InvolutionCentralizers.rootElement_orderOf 0 one_ne_zero
  let x : centralizer ({t} : Set (Sp F)) := ⟨r,mem_centralizer_singleton_iff.mpr root_commute.eq⟩
  have hx : x≠1 := by
    intro hx
    have he : r=1 := congrArg Subtype.val hx
    rw [he,orderOf_one] at hr
    omega
  have hd := (h t ht).dvd_orderOf hx
  rw [←Subgroup.orderOf_coe x] at hd
  change 2 ∣ orderOf r at hd
  rw [hr] at hd
  norm_num at hd
end Theory.SpecificGroups.SymplecticFour
