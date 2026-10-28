module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index

/-!
# Binary quadratic action with an index-two centralizing subgroup

If elementary abelian two-groups V and C satisfy C <= N(V), and a
subgroup Q centralizes V with [C : C intersect Q] = 2, then [V,C,C] = 1.
Each involution x in C centralizes its own displacement [v,x]. Two
actors outside Q have product in Q, so they centralize each other's
displacements as well. No ambient normality of Q is assumed.

This supplies the small-alpha obstruction in Delgado--Goldschmidt--
Stellmacher, Groups and Graphs (1985), Chapter 11, (11.3)(f).
-/

public section
open Subgroup
open scoped commutatorElement

theorem Subgroup.quadratic_of_elementary_index_two {G : Type*} [Group G] (V C Q : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 C]
    (hCV : C ≤ normalizer (V : Set G))
    (hQV : Q ≤ centralizer (V : Set G)) (hi : Q.relIndex C = 2) :
    ⁅⁅V,C⁆,C⁆ = ⊥ := by
  have hdisp : ⁅V,C⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp hCV
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply commutator_le.mpr
  intro v hv x hx y hy
  have hd : ⁅v,x⁆ ∈ V := hdisp (commutator_mem_commutator hv hx)
  have hdQ (z : G) (hz : z ∈ Q) : Commute ⁅v,x⁆ z := hQV hz _ hd
  by_cases hxQ : x ∈ Q
  · have hxv : Commute v x := hQV hxQ _ hv
    rw [hxv.commutator_eq]
    simp
  by_cases hyQ : y ∈ Q
  · exact (hdQ y hyQ).eq.symm
  have hxyQ : x*y ∈ Q := by
    have hh := (Q.subgroupOf C).mul_mem_iff_of_index_two hi (a := ⟨x,hx⟩) (b := ⟨y,hy⟩)
    exact hh.mpr (by change x ∈ Q ↔ y ∈ Q; simp [hxQ,hyQ])
  have hxx : x⁻¹ = x := inv_eq_of_mul_eq_one_left
    (by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx)
  have hdd : ⁅v,x⁆⁻¹ = ⁅v,x⁆ := inv_eq_of_mul_eq_one_left
    (by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) ⁅v,x⁆ hd)
  have hdx : Commute ⁅v,x⁆ x := by
    have hh := commutatorElement_inv_right v x
    rw [hxx,←commutatorElement_inv v x,hdd] at hh
    have hh' := congrArg (fun z => z * x) hh
    have hxx' : x*x=1 := by simpa only [pow_two] using
      elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx
    change ⁅v,x⁆ * x = x * ⁅v,x⁆
    simpa only [mul_assoc,hxx',mul_one] using hh'
  have hh := hdx.inv_right.mul_right (hdQ (x*y) hxyQ)
  simpa only [inv_mul_cancel_left] using hh.eq.symm

