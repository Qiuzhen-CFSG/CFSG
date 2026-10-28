module
public import Theory.SpecificGroups.Alternating.SevenFivePlacement
public import Mathlib.GroupTheory.Perm.Support

/-!
# Centralizer of the marked five-letter A₅ in S₇

Two overlapping three-cycles force a commuting permutation to fix all five
active letters. Only the transposition on the two remaining letters survives.
This uses two small support calculations, not enumeration of S₇.

Source: Aschbacher--Smith C.4.1(1), C.4.6 and 4.3.7, pp.151--152,616.
-/

public section
open Subgroup Equiv MulAction
namespace Theory.SpecificGroups.Alternating.SevenFivePlacement
private abbrev Five : Subgroup (Perm (Fin 7)) :=
  (fixingSubgroup (alternatingGroup (Fin 7)) ({0,1} : Set (Fin 7))).map
    (alternatingGroup (Fin 7)).subtype
private def a : Perm (Fin 7) := swap 2 3 * swap 3 4
private def b : Perm (Fin 7) := swap 4 5 * swap 5 6
private theorem a_even : a ∈ alternatingGroup (Fin 7) := by
  rw [Perm.mem_alternatingGroup]
  simp [a]
private theorem b_even : b ∈ alternatingGroup (Fin 7) := by
  rw [Perm.mem_alternatingGroup]
  simp [b]
private theorem a_mem : a ∈ Five := by
  refine ⟨⟨a,a_even⟩,?_,rfl⟩
  rintro ⟨i,hi⟩
  rcases hi with rfl | ⟨rfl⟩ <;> decide
private theorem b_mem : b ∈ Five := by
  refine ⟨⟨b,b_even⟩,?_,rfl⟩
  rintro ⟨i,hi⟩
  rcases hi with rfl | ⟨rfl⟩ <;> decide

theorem centralizer_standard_five : centralizer
    (((fixingSubgroup (alternatingGroup (Fin 7)) ({0,1} : Set (Fin 7))).map
      (alternatingGroup (Fin 7)).subtype) : Set (Perm (Fin 7))) =
    zpowers (swap (0 : Fin 7) 1) := by
  classical
  apply le_antisymm
  · intro g hg
    have hga : Commute g a := (hg a a_mem).symm
    have hgb : Commute g b := (hg b b_mem).symm
    have h4a := (Perm.mem_support_iff_of_commute hga 4).mpr (by decide : (4 : Fin 7) ∈ a.support)
    have h4b := (Perm.mem_support_iff_of_commute hgb 4).mpr (by decide : (4 : Fin 7) ∈ b.support)
    have h4 : g 4 = 4 := by
      have h : a.support ∩ b.support = {4} := by decide
      have hh : g 4 ∈ a.support ∩ b.support := Finset.mem_inter.mpr ⟨h4a,h4b⟩
      simpa only [h,Finset.mem_singleton] using hh
    have h2 : g 2 = 2 := by
      have hh := congrArg (fun p : Perm (Fin 7) => p 4) hga.eq
      simpa only [Perm.mul_apply,h4,show a 4 = 2 by decide] using hh
    have h3 : g 3 = 3 := by
      have hh := congrArg (fun p : Perm (Fin 7) => p 2) hga.eq
      simpa only [Perm.mul_apply,h2,show a 2 = 3 by decide] using hh
    have h5 : g 5 = 5 := by
      have hh := congrArg (fun p : Perm (Fin 7) => p 4) hgb.eq
      simpa only [Perm.mul_apply,h4,show b 4 = 5 by decide] using hh
    have h6 : g 6 = 6 := by
      have hh := congrArg (fun p : Perm (Fin 7) => p 5) hgb.eq
      simpa only [Perm.mul_apply,h5,show b 5 = 6 by decide] using hh
    have h0 : g 0 = 0 ∨ g 0 = 1 := by
      have hh : g 0 ≠ g 2 ∧ g 0 ≠ g 3 ∧ g 0 ≠ g 4 ∧ g 0 ≠ g 5 ∧ g 0 ≠ g 6 :=
        ⟨g.injective.ne (by decide),g.injective.ne (by decide),g.injective.ne (by decide),
          g.injective.ne (by decide),g.injective.ne (by decide)⟩
      rw [h2,h3,h4,h5,h6] at hh
      omega
    have h1 : g 1 = 0 ∨ g 1 = 1 := by
      have hh : g 1 ≠ g 2 ∧ g 1 ≠ g 3 ∧ g 1 ≠ g 4 ∧ g 1 ≠ g 5 ∧ g 1 ≠ g 6 :=
        ⟨g.injective.ne (by decide),g.injective.ne (by decide),g.injective.ne (by decide),
          g.injective.ne (by decide),g.injective.ne (by decide)⟩
      rw [h2,h3,h4,h5,h6] at hh
      omega
    have hne : g 0 ≠ g 1 := g.injective.ne (by decide)
    rcases h0 with h0 | h0
    · have h1 : g 1 = 1 := h1.resolve_left (by simpa only [h0] using hne.symm)
      have hg1 : g = 1 := by
        apply Equiv.ext
        intro i
        fin_cases i <;> simpa only [h0,h1,h2,h3,h4,h5,h6]
      rw [hg1]
      exact one_mem _
    · have h1 : g 1 = 0 := h1.resolve_right (by simpa only [h0] using hne.symm)
      have hgs : g = swap 0 1 := by
        apply Equiv.ext
        intro i
        fin_cases i <;> simpa only [h0,h1,h2,h3,h4,h5,h6]
      rw [hgs]
      exact mem_zpowers _
  · apply zpowers_le.mpr
    rintro p ⟨a,ha,rfl⟩
    have ha0 : a.val 0 = 0 := ha ⟨0,by simp⟩
    have ha1 : a.val 1 = 1 := ha ⟨1,by simp⟩
    change a.val * swap 0 1 = swap 0 1 * a.val
    simpa only [ha0,ha1] using mul_swap_eq_swap_mul a.val 0 1
end Theory.SpecificGroups.Alternating.SevenFivePlacement

namespace Theory.SpecificGroups.Alternating.SevenFivePlacement

open MulAction

theorem map_fixer_pair (σ : Equiv.Perm (Fin 7)) (i j : Fin 7) :
    ((fixingSubgroup (alternatingGroup (Fin 7)) ({i,j} : Set (Fin 7))).map
      (alternatingGroup (Fin 7)).subtype).map (MulAut.conj σ).toMonoidHom =
    (fixingSubgroup (alternatingGroup (Fin 7)) ({σ i,σ j} : Set (Fin 7))).map
      (alternatingGroup (Fin 7)).subtype := by
  have heven (p : Equiv.Perm (Fin 7)) (hp : p ∈ alternatingGroup (Fin 7)) :
      σ * p * σ⁻¹ ∈ alternatingGroup (Fin 7) :=
    (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem p hp σ
  apply le_antisymm
  · rintro _ ⟨p,⟨b,hb,rfl⟩,rfl⟩
    refine ⟨⟨σ * b.val * σ⁻¹,heven _ b.property⟩,?_,rfl⟩
    rintro ⟨x,hx⟩
    change (σ * b.val * σ⁻¹) x = x
    have hi := hb ⟨i,by simp⟩
    have hj := hb ⟨j,by simp⟩
    change b.val i = i at hi
    change b.val j = j at hj
    rcases hx with rfl | ⟨rfl⟩ <;> simp [hi,hj]
  · rintro _ ⟨b,hb,rfl⟩
    let p : alternatingGroup (Fin 7) :=
      ⟨σ⁻¹ * b.val * σ,(inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem b.val b.property σ⁻¹⟩
    have hp : p ∈ fixingSubgroup (alternatingGroup (Fin 7)) ({i,j} : Set (Fin 7)) := by
      rintro ⟨x,hx⟩
      have hi := hb ⟨σ i,by simp⟩
      have hj := hb ⟨σ j,by simp⟩
      change b.val (σ i) = σ i at hi
      change b.val (σ j) = σ j at hj
      change (σ⁻¹ * b.val * σ) x = x
      rcases hx with rfl | ⟨rfl⟩ <;> simp [hi,hj]
    refine ⟨p.val,⟨p,hp,rfl⟩,?_⟩
    change σ * (σ⁻¹ * b.val * σ) * σ⁻¹ = b.val
    group
end Theory.SpecificGroups.Alternating.SevenFivePlacement
