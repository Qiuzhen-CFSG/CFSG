module
public import Theory.Alternating.Aut
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.FinCases

/-!
# Pointwise fixers of a triple-transposition centralizer

In the seven-point permutation action, the centralizer of C_A₇(t), for t
of cycle type (2,2,2), is precisely {1,t}. Three explicit even permutations
in C_A₇(t) determine all seven coordinates of a pointwise fixer. Conjugacy
of cycle types transports the calculation, and Aut(A₇) = S₇ gives the
automorphism version.

Source application: Aschbacher–Smith 12.4.8, printed p.816.
-/

open Equiv Equiv.Perm Subgroup
namespace AlternatingSeven.DoubleCentralizer
private abbrev S7 := Perm (Fin 7)
private def a : S7 := swap 0 1 * swap 2 3
private def b : S7 := swap 2 3 * swap 4 5
private def r : S7 := (swap 0 2 * swap 2 4) * (swap 1 3 * swap 3 5)
private def t : S7 := swap 0 1 * swap 2 3 * swap 4 5

private theorem coordinate_centralizer (x : S7)
    (ha : Commute x a) (hb : Commute x b) (hr : Commute x r) :
    x = 1 ∨ x = t := by
  have h1 := congrArg (fun p : S7 => p 0) ha.eq
  have h2 := congrArg (fun p : S7 => p 0) hr.eq
  have h3 := congrArg (fun p : S7 => p 2) ha.eq
  have h4 := congrArg (fun p : S7 => p 2) hr.eq
  have h5 := congrArg (fun p : S7 => p 4) hb.eq
  have h0b := congrArg (fun p : S7 => p 0) hb.eq
  have h6a := congrArg (fun p : S7 => p 6) ha.eq
  have h6b := congrArg (fun p : S7 => p 6) hb.eq
  change x 1 = a (x 0) at h1
  change x 2 = r (x 0) at h2
  change x 3 = a (x 2) at h3
  change x 4 = r (x 2) at h4
  change x 5 = b (x 4) at h5
  change x 0 = b (x 0) at h0b
  change x 6 = a (x 6) at h6a
  change x 6 = b (x 6) at h6b
  have h6 : x 6 = 6 := (by decide +kernel : ∀ i : Fin 7,
    i = a i → i = b i → i = 6) (x 6) h6a h6b
  have h0 : x 0 = 0 ∨ x 0 = 1 := (by decide +kernel : ∀ i : Fin 7,
    i = b i → a i ≠ i → i = 0 ∨ i = 1) (x 0) h0b (by
      rw [← h1]
      exact x.injective.ne (by decide))
  rcases h0 with h0 | h0
  · left
    apply Equiv.ext
    intro i
    fin_cases i
    · exact h0
    · simpa [h0, a, b, r, t, swap_apply_def] using h1
    · simpa [h0, a, b, r, t, swap_apply_def] using h2
    · simpa [h2, h0, a, b, r, t, swap_apply_def] using h3
    · simpa [h2, h0, a, b, r, t, swap_apply_def] using h4
    · simpa [h4, h2, h0, a, b, r, t, swap_apply_def] using h5
    · exact h6
  · right
    apply Equiv.ext
    intro i
    fin_cases i
    · exact h0
    · simpa [h0, a, b, r, t, swap_apply_def] using h1
    · simpa [h0, a, b, r, t, swap_apply_def] using h2
    · simpa [h2, h0, a, b, r, t, swap_apply_def] using h3
    · simpa [h2, h0, a, b, r, t, swap_apply_def] using h4
    · simpa [h4, h2, h0, a, b, r, t, swap_apply_def] using h5
    · exact h6

private theorem standard (x : S7)
    (hx : x ∈ centralizer ((alternatingGroup (Fin 7) ⊓ centralizer ({t} : Set S7) :
      Subgroup S7) : Set S7)) : x = 1 ∨ x = t := by
  apply coordinate_centralizer
  · exact (hx a (by
      constructor
      · change a.sign = 1; decide +kernel
      · exact mem_centralizer_singleton_iff.mpr (by decide +kernel))).symm
  · exact (hx b (by
      constructor
      · change b.sign = 1; decide +kernel
      · exact mem_centralizer_singleton_iff.mpr (by decide +kernel))).symm
  · exact (hx r (by
      constructor
      · change r.sign = 1; decide +kernel
      · exact mem_centralizer_singleton_iff.mpr (by decide +kernel))).symm

public theorem triple_double_centralizer (z : Perm (Fin 7)) (hz : z.cycleType = {2,2,2})
    (x : Perm (Fin 7)) (hx : x ∈ centralizer
      ((alternatingGroup (Fin 7) ⊓ centralizer ({z} : Set (Perm (Fin 7))) :
        Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7)))) :
    x = 1 ∨ x = z := by
  have hc : IsConj t z := isConj_iff_cycleType_eq.mpr
    ((by decide +kernel : t.cycleType = {2,2,2}).trans hz.symm)
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  let e := MulAut.conj g
  have he : e t = z := hg
  have hx' : e.symm x ∈ centralizer
      ((alternatingGroup (Fin 7) ⊓ centralizer ({t} : Set S7) : Subgroup S7) : Set S7) := by
    intro y hy
    have hy' : e y ∈ alternatingGroup (Fin 7) ⊓ centralizer ({z} : Set S7) := by
      refine ⟨(inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem y hy.1 g, ?_⟩
      have hc : Commute y t := mem_centralizer_singleton_iff.mp hy.2
      have hh := hc.map e.toMonoidHom
      change Commute (e y) (e t) at hh
      rw [he] at hh
      exact mem_centralizer_singleton_iff.mpr hh.eq
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) hy'
  rcases standard (e.symm x) hx' with hh | hh
  · exact Or.inl (by simpa only [e.apply_symm_apply, map_one] using congrArg e hh)
  · exact Or.inr (by simpa only [e.apply_symm_apply, he] using congrArg e hh)
end AlternatingSeven.DoubleCentralizer


public theorem AlternatingSeven.DoubleCentralizer.fixed_automorphism
    (σ : Perm (Fin 7)) (hσ : σ.cycleType = {2,2,2})
    (β : MulAut (alternatingGroup (Fin 7)))
    (hβ : ∀ x ∈ (MulAut.conjNormal (H := alternatingGroup (Fin 7)) σ).fixedSubgroup,
      β x = x) :
    β = 1 ∨ β = MulAut.conjNormal σ := by
  obtain ⟨b,rfl⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    7 (by decide) (by decide)).surjective β
  have hb : b ∈ centralizer ((alternatingGroup (Fin 7) ⊓
      centralizer ({σ} : Set (Perm (Fin 7)))) : Set (Perm (Fin 7))) := by
    intro x hx
    have hfix : (⟨x,hx.1⟩ : alternatingGroup (Fin 7)) ∈
        (MulAut.conjNormal σ).fixedSubgroup := by
      rw [MulAut.mem_fixedSubgroup]
      apply Subtype.ext
      change σ * x * σ⁻¹ = x
      rw [← mem_centralizer_singleton_iff.mp hx.2, mul_inv_cancel_right]
    have he := congrArg Subtype.val (hβ ⟨x,hx.1⟩ hfix)
    change b * x * b⁻¹ = x at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  rcases AlternatingSeven.DoubleCentralizer.triple_double_centralizer σ hσ b hb with rfl | rfl
  · exact Or.inl (map_one (MulAut.conjNormal : Perm (Fin 7) →* _))
  · exact Or.inr rfl
