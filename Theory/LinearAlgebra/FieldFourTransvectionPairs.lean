module
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Products of transvections over the four-element field

Write two transvections as x ↦ x + f(x)v and x ↦ x + g(x)w.
Their cross-pairing a = f(w)g(v) is zero, one, or satisfies a²+a+1=0.
Direct scalar calculations give fourth, third, or fifth power one,
respectively. In particular their product cannot have order fifteen.
We also convert an involution of displacement rank at most one into
this transvection form and retain it under conjugation.

Source application: the PSL₂(31) multiplicity exclusion in
Aschbacher–Smith 8.2.9, printed p.721, refs/quasithin.pdf.
-/
public section
set_option linter.unusedSimpArgs false
open scoped CharTwo
namespace LinearEquiv
variable {F X : Type*} [Field F] [CharP F 2] [AddCommGroup X] [Module F X]

private theorem pair_cube (f g : Module.Dual F X) (v w : X) (hf : f v=0) (hg : g w=0)
    (hc : f w*g v=1) : (transvection hf * transvection hg)^3=1 := by
  apply LinearEquiv.ext
  intro x
  simp [pow_succ,LinearMap.transvection.apply,hf,hg]
  match_scalars <;> ring_nf <;> simp
  · linear_combination (norm := skip) (g x*(f w*g v+1)+f x*g v)*hc
    ring_nf
    simp
  · linear_combination (norm := skip) (f x*(f w*g v+1)+g x*f w*(f w*g v))*hc
    ring_nf
    simp

private theorem pair_four (f g : Module.Dual F X) (v w : X) (hf : f v=0) (hg : g w=0)
    (hc : f w*g v=0) : (transvection hf * transvection hg)^4=1 := by
  rcases mul_eq_zero.mp hc with h | h <;>
    apply LinearEquiv.ext <;> intro x <;>
    simp [pow_succ,LinearMap.transvection.apply,hf,hg,h] <;>
    match_scalars <;> ring_nf <;> simp

private theorem pair_five (f g : Module.Dual F X) (v w : X) (hf : f v=0) (hg : g w=0)
    (hc : (f w*g v)^2+f w*g v+1=0) : (transvection hf * transvection hg)^5=1 := by
  apply LinearEquiv.ext
  intro x
  simp [pow_succ,LinearMap.transvection.apply,hf,hg]
  match_scalars <;> ring_nf <;> simp
  · linear_combination (norm := skip)
      (g x*((f w*g v)^2+f w*g v+1)+f x*f w*(g v)^2)*hc
    ring_nf
    simp
  · linear_combination (norm := skip)
      (f x*((f w*g v)^2+f w*g v+1)+g x*f w*((f w*g v)^2+1))*hc
    ring_nf
    simp

theorem mem_transvections_of_square_one_rank_one [FiniteDimensional F X]
    (t : X ≃ₗ[F] X) (ht : t*t=1)
    (hr : Module.finrank F (LinearMap.range (t.toLinearMap-1)) ≤ 1) :
    t ∈ transvections F X := by
  obtain ⟨f,v,he⟩ := mem_dilatransvections_iff_finrank.mpr hr
  have he' (x : X) : t x=x+f x • v := congrArg (fun l : X →ₗ[F] X => l x) he
  have hh : t (t v)=v := DFunLike.congr_fun ht v
  have heq : t (t v)=v+(f v)^2 • v := by
    simp only [he',map_add,map_smul]
    match_scalars
    ring_nf
    simp
    ring
  rw [heq] at hh
  have hz : (f v)^2 • v=0 := add_eq_left.mp hh
  have hf : f v=0 := by
    rcases smul_eq_zero.mp hz with h | h
    · exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp h
    · simp [h]
  refine mem_transvections_iff.mpr ⟨f,v,hf,?_⟩
  ext x
  exact he' x

omit [CharP F 2] in
theorem conjugate_mem_transvections (a t : X ≃ₗ[F] X)
    (ht : t ∈ transvections F X) : a*t*a⁻¹ ∈ transvections F X := by
  obtain ⟨f,v,hf,rfl⟩ := mem_transvections_iff.mp ht
  let f' : Module.Dual F X := f.comp a.symm.toLinearMap
  have hf' : f' (a v)=0 := by simp [f',hf]
  refine mem_transvections_iff.mpr ⟨f',a v,hf',?_⟩
  ext x
  simp [f',LinearMap.transvection.apply]

theorem transvection_pair_not_order_fifteen [Finite F] (hF : Nat.card F=4)
    (s t : X ≃ₗ[F] X) (hs : s ∈ transvections F X) (ht : t ∈ transvections F X) :
    orderOf (s*t) ≠ 15 := by
  obtain ⟨f,v,hf,rfl⟩ := mem_transvections_iff.mp hs
  obtain ⟨g,w,hg,rfl⟩ := mem_transvections_iff.mp ht
  intro ho
  let a := f w*g v
  have ha : a=0 ∨ a=1 ∨ a^2+a+1=0 := by
    by_cases h0 : a=0
    · exact Or.inl h0
    by_cases h1 : a=1
    · exact Or.inr (Or.inl h1)
    right; right
    let := Fintype.ofFinite F
    have hpow : a^3=1 := by
      simpa only [←Nat.card_eq_fintype_card,hF] using FiniteField.pow_card_sub_one_eq_one a h0
    have he : (a-1)*(a^2+a+1)=0 := by linear_combination hpow
    exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr h1)
  rcases ha with h | h | h
  · have hh := orderOf_dvd_of_pow_eq_one (pair_four f g v w hf hg h)
    rw [ho] at hh
    norm_num at hh
  · have hh := orderOf_dvd_of_pow_eq_one (pair_cube f g v w hf hg h)
    rw [ho] at hh
    norm_num at hh
  · have hh := orderOf_dvd_of_pow_eq_one (pair_five f g v w hf hg h)
    rw [ho] at hh
    norm_num at hh
end LinearEquiv
