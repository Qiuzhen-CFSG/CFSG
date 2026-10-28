module
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Tactic.Group

/-!
# Extending an alternating-group section through a marked involution

Fix a transposition σ and an alternating-group section a of a homomorphism q.
An involution τ above σ extends a to a section of the full symmetric group when
its conjugation agrees with σ on a. Write each permutation uniquely as an even
permutation g or as gσ; the extension sends these to a(g) and a(g)τ. The four
multiplication cases use precisely the prescribed conjugation and τ² = 1.

The section retains both the original alternating marking and the exact chosen
odd involution. The involution hypothesis is essential; a lift of an odd
permutation with order four need not give a symmetric-group section.

Source application: Aschbacher–Smith 2.4.29, the marked A₅-to-S₅ extension.
-/

public noncomputable section
open Subgroup Equiv.Perm
namespace AlternatingIndexTwoSection
variable {Ω H : Type*} [Fintype Ω] [DecidableEq Ω] [Group H]

private theorem odd_mul_swap_mem (σ : Equiv.Perm Ω) (hσ : σ.IsSwap)
    (x : Equiv.Perm Ω) (hx : x ∉ alternatingGroup Ω) : x * σ ∈ alternatingGroup Ω := by
  have hs : sign x = -1 := (Int.units_eq_one_or (sign x)).resolve_left
    (fun h => hx (mem_alternatingGroup.mpr h))
  simp only [mem_alternatingGroup,map_mul,hs,hσ.sign_eq,neg_mul_neg,one_mul]

private def extensionFun (a : alternatingGroup Ω →* H) (σ : Equiv.Perm Ω)
    (hσ : σ.IsSwap) (τ : H) (x : Equiv.Perm Ω) : H := by
  classical
  exact if hx : x ∈ alternatingGroup Ω then a ⟨x,hx⟩
  else a ⟨x*σ,odd_mul_swap_mem σ hσ x hx⟩ * τ

private theorem extension_even (a : alternatingGroup Ω →* H) (σ : Equiv.Perm Ω)
    (hσ : σ.IsSwap) (τ : H) (g : alternatingGroup Ω) :
    extensionFun a σ hσ τ g = a g := by
  simp only [extensionFun,dif_pos g.property]

private theorem extension_odd (a : alternatingGroup Ω →* H) (σ : Equiv.Perm Ω)
    (hσ : σ.IsSwap) (τ : H) (g : alternatingGroup Ω) :
    extensionFun a σ hσ τ (g*σ) = a g * τ := by
  have hn : (g : Equiv.Perm Ω)*σ ∉ alternatingGroup Ω := by
    rw [mem_alternatingGroup,map_mul,mem_alternatingGroup.mp g.property,hσ.sign_eq,one_mul]
    decide
  have hσσ : σ*σ = 1 := by
    have hh := pow_orderOf_eq_one σ
    rw [hσ.orderOf,pow_two] at hh
    exact hh
  simp only [extensionFun,dif_neg hn]
  congr 2
  apply Subtype.ext
  exact (mul_assoc _ _ _).trans (by rw [hσσ,mul_one])

private theorem normal_forms (σ : Equiv.Perm Ω) (hσ : σ.IsSwap) (x : Equiv.Perm Ω) :
    (∃ g : alternatingGroup Ω, x = g) ∨ (∃ g : alternatingGroup Ω, x = g*σ) := by
  by_cases hx : x ∈ alternatingGroup Ω
  · exact Or.inl ⟨⟨x,hx⟩,rfl⟩
  · right
    refine ⟨⟨x*σ,odd_mul_swap_mem σ hσ x hx⟩,?_⟩
    have hh := pow_orderOf_eq_one σ
    rw [hσ.orderOf,pow_two] at hh
    simp only [mul_assoc,hh,mul_one]

/-- An alternating-group section extends through a prescribed involution
that realizes the conjugation action of a transposition. -/
theorem exists_section_extending_alternating
    (q : H →* Equiv.Perm Ω) (a : alternatingGroup Ω →* H)
    (ha : q.comp a = (alternatingGroup Ω).subtype)
    (σ : Equiv.Perm Ω) (hσ : σ.IsSwap) (τ : H) (hτ : τ^2=1)
    (hqτ : q τ = σ)
    (hconj : ∀ g : alternatingGroup Ω,
      τ*a g*τ⁻¹ = a (MulAut.conjNormal σ g)) :
    ∃ s : Equiv.Perm Ω →* H, q.comp s = MonoidHom.id _ ∧
      s.comp (alternatingGroup Ω).subtype = a ∧ s σ = τ := by
  have hτinv : τ⁻¹=τ := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hτ)
  have hσinv : σ⁻¹=σ := by
    apply inv_eq_of_mul_eq_one_right
    have hh := pow_orderOf_eq_one σ
    rwa [hσ.orderOf,pow_two] at hh
  let f := extensionFun a σ hσ τ
  have heven (g : alternatingGroup Ω) : f g = a g := extension_even a σ hσ τ g
  have hodd (g : alternatingGroup Ω) : f (g*σ) = a g*τ := extension_odd a σ hσ τ g
  have hmul (x y : Equiv.Perm Ω) : f (x*y) = f x*f y := by
    rcases normal_forms σ hσ x with ⟨g,rfl⟩ | ⟨g,rfl⟩ <;>
      rcases normal_forms σ hσ y with ⟨h,rfl⟩ | ⟨h,rfl⟩
    · change f ((g*h : alternatingGroup Ω) : Equiv.Perm Ω) = _
      rw [heven,heven,heven,map_mul]
    · rw [← mul_assoc]
      change f (((g*h : alternatingGroup Ω) : Equiv.Perm Ω)*σ) = _
      rw [hodd,heven,hodd,map_mul,mul_assoc]
    · have hm : (g : Equiv.Perm Ω)*σ*h =
          ((g*(MulAut.conjNormal σ h) : alternatingGroup Ω) : Equiv.Perm Ω)*σ := by
        simp only [Subgroup.coe_mul,MulAut.conjNormal_apply,mul_assoc,inv_mul_cancel,mul_one]
      rw [hm,hodd,hodd,heven,map_mul,← hconj]
      group
    · have hm : ((g : Equiv.Perm Ω)*σ)*(h*σ) =
          ((g*(MulAut.conjNormal σ h) : alternatingGroup Ω) : Equiv.Perm Ω) := by
        simp only [Subgroup.coe_mul,MulAut.conjNormal_apply,hσinv,mul_assoc]
      rw [hm,heven,hodd,hodd,map_mul,← hconj,hτinv]
      group
  let s : Equiv.Perm Ω →* H :=
    { toFun := f
      map_one' := by simpa only [Subgroup.coe_one,map_one] using heven 1
      map_mul' := hmul }
  refine ⟨s,?_,?_,?_⟩
  · apply MonoidHom.ext
    intro x
    change q (f x) = x
    rcases normal_forms σ hσ x with ⟨g,rfl⟩ | ⟨g,rfl⟩
    · rw [heven]
      exact DFunLike.congr_fun ha g
    · rw [hodd,map_mul,hqτ]
      exact congrArg (fun z => z*σ) (DFunLike.congr_fun ha g)
  · apply MonoidHom.ext
    exact heven
  · change f σ = τ
    simpa only [Subgroup.coe_one,one_mul,map_one] using hodd 1

end AlternatingIndexTwoSection
end
