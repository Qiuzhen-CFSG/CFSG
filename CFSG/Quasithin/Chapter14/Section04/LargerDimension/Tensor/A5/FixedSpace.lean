module

public import Theory.Representation.BinaryPermutation.CubicFixedSpace.Five

/-!
# The A₅ Borel fixes the Sylow-fixed line

In the binary augmentation core on five letters, the regular Klein four
fixes precisely zero and the word (1,1,1,1,0). Its normalizer preserves
that one-dimensional fixed space, hence fixes it pointwise. The coordinate
certificate tests just the 32 binary words; the normalizer argument is
structural. This is the model calculation underlying X₂ centralizing
Ṽ₂ in Aschbacher–Smith 14.4.10(3), printed p.1011.

An application to the source still requires its actual constituent marking
and the image of the literal Borel `Tensor.borel H T`.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.A5
open BinaryPermutation
open BinaryPermutation.CubicFixedSpace.Five

private def pointWord : Full (Fin 5) := ![1, 1, 1, 1, 0]
private def point : core (Fin 5) := ⟨pointWord, by
  change (∑ k, pointWord k) = 0
  decide +kernel⟩

private theorem fixed_core_cases (v : core (Fin 5))
    (hv : v ∈ fixedSpace ((coreRepresentation (Fin 5)).comp
      (alternatingGroup (Fin 5)).subtype) klein) : v = 0 ∨ v = point := by
  have h : ∀ v : Full (Fin 5), (∑ k, v k) = 0 →
      (∀ k, v (first.val.symm k) = v k) →
      (∀ k, v (second.val.symm k) = v k) →
      v = 0 ∨ v = pointWord := by decide +kernel
  rcases h v v.property
    (fun k => congrArg (fun w : core (Fin 5) => w.val k) (hv ⟨first, first_mem⟩))
    (fun k => congrArg (fun w : core (Fin 5) => w.val k) (hv ⟨second, second_mem⟩)) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem borel_fixes_core (g : alternatingGroup (Fin 5))
    (hg : g ∈ normalizer (klein : Set (alternatingGroup (Fin 5))))
    (v : core (Fin 5))
    (hv : v ∈ fixedSpace ((coreRepresentation (Fin 5)).comp
      (alternatingGroup (Fin 5)).subtype) klein) :
    coreRepresentation (Fin 5) g.val v = v := by
  let ρ := (coreRepresentation (Fin 5)).comp (alternatingGroup (Fin 5)).subtype
  have hinv (w : core (Fin 5)) : ρ g⁻¹ (ρ g w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hfixed : ρ g v ∈ fixedSpace ρ klein := by
    intro k
    have hk : g⁻¹ * k.val * g ∈ klein := by
      simpa only [inv_inv] using (mem_normalizer_iff.mp (inv_mem hg) k.val).mp k.property
    have h : ρ g (ρ (g⁻¹ * k.val * g) v) = ρ g v :=
      congrArg (ρ g) (hv ⟨g⁻¹ * k.val * g, hk⟩)
    have he : g * (g⁻¹ * k.val * g) = k.val * g := by group
    rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply] at h
    exact h
  by_cases hz : v = 0
  · subst v
    exact map_zero _
  have hne : ρ g v ≠ 0 := by
    intro he
    apply hz
    rw [← hinv v, he, map_zero]
  have h₁ := (fixed_core_cases v hv).resolve_left hz
  have h₂ := (fixed_core_cases (ρ g v) hfixed).resolve_left hne
  exact h₂.trans h₁.symm

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.A5

end
