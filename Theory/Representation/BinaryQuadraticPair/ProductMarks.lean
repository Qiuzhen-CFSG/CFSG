module

public import Theory.Representation.BinaryQuadraticPair

/-!
# A fixed-free odd element from quadratic product marks

For two independently marked transpositions in S₃ × S₃, and an element
of A₃ × A₃, the word table defines a diagonal S₃ homomorphism. Both
involutions fix the first mark and have displacement there, so their
product does too. Complementarity of the mark and its odd translate
lets the binary quadratic-pair theorem eliminate every vector fixed by
that odd element. In particular the common A₃ × A₃ fixed space is zero.

This is the fixed-space step needed in Aschbacher–Smith G.2.6(5), printed
p.336. It uses the marked configuration, not two-perfectness of an actor.
The six-word calculation is checked by the Lean kernel.
-/

@[expose] public section
open InvertedCubicTensor
namespace Representation.BinaryQuadraticPair

private def wordMap (t a x : S₃) : S₃ :=
  if x = 1 then 1 else if x = cubic then a else if x = cubic * cubic then a * a
  else if x = inverter then t else if x = cubic * inverter then a * t else a * a * t

private theorem wordMap_mul :
    ∀ t a : S₃, t * t = 1 → t ≠ 1 → a ∈ alternatingGroup (Fin 3) →
      ∀ x y : S₃, wordMap t a (x * y) = wordMap t a x * wordMap t a y := by
  change ∀ t a : S₃, t * t = 1 → t ≠ 1 → Equiv.Perm.sign a = 1 →
    ∀ x y : S₃, wordMap t a (x * y) = wordMap t a x * wordMap t a y
  decide +kernel

private def markedHom (t a : S₃) (ht : t * t = 1) (ht1 : t ≠ 1)
    (ha : a ∈ alternatingGroup (Fin 3)) : S₃ →* S₃ where
  toFun := wordMap t a
  map_one' := by simp [wordMap]
  map_mul' := wordMap_mul t a ht ht1 ha

private theorem markedHom_inverter (t a : S₃) (ht : t * t = 1) (ht1 : t ≠ 1)
    (ha : a ∈ alternatingGroup (Fin 3)) : markedHom t a ht ht1 ha inverter = t := by
  simp [markedHom, wordMap, show inverter ≠ 1 by decide +kernel,
    show inverter ≠ cubic by decide +kernel,
    show inverter ≠ cubic * cubic by decide +kernel]

private theorem markedHom_cubic (t a : S₃) (ht : t * t = 1) (ht1 : t ≠ 1)
    (ha : a ∈ alternatingGroup (Fin 3)) : markedHom t a ht ht1 ha cubic = a := by
  simp [markedHom, wordMap, show cubic ≠ 1 by decide +kernel]

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

/-- The marked quadratic configuration, before any module recognition. -/
structure ProductMark (ρ : Representation (ZMod 2) (S₃ × S₃) M)
    (A : Submodule (ZMod 2) M) (t₁ t₂ : S₃) (a : S₃ × S₃) : Prop where
  left_square : t₁ * t₁ = 1
  left_ne_one : t₁ ≠ 1
  right_square : t₂ * t₂ = 1
  right_ne_one : t₂ ≠ 1
  even : a ∈ (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))
  left_fixed : ∀ v ∈ A, ρ (t₁, 1) v = v
  right_fixed : ∀ v ∈ A, ρ (1, t₂) v = v
  left_range : LinearMap.range (ρ (t₁, 1) - 1) ≤ A
  right_range : LinearMap.range (ρ (1, t₂) - 1) ≤ A
  complementary : IsCompl A (A.map (ρ a))

namespace ProductMark
variable {ρ : Representation (ZMod 2) (S₃ × S₃) M}
  {A : Submodule (ZMod 2) M} {t₁ t₂ : S₃} {a : S₃ × S₃}
  (h : ProductMark ρ A t₁ t₂ a)
include h

/-- The mixed identity concerns the two independently marked involutions. -/
theorem mixed_quadratic : (ρ (t₁, 1) - 1) * (ρ (1, t₂) - 1) = 0 := by
  ext v
  change ρ (t₁, 1) ((ρ (1, t₂) - 1) v) - (ρ (1, t₂) - 1) v = 0
  exact sub_eq_zero.mpr (h.left_fixed _ (h.right_range ⟨v, rfl⟩))

private theorem diagonal_range : LinearMap.range (ρ (t₁, t₂) - 1) ≤ A := by
  rintro _ ⟨v, rfl⟩
  have h₁ : ρ (t₁, 1) v - v ∈ A := h.left_range ⟨v, rfl⟩
  have h₂ : ρ (1, t₂) v - v ∈ A := h.right_range ⟨v, rfl⟩
  have he : (ρ (t₁, t₂) - 1) v =
      (ρ (1, t₂) v - v) + (ρ (t₁, 1) v - v) := by
    have hf := h.left_fixed _ h₂
    rw [map_sub] at hf
    have hm : ρ (t₁, t₂) v = ρ (t₁, 1) (ρ (1, t₂) v) := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    change ρ (t₁, t₂) v - v = _
    rw [hm]
    rw [← hf]
    abel
  rw [he]
  exact A.add_mem h₂ h₁

/-- Complementary marks eliminate the common fixed part; no perfectness
hypothesis is used to infer a false fixed-space assertion. -/
theorem fixedFree : ∀ v, ρ a v = v → v = 0 := by
  let j : S₃ →* S₃ × S₃ :=
    (markedHom t₁ a.1 h.left_square h.left_ne_one h.even.1).prod
      (markedHom t₂ a.2 h.right_square h.right_ne_one h.even.2)
  have hjt : j inverter = (t₁, t₂) := by
    exact Prod.ext (markedHom_inverter ..) (markedHom_inverter ..)
  have hja : j cubic = a := by
    exact Prod.ext (markedHom_cubic ..) (markedHom_cubic ..)
  have htfix : ∀ v ∈ A, (ρ.comp j) inverter v = v := by
    intro v hv
    change ρ (j inverter) v = v
    rw [hjt]
    have hm : ρ (t₁, t₂) = ρ (t₁, 1) * ρ (1, t₂) := by
      rw [← map_mul]
      simp
    rw [hm, Module.End.mul_apply, h.right_fixed v hv, h.left_fixed v hv]
  have hr : LinearMap.range ((ρ.comp j) inverter - 1) ≤ A := by
    change LinearMap.range (ρ (j inverter) - 1) ≤ A
    rw [hjt]
    exact h.diagonal_range
  have hc : IsCompl A (A.map ((ρ.comp j) cubic)) := by
    change IsCompl A (A.map (ρ (j cubic)))
    rw [hja]
    exact h.complementary
  have hh := (fixed_cubic_and_displacement (ρ.comp j) A inverter cubic
    inverter_square (by decide +kernel) htfix hr hc).1
  intro v hv
  apply hh v
  change ρ (j cubic) v = v
  rwa [hja]

/-- The literal full odd subgroup has zero fixed space. -/
theorem common_fixed_eq_bot : Representation.BinaryOffender.fixedSpace ρ
    ((alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))) = ⊥ := by
  apply bot_unique
  intro v hv
  exact h.fixedFree v (hv ⟨a, h.even⟩)

end ProductMark
end Representation.BinaryQuadraticPair
