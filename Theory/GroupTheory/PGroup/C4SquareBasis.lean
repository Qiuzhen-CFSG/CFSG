module

public import Theory.GroupAction.C4SquareAutomorphismOrder
public import Theory.GroupTheory.PGroup.OmegaImage
import Mathlib.Tactic

/-!
# A basis and its omega four in a C₄-square

An explicit isomorphism with C₄ × C₄ gives two commuting generators of
exponent four. Their squares generate the first omega subgroup, so an
ambiently specified omega four is identified without a uniqueness argument.
The proof transports the sixteen coordinate normal forms and the four
square-trivial elements of the coordinate model.

This supplies the marked base for the extension recognition in
Janko–Thompson, Math. Z. 113 (1970), 1.4(c), printed p.386.
-/

open Subgroup
namespace C4SquareExtension
private def u : Model := (Multiplicative.ofAdd 1, 1)
private def v : Model := (1, Multiplicative.ofAdd 1)
private theorem decomp : ∀ x : Model, ∃ i j : Fin 4, x = u ^ i.val * v ^ j.val := by
  decide
private theorem squares : ∀ x : Model, x ^ 2 = 1 →
    x = 1 ∨ x = u ^ 2 ∨ x = v ^ 2 ∨ x = u ^ 2 * v ^ 2 := by decide
private theorem model_generate : closure ({u,v} : Set Model) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨i,j,rfl⟩ := decomp x
  exact mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (subset_closure (by simp)) _)
private theorem model_omega : omega₁ Model (p := 2) = closure ({u ^ 2,v ^ 2} : Set Model) := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    rcases squares x (by simpa using hx) with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  · apply (closure_le _).mpr
    intro x hx
    rcases (by simpa using hx : x = u ^ 2 ∨ x = v ^ 2) with rfl | rfl
    · exact subset_closure (by decide)
    · exact subset_closure (by decide)

/-- Choose a basis of a C₄-square and identify its ambient omega four. -/
public theorem exists_basis {P : Type*} [Group P] (D W : Subgroup P)
    (e : D ≃* Model) (hO : (omega₁ D (p := 2)).map D.subtype = W) :
    ∃ a b : P, a ^ 4 = 1 ∧ b ^ 4 = 1 ∧ Commute a b ∧
      D = closure ({a,b} : Set P) ∧ W = closure ({a ^ 2,b ^ 2} : Set P) := by
  let f : Model →* P := D.subtype.comp e.symm.toMonoidHom
  refine ⟨f u, f v, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, show u ^ 4 = 1 by decide, map_one]
  · rw [← map_pow, show v ^ 4 = 1 by decide, map_one]
  · exact (Commute.all u v).map f
  · have hr : f.range = D := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact (e.symm y).property
      · intro hx
        exact ⟨e ⟨x,hx⟩, by simp [f]⟩
    have hh := congrArg (Subgroup.map f) model_generate
    rw [← MonoidHom.range_eq_map, hr] at hh
    simpa [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      f, Subgroup.map_map] using hh.symm
  · rw [← hO]
    change (omega D (p := 2) 1).map D.subtype = _
    rw [← e.symm.map_omega 2 1, Subgroup.map_map]
    change (omega₁ Model (p := 2)).map f = _
    rw [model_omega]
    simp [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      map_pow, f]
end C4SquareExtension
