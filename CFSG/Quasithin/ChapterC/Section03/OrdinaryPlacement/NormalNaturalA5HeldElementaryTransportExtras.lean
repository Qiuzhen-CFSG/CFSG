module

public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryTransport

/-!
# Returning native Held subgroup data to the original subgroup

Purity and normalizer order survive conjugation, and containment in a conjugate
core can be pulled back through the same conjugating element. These transports
retain the original subgroup in the ordinary case of Aschbacher--Smith 12.7.5.
-/

public section
open Subgroup
namespace Held.OrdinaryElementary

/-- A conjugate of a subgroup with no class-A elements has no class-A elements. -/
theorem pure_map_conj (E : Subgroup He) (g : He)
    (h : ∀ x : E, ¬ IsConj a (x : He)) :
    ∀ x : E.map (MulAut.conj g).toMonoidHom, ¬ IsConj a (x : He) := by
  intro x hx
  obtain ⟨y, hy, he⟩ := x.property
  have hc : IsConj y (x : He) := isConj_iff.mpr ⟨g, he⟩
  exact h ⟨y, hy⟩ (hx.trans hc.symm)

/-- Full ambient normalizers of conjugate subgroups have equal orders. -/
theorem normalizer_card_map_conj (E : Subgroup He) (g : He) :
    Nat.card (normalizer (E.map (MulAut.conj g).toMonoidHom : Set He)) =
      Nat.card (normalizer (E : Set He)) := by
  rw [← map_equiv_normalizer_eq E (MulAut.conj g)]
  exact card_map_of_injective (MulAut.conj g).injective

/-- Pull back a native conjugate containment to the unchanged original subgroup. -/
theorem le_map_conj_of_map_conj_le (E Q : Subgroup He) (g k : He)
    (h : E.map (MulAut.conj g).toMonoidHom ≤ Q.map (MulAut.conj k).toMonoidHom) :
    E ≤ Q.map (MulAut.conj (g⁻¹ * k)).toMonoidHom := by
  intro x hx
  obtain ⟨y, hy, he⟩ := h (mem_map.mpr ⟨x, hx, rfl⟩)
  refine mem_map.mpr ⟨y, hy, ?_⟩
  change (MulAut.conj k) y = (MulAut.conj g) x at he
  have hh := congrArg (MulAut.conj g).symm he
  change (MulAut.conj (g⁻¹ * k)) y = x
  simpa only [MulEquiv.symm_apply_apply, MulAut.conj_apply,
    MulAut.conj_symm_apply, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel,
    mul_one, inv_mul_cancel_left] using hh

end Held.OrdinaryElementary
