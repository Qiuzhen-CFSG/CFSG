module

public import Theory.SpecificGroups.SL2.Affine
public import Mathlib.Tactic.FinCases

/-!
# Faithfulness and irreducibility of the natural affine action

Completing a nonzero column to a determinant-one matrix shows that SL₂(F)
is transitive on the nonzero vectors. Hence every invariant additive subgroup
of F² is trivial or the whole group, including after restriction of scalars.
The action is faithful because a matrix is determined by its action on vectors.

The column calculation is the one used in `SL2.TwoCore`; these action facts
support the natural local blocks in Aschbacher–Smith, C.1.7 and F.1.12(I)(1).
-/

@[expose] public section
open Matrix
open scoped MatrixGroups
namespace Matrix.SL2
variable (F : Type*) [Field F]

theorem naturalAction_injective : Function.Injective (naturalAction F) := by
  intro g h he
  apply SpecialLinearGroup.toLin'_injective
  ext v : 1
  exact congrArg (fun a : MulAut (Multiplicative (Fin 2 → F)) =>
    Multiplicative.toAdd (a (Multiplicative.ofAdd v))) he

private theorem exists_first_column (v : Fin 2 → F) (hv : v ≠ 0) :
    ∃ g : SL(2, F), g • (![1,0] : Fin 2 → F) = v := by
  by_cases h : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1; apply hv; ext i; fin_cases i <;> simp_all
    refine ⟨⟨!![v 0, -(v 1)⁻¹; v 1, 0], by simp [det_fin_two, h1]⟩, ?_⟩
    change (!![v 0, -(v 1)⁻¹; v 1, 0] *ᵥ ![1,0]) = v
    ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], by simp [det_fin_two, h]⟩, ?_⟩
    change (!![v 0, 0; v 1, (v 0)⁻¹] *ᵥ ![1,0]) = v
    ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

/-- SL₂ is transitive on the nonzero vectors, over any field. -/
theorem exists_mulVec_eq (v w : Fin 2 → F) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : SL(2, F), g.val *ᵥ v = w := by
  obtain ⟨a, ha⟩ := exists_first_column F v hv
  obtain ⟨b, hb⟩ := exists_first_column F w hw
  refine ⟨b * a⁻¹, ?_⟩
  change (b * a⁻¹) • v = w
  rw [← ha, mul_smul, inv_smul_smul, hb]

/-- Invariant additive subgroups of the natural plane are zero or the whole plane.
This is stronger than irreducibility over the defining field. -/
theorem naturalAction_irreducible (V : Subgroup (Multiplicative (Fin 2 → F)))
    (hV : ∀ g v, v ∈ V → naturalAction F g v ∈ V) : V = ⊥ ∨ V = ⊤ := by
  rcases V.bot_or_exists_ne_one with h | ⟨v, hv, hv1⟩
  · exact Or.inl h
  · right
    apply top_unique
    intro w _
    by_cases hw : w = 1
    · subst w
      exact V.one_mem
    obtain ⟨g, hg⟩ := exists_mulVec_eq F (Multiplicative.toAdd v)
      (Multiplicative.toAdd w) (fun h => hv1 (Multiplicative.toAdd.injective h))
      (fun h => hw (Multiplicative.toAdd.injective h))
    have he : naturalAction F g v = w := Multiplicative.toAdd.injective hg
    exact he ▸ hV g v hv
end Matrix.SL2
