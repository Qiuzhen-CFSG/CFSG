module

public import Theory.Representation.SpecialLinearNatural
import Mathlib.Tactic.FinCases

/-!
# The actual natural action of SL₂

The action is literal matrix multiplication, expressed multiplicatively for
quotient groups. Completing two nonzero columns to determinant-one matrices
proves transitivity on nonzero vectors over every field.

Source: the natural-module condition of Aschbacher–Smith C.1.12, printed p.124.
-/

@[expose] public section

namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F]

private theorem exists_column (v : Fin 2 → F) (hv : v ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, g • Pi.single 0 (1 : F) = v := by
  have hc : IsCoprime (v 0) (v 1) := by
    rw [Semifield.isCoprime_iff]
    by_contra h
    push Not at h
    apply hv
    ext i
    fin_cases i <;> simp_all
  obtain ⟨g, h0, h1⟩ := hc.exists_SL2_col 0
  refine ⟨g, ?_⟩
  change Matrix.mulVec g.val (Pi.single 0 1) = v
  rw [Matrix.mulVec_single_one]
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- SL₂ is transitive on the nonzero vectors of its literal natural module. -/
theorem natural_transitive {v w : Fin 2 → F} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, Matrix.mulVec g.val v = w := by
  obtain ⟨a, ha⟩ := exists_column v hv
  obtain ⟨b, hb⟩ := exists_column w hw
  refine ⟨b * a⁻¹, ?_⟩
  change (b * a⁻¹) • v = w
  rw [← ha, mul_smul, inv_smul_smul, hb]
/-- The additive natural action, written as a multiplicative group action. -/
def naturalAction : Matrix.SpecialLinearGroup (Fin 2) F →*
    MulAut (Multiplicative (Fin 2 → F)) where
  toFun g := AddEquiv.toMultiplicative (Matrix.SpecialLinearGroup.toLin' g).toAddEquiv
  map_one' := by
    apply MulEquiv.ext
    intro v
    apply Multiplicative.toAdd.injective
    change Matrix.mulVec (1 : Matrix (Fin 2) (Fin 2) F) _ = _
    simp
  map_mul' g h := by
    apply MulEquiv.ext
    intro v
    apply Multiplicative.toAdd.injective
    change Matrix.mulVec (g.val * h.val) _ = Matrix.mulVec g.val (Matrix.mulVec h.val _)
    exact Matrix.mulVec_mulVec _ _ _ |>.symm

@[simp] theorem naturalAction_apply (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (v : Multiplicative (Fin 2 → F)) :
    Multiplicative.toAdd (naturalAction g v) = Matrix.mulVec g.val (Multiplicative.toAdd v) := rfl
end Theory.SpecificGroups.SymplecticFour
