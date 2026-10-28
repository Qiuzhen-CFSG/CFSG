module

public import Theory.Representation.G2Natural

/-!
# The adjoint action of the actual split-octonion G₂ group

The carrier is the space of derivations of the explicit octonion multiplication.
Multiplication need not be associative: the Leibniz equation defines a linear
subspace of the endomorphism space. Conjugation by an octonion automorphism
preserves this equation and gives the adjoint representation of `Atlas.G2.Model`.

Source: GLS3, Examples 1.14.9(c) and 2.8.10(g), with the concrete split-octonion
model from the attributed ATLAS imports. Dimension and irreducibility of this
carrier are separate mathematical obligations.
-/

@[expose] public section

namespace Atlas.G2.Restricted.Adjoint

open Atlas.SplitOctonion

variable (F : Type*) [Field F]

/-- Derivations of the split octonions, using their actual nonassociative product. -/
def derivations : Submodule F (Module.End F (Carrier F)) where
  carrier := { D | ∀ x y, D (mul x y) = mul (D x) y + mul x (D y) }
  zero_mem' := by
    intro x y
    ext i
    fin_cases i <;> simp [mul]
  add_mem' := by
    intro D E hD hE x y
    simp only [LinearMap.add_apply, hD x y, hE x y, Atlas.SplitOctonion.add_mul,
      Atlas.SplitOctonion.mul_add]
    abel
  smul_mem' := by
    intro a D hD x y
    simp only [LinearMap.smul_apply, hD x y, smul_add, Atlas.SplitOctonion.smul_mul,
      Atlas.SplitOctonion.mul_smul]

/-- The concrete adjoint carrier. -/
abbrev Space := derivations F

@[simp] theorem mem_derivations (D : Module.End F (Carrier F)) :
    D ∈ derivations F ↔ ∀ x y, D (mul x y) = mul (D x) y + mul x (D y) := Iff.rfl

/-- Conjugation on the full octonion endomorphism space. -/
def ambientAction : Representation F (Model F) (Module.End F (Carrier F)) :=
  (Natural.ambient F).linHom (Natural.ambient F)

@[simp] theorem ambientAction_apply (g : Model F) (D : Module.End F (Carrier F))
    (x : Carrier F) : ambientAction F g D x = g.val (D ((g⁻¹).val x)) := rfl

/-- Conjugating a derivation by an actual octonion automorphism is a derivation. -/
theorem ambientAction_mem (g : Model F) (D : Module.End F (Carrier F))
    (hD : D ∈ derivations F) : ambientAction F g D ∈ derivations F := by
  intro x y
  change g.val (D ((g⁻¹).val (mul x y))) =
    mul (g.val (D ((g⁻¹).val x))) y + mul x (g.val (D ((g⁻¹).val y)))
  rw [automorphism_mul, hD, map_add, automorphism_mul, automorphism_mul]
  have hi (z : Carrier F) : g.val ((g⁻¹).val z) = z := g.val.apply_symm_apply z
  rw [hi, hi]

/-- The adjoint representation on genuine octonion derivations. -/
def action : Representation F (Model F) (Space F) :=
  (ambientAction F).subrepresentation (derivations F) (ambientAction_mem F)

@[simp] theorem action_val (g : Model F) (D : Space F) :
    (action F g D).val = ambientAction F g D.val := rfl

/-- Explicit conjugation formula for the adjoint action. -/
theorem action_apply (g : Model F) (D : Space F) (x : Carrier F) :
    (action F g D).val x = g.val (D.val ((g⁻¹).val x)) := rfl

/-- The derivation equation itself is retained on the carrier. -/
theorem leibniz (D : Space F) (x y : Carrier F) :
    D.val (mul x y) = mul (D.val x) y + mul x (D.val y) := D.property x y

end Atlas.G2.Restricted.Adjoint
