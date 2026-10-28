module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Elementary
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Determinant
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Spinor.Character
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Spinor.Intrinsic
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Spinor.CoordinateValues

/-!
# Determinant and reflection characters on the literal minus complement

A single coordinate hyperbolic pair represents every field value, so the
full complementary orthogonal commutator has index at most four, including
in dimension four over F₃. A square-class character with the standard
reflection values identifies this commutator together with determinant.

Wall's intrinsic spinor character and the proved coordinate calculations
discharge the premises of the retained conditional interfaces. Identity
extension preserves the spinor norm and reflects Omega membership. Negation
belongs to Omega exactly when `(-1)^(r+1) * (1 + 4 * parameter F)` is square.
These conclusions hold for every `r ≥ 1` over every finite odd field,
including the four-dimensional complement over F₃. Omega retains its
definition as the full orthogonal commutator throughout.

Sources: GLS3 §2.7, printed pp.88–89; Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup
namespace ClassicalOrthogonal.Fundamental.MinusCentralizer
open ClassicalOrthogonal.SpinorInvariants
variable {F : Type*} [Field F] [Finite F]

/-- The first actual hyperbolic coordinate represents every field value. -/
theorem complement_represents (r : ℕ) (hr : 1 ≤ r) (c : F) :
    ∃ a : Minus.Space F r, Minus.quadraticForm F (r + 1) a = c := by
  classical
  let i : Fin r := ⟨0, by omega⟩
  refine ⟨(fun j => (if j = i then 1 else 0, if j = i then c else 0), 0), ?_⟩
  simp [Minus.quadraticForm, i]

/-- The literal complementary Omega has index at most four, without a
Witt-index-two or elementary-generation hypothesis. -/
theorem complement_omega_index_le_four (r : ℕ) (hr : 1 ≤ r) (h2 : (2 : F) ≠ 0) :
    (Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1))).index ≤ 4 :=
  card_abelianization_le_four _ (Minus.quadraticForm_nonsingular F (r + 1)) h2
    (fun c _ => complement_represents r hr c)

/-- The full commutator comparison on the literal complementary carrier.
The existence of the reflection character remains a separate premise. -/
theorem complement_mem_omega_iff_det_character (r : ℕ) (hr : 1 ≤ r) (h2 : (2 : F) ≠ 0)
    (χ : ReflectionCharacter (Minus.quadraticForm F (r + 1)))
    (u : Minus.Orthogonal F (Minus.Space F r) (Minus.quadraticForm F (r + 1))) :
    u ∈ Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) ↔
      LinearEquiv.det u.val = 1 ∧ χ.hom u = 1 :=
  mem_commutator_iff_det_character _ (Minus.quadraticForm_nonsingular F (r + 1)) h2 χ
    (fun c _ => complement_represents r hr c) u

/-- The actual block restriction follows from the character's identity-extension
calculation and the already proved determinant calculation. -/
theorem complement_mem_omega_of_fullBlock_mem_of_characters
    (r : ℕ) (hr : 1 ≤ r) (h2 : (2 : F) ≠ 0)
    (χ : ReflectionCharacter (Minus.quadraticForm F (r + 1)))
    (ψ : ReflectionCharacter (Minus.quadraticForm F (r + 3)))
    (hext : ∀ u : Minus.Orthogonal F (Minus.Space F r) (Minus.quadraticForm F (r + 1)),
      ψ.hom (fullBlockHom r (1, u)) = χ.hom u)
    (u : Minus.Orthogonal F (Minus.Space F r) (Minus.quadraticForm F (r + 1)))
    (hu : fullBlockHom r (1, u) ∈
      Minus.Omega F (Minus.Space F (r + 2)) (Minus.quadraticForm F (r + 3))) :
    u ∈ Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) := by
  apply (complement_mem_omega_iff_det_character r hr h2 χ u).mpr
  refine ⟨complement_det_eq_one_of_fullBlock_mem_omega r u hu, ?_⟩
  rw [← hext u]
  exact Abelianization.commutator_subset_ker
    (G := quadraticIsometrySubgroup (Minus.quadraticForm F (r + 3)))
    (A := Atlas.SquareClass F) ψ.hom hu

/-- On the even-dimensional complement, the character alone detects whether
negation lies in the literal commutator. -/
theorem negativeComplement_mem_omega_iff_character
    (r : ℕ) (hr : 1 ≤ r) (h2 : (2 : F) ≠ 0)
    (χ : ReflectionCharacter (Minus.quadraticForm F (r + 1))) :
    negativeComplement (F := F) r ∈
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) ↔
      χ.hom (negativeComplement r) = 1 := by
  rw [complement_mem_omega_iff_det_character r hr h2 χ, negativeComplement_det]
  exact ⟨And.right, fun h => ⟨rfl, h⟩⟩

/-- The scalar source criterion once the character's concrete negation value
has been computed on the published minus coordinates. -/
theorem negativeComplement_mem_omega_iff_of_character_value
    (r : ℕ) (hr : 1 ≤ r) (h2 : (2 : F) ≠ 0)
    (χ : ReflectionCharacter (Minus.quadraticForm F (r + 1)))
    (hd : (-1 : F) ^ (r + 1) * (1 + 4 * Minus.parameter F) ≠ 0)
    (hval : χ.hom (negativeComplement r) = Atlas.squareClass F
      (Units.mk0 ((-1 : F) ^ (r + 1) * (1 + 4 * Minus.parameter F)) hd)) :
    negativeComplement (F := F) r ∈
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) ↔
      IsSquare ((-1 : F) ^ (r + 1) * (1 + 4 * Minus.parameter F)) := by
  rw [negativeComplement_mem_omega_iff_character r hr h2 χ, hval,
    Atlas.squareClass_mk0_eq_one]

/-- The literal complementary commutator is the common kernel of determinant
and the constructed intrinsic spinor norm. No character-existence premise remains. -/
theorem complement_omega_eq_det_spinor_kernel
    (r : ℕ) (hr : 1 ≤ r) (h2 : (2 : F) ≠ 0) :
    Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) =
      (determinantCharacter (Minus.quadraticForm F (r + 1))
        (Minus.quadraticForm_nonsingular F (r + 1)) h2
        (minusReflectionCharacter F r h2)).ker :=
  commutator_eq_determinantCharacter_kernel _
    (Minus.quadraticForm_nonsingular F (r + 1)) h2
    (minusReflectionCharacter F r h2) (fun c _ => complement_represents r hr c)

/-- Determinant and the intrinsic spinor norm recognize the full complementary
commutator, including Witt index one. -/
theorem complement_mem_omega_iff_det_spinor
    (r : ℕ) (hr : 1 ≤ r) (h2 : (2 : F) ≠ 0)
    (u : Minus.Orthogonal F (Minus.Space F r) (Minus.quadraticForm F (r + 1))) :
    u ∈ Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) ↔
      LinearEquiv.det u.val = 1 ∧ (minusReflectionCharacter F r h2).hom u = 1 :=
  complement_mem_omega_iff_det_character r hr h2 (minusReflectionCharacter F r h2) u

/-- The intrinsic spinor norm is unchanged by the literal identity block extension. -/
theorem fullBlockHom_complement_spinor (r : ℕ) (h2 : (2 : F) ≠ 0)
    (u : Minus.Orthogonal F (Minus.Space F r) (Minus.quadraticForm F (r + 1))) :
    (minusReflectionCharacter F (r + 2) h2).hom (fullBlockHom r (1, u)) =
      (minusReflectionCharacter F r h2).hom u :=
  CoordinateValues.fullBlockHom_character r h2
    (minusReflectionCharacter F r h2) (minusReflectionCharacter F (r + 2) h2) u

/-- The spinor norm of literal negation is the product of the quadratic values
of the explicit orthogonal coordinate reflections. -/
theorem negativeComplement_spinor (r : ℕ) (h2 : (2 : F) ≠ 0) :
    (minusReflectionCharacter F r h2).hom (negativeComplement r) =
      Atlas.squareClass F
        (Units.mk0 ((-1 : F) ^ (r + 1) * (1 + 4 * Minus.parameter F))
          (CoordinateValues.minus_discriminant_ne_zero r h2)) :=
  CoordinateValues.negativeComplement_character r h2 (minusReflectionCharacter F r h2)

/-- Ambient commutator membership restricts to the actual complementary block.
This discharges `hrestrict` in the minus centralizer's residual assembly. -/
theorem complement_mem_omega_of_fullBlock_mem
    (r : ℕ) (hr : 1 ≤ r) (h2 : (2 : F) ≠ 0)
    (u : Minus.Orthogonal F (Minus.Space F r) (Minus.quadraticForm F (r + 1)))
    (hu : fullBlockHom r (1, u) ∈
      Minus.Omega F (Minus.Space F (r + 2)) (Minus.quadraticForm F (r + 3))) :
    u ∈ Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) :=
  complement_mem_omega_of_fullBlock_mem_of_characters r hr h2
    (minusReflectionCharacter F r h2) (minusReflectionCharacter F (r + 2) h2)
    (fullBlockHom_complement_spinor r h2) u hu

/-- Identity extension both preserves and reflects literal Omega membership. -/
theorem fullBlock_mem_omega_iff_complement_mem
    (r : ℕ) (hr : 1 ≤ r) (h2 : (2 : F) ≠ 0)
    (u : Minus.Orthogonal F (Minus.Space F r) (Minus.quadraticForm F (r + 1))) :
    fullBlockHom r (1, u) ∈
      Minus.Omega F (Minus.Space F (r + 2)) (Minus.quadraticForm F (r + 3)) ↔
      u ∈ Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) :=
  ⟨complement_mem_omega_of_fullBlock_mem r hr h2 u,
    fullBlock_mem_omega_of_complement_mem r u⟩

/-- The unconditional square criterion for complementary negative-scalar membership.
The scalar and projective-kernel assembly can now use this without a spinor premise. -/
theorem negativeComplement_mem_omega_iff_isSquare
    (r : ℕ) (hr : 1 ≤ r) (h2 : (2 : F) ≠ 0) :
    negativeComplement (F := F) r ∈
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) ↔
      IsSquare ((-1 : F) ^ (r + 1) * (1 + 4 * Minus.parameter F)) :=
  negativeComplement_mem_omega_iff_of_character_value r hr h2
    (minusReflectionCharacter F r h2) (CoordinateValues.minus_discriminant_ne_zero r h2)
    (negativeComplement_spinor r h2)

end ClassicalOrthogonal.Fundamental.MinusCentralizer
