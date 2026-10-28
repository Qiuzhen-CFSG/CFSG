module

public import Mathlib.LinearAlgebra.RootSystem.BaseExists
public import Theory.AlgebraicGroup.RootSubgroups.Finite

/-!
# Root geometry inside the actual torus character lattice

This interface separates the geometric part of GLS3, Theorem 1.9.5(d), from
the subsequent choice of root groups and algebraic cocharacters. The indices
are the actual characters occurring on one-parameter subgroups. The real root
vectors are their images under a faithful additive map of the actual root
lattice; in particular this is not an unrelated root-system model. The roots
span this real space. The full character lattice is retained separately for
the integral coroot assertion, including the central torus directions.

`HasIntegralCoroots` is the additional integral-lattice assertion needed for
the cocharacters in GLS3, Remarks 1.9.6. Crystallographic integrality on roots
alone does not assert integrality on all torus characters. Neither geometric
existence assertion is assumed to follow from reductivity in this module.

Source: Borel, *Linear Algebraic Groups*, §§13.18, 14.6--14.8; GLS3 §1.9.
The consumer `RootSubgroups.ReductiveRealization` constructs complete actual
root-group data from these two inputs.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]
variable {G : Variety k} [AlgebraicGroup G]

/-- Roots indexed by their actual ambient torus characters. -/
public abbrev TorusRootIndex (T : ClosedSubgroup G) :=
  {χ : TorusWeight T // IsTorusRoot T χ}

public instance torusRootIndex_finite [IsAlgClosed k] (T : ClosedSubgroup G) :
    Finite (TorusRootIndex T) :=
  (torusRootSet_finite T).to_subtype

/-- An actual root, regarded as an element of the actual root lattice. -/
@[expose]
public def TorusRootIndex.latticeElement {T : ClosedSubgroup G}
    (α : TorusRootIndex T) : TorusRootLattice T :=
  ⟨α.val, Subgroup.subset_closure α.property⟩

/-- A reduced crystallographic root pairing on the actual characters.
Its real space is the span of the actual root lattice. -/
public structure TorusCharacterRootGeometry (T : ClosedSubgroup G) where
  dimension : ℕ
  characterMap : Additive (TorusRootLattice T) →+ (Fin dimension → ℝ)
  characterMap_injective : Function.Injective characterMap
  pairing : RootPairing (TorusRootIndex T) ℝ
    (Fin dimension → ℝ) (Fin dimension → ℝ)
  root_eq : ∀ α, pairing.root α = characterMap (Additive.ofMul α.latticeElement)
  isRootSystem : pairing.IsRootSystem
  isCrystallographic : pairing.IsCrystallographic
  isReduced : pairing.IsReduced

namespace TorusCharacterRootGeometry

variable {T : ClosedSubgroup G} (R : TorusCharacterRootGeometry T)

attribute [instance] isRootSystem isCrystallographic isReduced

/-- The coroot functional extends integrally from roots to all characters.
This is a separate geometric assertion, not part of a bare root system. -/
@[expose]
public def HasIntegralCoroots : Prop :=
  ∀ β : TorusRootIndex T, ∃ φ : Additive (TorusWeight T) →+ ℤ,
    ∀ α : TorusRootIndex T,
      (φ (Additive.ofMul α.val) : ℝ) = R.pairing.pairing α β

/-- Addition of the real root vectors is exactly multiplication of the
original characters. -/
public theorem root_add_iff (α β γ : TorusRootIndex T) :
    R.pairing.root γ = R.pairing.root α + R.pairing.root β ↔
      γ.val = α.val * β.val := by
  rw [R.root_eq, R.root_eq, R.root_eq, ← map_add]
  rw [R.characterMap_injective.eq_iff]
  change γ.latticeElement = α.latticeElement * β.latticeElement ↔ _
  exact Subtype.ext_iff

/-- The root-system negative is the inverse of the actual character. -/
public theorem root_neg (α : TorusRootIndex T) :
    (R.pairing.reflectionPerm α α).val = α.val⁻¹ := by
  suffices h : (R.pairing.reflectionPerm α α).latticeElement =
      α.latticeElement⁻¹ from congrArg Subtype.val h
  apply R.characterMap_injective
  change R.characterMap (Additive.ofMul
      (R.pairing.reflectionPerm α α).latticeElement) =
    R.characterMap (-Additive.ofMul α.latticeElement)
  rw [map_neg, ← R.root_eq, ← R.root_eq]
  simp

/-- Real root reflections transport to the original character lattice with
any integral exponent equal to the Cartan pairing. -/
public theorem root_reflect (α β : TorusRootIndex T) (m : ℤ)
    (hm : (m : ℝ) = R.pairing.pairing β α) :
    (R.pairing.reflectionPerm α β).val = β.val * α.val ^ (-m) := by
  suffices h : (R.pairing.reflectionPerm α β).latticeElement =
      β.latticeElement * α.latticeElement ^ (-m) from congrArg Subtype.val h
  apply R.characterMap_injective
  change R.characterMap (Additive.ofMul
      (R.pairing.reflectionPerm α β).latticeElement) =
    R.characterMap (Additive.ofMul β.latticeElement +
      (-m) • Additive.ofMul α.latticeElement)
  rw [map_add, map_zsmul, ← R.root_eq, ← R.root_eq, ← R.root_eq,
    R.pairing.root_reflectionPerm, R.pairing.reflection_apply_root]
  rw [← Int.cast_smul_eq_zsmul ℝ]
  simp only [Int.cast_neg, hm, neg_smul, sub_eq_add_neg]

end TorusCharacterRootGeometry

end Theory.AlgebraicGroup
