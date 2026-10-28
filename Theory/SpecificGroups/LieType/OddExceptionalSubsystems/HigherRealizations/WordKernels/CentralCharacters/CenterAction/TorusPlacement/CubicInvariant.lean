module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ResidueDiagonal
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.CubicInvariant.Transport
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.CubicInvariant.E7ToE8
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.CubicInvariant.E7Block

/-!
# The cubic detector for residue diagonals in higher E6 word images

The explicit 27-coordinate cubic in `CubicInvariant.Model` is preserved by all
twelve signed transvections and every evaluated word. Its value at the vector
supported at coordinates 0, 9, 26 is one. An actual injective invariant block
therefore forces a scalar word value to have cube one. The residue diagonal
acts on the intended block by `u⁻¹`; taking inverses gives precisely `u³ = 1`.

The applications below connect this polynomial calculation to the literal
E7 and E8 word maps. `E7Block` constructs the injective block and proves its
generator equations and residue character. Instantiating the conditional
detector gives `e7Six_residue_cube` with no representation premises. The actual
E7-to-E8 integral inclusion then gives `e8Six_residue_cube` for the same word.
These discharge the cubic inputs of `e7Six_torus_of_shape_and_cube` and
`e8Six_torus_of_shape_and_cube`; central scalar shape and final torus placement
remain with their separate owners.

Sources: GLS3 §§1.12.5–6 and §2.6.2 (`refs/KGroup/GLS3/Chapter1.tex` and
`refs/KGroup/GLS3/chapter2.tex`), for Aschbacher–Smith A.2.17, printed p.39.
All polynomial and word arguments work over arbitrary fields, including
characteristic three.
-/

@[expose] public section
open scoped Matrix
noncomputable section

open Theory.AlgebraicGroup.StandardRootSystem
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement
attribute [local instance] Classical.decEq
local instance cubicInvariantE7RootsFintype : Fintype typeE7Roots := Fintype.ofFinite _
local instance cubicInvariantE8RootsFintype : Fintype typeE8Roots := Fintype.ofFinite _

variable (F : Type*) [Field F]

/-- The E7 cubic constraint follows from an actual invariant copy of the explicit 27-coordinate
module. The copy and its residue character remain concrete representation obligations. -/
theorem e7Six_residue_cube_of_block
    (J : (Fin 27 → F) →ₗ[F] ((typeE7RootPairing_base.support ⊕ typeE7Roots) → F))
    (hinj : Function.Injective J)
    (hJ : ∀ (s : Bool) (i : Fin 6) (t : F) (x : Fin 27 → F),
      (e7Simple F s (i.castLE (by decide)) t).val.val *ᵥ J x =
        J (CubicModel.curve s i t x))
    (hscalar : ∀ (u : Fˣ) x, (residueDiagonal F e7Node u).val *ᵥ J x =
      J ((u⁻¹ : Fˣ).val • x))
    (w : SixNodeWord F) (u : Fˣ)
    (h : (e7Six F w).val = residueDiagonal F e7Node u) : u ^ 3 = 1 := by
  have hc : ((u⁻¹ : Fˣ).val) ^ 3 = 1 := by
    refine CubicModel.cube_of_intertwining J
      ((ExceptionalSplit.rootGenerated _ _ F).subtype.comp (e7Six F)) hinj
      ?_ w _ ?_
    · intro s i t x
      simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, e7Six_of] using hJ s i t x
    · intro x
      change (e7Six F w).val.val *ᵥ J x = _
      rw [h, hscalar]
  have hu : (u⁻¹) ^ 3 = 1 := Units.ext (by simpa using hc)
  simpa only [inv_pow, inv_eq_one] using hu

/-- The same word-level cubic detector for a literal E8 invariant block. -/
theorem e8Six_residue_cube_of_block
    (J : (Fin 27 → F) →ₗ[F] ((typeE8RootPairing_base.support ⊕ typeE8Roots) → F))
    (hinj : Function.Injective J)
    (hJ : ∀ (s : Bool) (i : Fin 6) (t : F) (x : Fin 27 → F),
      (e8Simple F s (i.castLE (by decide)) t).val.val *ᵥ J x =
        J (CubicModel.curve s i t x))
    (hscalar : ∀ (u : Fˣ) x, (residueDiagonal F e8Node u).val *ᵥ J x =
      J ((u⁻¹ : Fˣ).val • x))
    (w : SixNodeWord F) (u : Fˣ)
    (h : (e8Six F w).val = residueDiagonal F e8Node u) : u ^ 3 = 1 := by
  have hc : ((u⁻¹ : Fˣ).val) ^ 3 = 1 := by
    refine CubicModel.cube_of_intertwining J
      ((ExceptionalSplit.rootGenerated _ _ F).subtype.comp (e8Six F)) hinj
      ?_ w _ ?_
    · intro s i t x
      simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, e8Six_of] using hJ s i t x
    · intro x
      change (e8Six F w).val.val *ᵥ J x = _
      rw [h, hscalar]
  have hu : (u⁻¹) ^ 3 = 1 := Units.ext (by simpa using hc)
  simpa only [inv_pow, inv_eq_one] using hu

/-- The E7 block suffices for the E8 constraint, via the actual integral E7 inclusion in E8. -/
theorem e8Six_residue_cube_of_e7_block
    (J : (Fin 27 → F) →ₗ[F] ((typeE7RootPairing_base.support ⊕ typeE7Roots) → F))
    (hinj : Function.Injective J)
    (hJ : ∀ (s : Bool) (i : Fin 6) (t : F) (x : Fin 27 → F),
      (e7Simple F s (i.castLE (by decide)) t).val.val *ᵥ J x =
        J (CubicModel.curve s i t x))
    (hscalar : ∀ (u : Fˣ) x, (residueDiagonal F e7Node u).val *ᵥ J x =
      J ((u⁻¹ : Fˣ).val • x))
    (w : SixNodeWord F) (u : Fˣ)
    (h : (e8Six F w).val = residueDiagonal F e8Node u) : u ^ 3 = 1 :=
  e7Six_residue_cube_of_block F J hinj hJ hscalar w u
    (E7ToE8.e7Six_eq_residueDiagonal_of_e8Six_eq F w u h)

/-- Membership of a residue diagonal in the literal E7 six-node word image forces its
parameter to be a cube root of unity. No finiteness or characteristic restriction is needed. -/
theorem e7Six_residue_cube (w : SixNodeWord F) (u : Fˣ)
    (h : (e7Six F w).val = residueDiagonal F e7Node u) : u ^ 3 = 1 :=
  e7Six_residue_cube_of_block F (E7Block.J F) (E7Block.J_injective F)
    (E7Block.simple_J F) (E7Block.residueDiagonal_J F) w u h

/-- Membership of a residue diagonal in the literal E8 six-node word image forces its
parameter to be a cube root of unity, by restriction along the actual E7 inclusion. -/
theorem e8Six_residue_cube (w : SixNodeWord F) (u : Fˣ)
    (h : (e8Six F w).val = residueDiagonal F e8Node u) : u ^ 3 = 1 :=
  e7Six_residue_cube F w u
    (E7ToE8.e7Six_eq_residueDiagonal_of_e8Six_eq F w u h)

end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement
