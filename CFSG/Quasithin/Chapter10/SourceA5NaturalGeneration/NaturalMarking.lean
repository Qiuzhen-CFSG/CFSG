module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking
public import Theory.Representation.BinaryConjugationSection.SL2CubicFixed
/-!
# Cubic fixed points for the chosen original natural A₅ marking

Apply the natural-section fixed-point theorem through the literal original
map L → L/O₂(L) → A₅ → SL₂(4). The fixed subgroup in [V,L] is exactly
C_[V,L](L), preserving any central cover. This is the component-coordinate
calculation consumed by the paired Sylow-center argument of10.2.3(4).

Source: Aschbacher–Smith10.2.3(4), printed p.746.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
local instance naturalGenerationMarkingFieldFourAlgebra : Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2

/-- A cubic in the original A₅ quotient fixes precisely the original moved center. -/
theorem source_original_natural_cubic_fixed_eq
    (f : alternatingGroup (Fin 5) ≃*
      SL(2,Representation.OrthogonalFourMinus.FiniteModel.Field 1))
    (c : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
      (sourceMovedFixed D)
      (Representation.SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    (b : L) (hb : orderOf (e (QuotientGroup.mk' (pCore 2 L) b)) = 3) :
    ⁅D.fullModule,L⁆ ⊓ centralizer ({(b : G)} : Set G) = sourceMovedFixed D := by
  apply c.natural_cubic_fixed_eq_kernel _ inf_le_right b
  change orderOf (f (e (QuotientGroup.mk' (pCore 2 L) b))) = 3
  rwa [MulEquiv.orderOf_eq]
end CFSG.Quasithin.Chapter10
