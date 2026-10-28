module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SLTwo
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.FixedFiltration

/-!
# Borel fixation through the SL₂ exceptional extension

The first natural layer is a literal invariant submodule modulo a centralized
submodule. The second is a quotient of the remaining quotient module by its
centralized submodule. Neither extension is assumed split. Vanishing of the
natural module's Borel fixed space handles each layer, and the odd-index trace
lifts fixed vectors across the intervening extension.

This is the fixed-space calculation for the exceptional extension in
Aschbacher--Smith, 15.3.65, printed p.1152 (combined manuscript, 1 March 2004).
F.9.18(6) and B.5.1 must still identify these layers in the source module.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction
open Representation Representation.BinaryOffender Matrix

variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]

/-- The two natural layers in the SL₂ exception. The invariant kernel I
and the quotient V/I may each be nonsplit extensions over central submodules.
All quotient actions and both equivariant identifications are retained. -/
theorem slTwo_two_layer_fixed
    (ρ : Representation (ZMod 2) D V) (B : Subgroup D) (hindex : Odd B.index)
    (I : Subrepresentation ρ)
    (C₀ : Subrepresentation I.toRepresentation)
    (hC₀ : C₀.toSubmodule ≤ fixedSpace I.toRepresentation ⊤)
    (C₁ : Subrepresentation I.quotientRepresentation)
    (hC₁ : C₁.toSubmodule ≤ fixedSpace I.quotientRepresentation ⊤)
    (φ : D →* SpecialLinearGroup (Fin 2) F)
    (hB : B.map φ = SpecialLinearGroup.rankOneBorel F)
    (e₀ : (I ⧸ C₀.toSubmodule) ≃ₗ[ZMod 2] (Fin 2 → F))
    (he₀ : ∀ g v, e₀ (C₀.quotientRepresentation g v) = specialLinearNatural 2 (φ g) (e₀ v))
    (e₁ : ((V ⧸ I.toSubmodule) ⧸ C₁.toSubmodule) ≃ₗ[ZMod 2] (Fin 2 → F))
    (he₁ : ∀ g v, e₁ (C₁.quotientRepresentation g v) = specialLinearNatural 2 (φ g) (e₁ v))
    (hF : 2 < Nat.card F) :
    fixedSpace ρ B ≤ fixedSpace ρ ⊤ := by
  have hI : fixedSpace I.toRepresentation B ≤ fixedSpace I.toRepresentation ⊤ :=
    fixedSpace_le_of_central_extension _ C₀ hC₀ B
      (slTwo_section_fixedSpace_eq_bot _ φ e₀ he₀ B hB hF)
  have hQ : fixedSpace I.quotientRepresentation B ≤
      fixedSpace I.quotientRepresentation ⊤ :=
    fixedSpace_le_of_central_extension _ C₁ hC₁ B
      (slTwo_section_fixedSpace_eq_bot _ φ e₁ he₁ B hB hF)
  apply fixedSpace_le_of_extension ρ I B hindex _ hQ
  rintro v ⟨hvI, hvB⟩ g
  have hfix : (⟨v, hvI⟩ : I) ∈ fixedSpace I.toRepresentation B := by
    intro b
    exact Subtype.ext (hvB b)
  exact congrArg (fun w : I => (w : V)) (hI hfix g)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction
