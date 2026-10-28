module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.DualAction.Inputs

/-!
# The code chief factors and natural bottom factor

Annihilation reverses all four covers in the cocode chief flag. The three
resulting intermediate spaces are exactly the canonical V4, V8, V9; their
dimensions follow from the nondegenerate ten-dimensional coordinate pairing.
The natural cocode quotient marking gives the natural code bottom marking
through the self-duality of the binary five-point natural module.

Source: Aschbacher--Smith, the chief-factor and natural-module duality in
H.16.3(1--2), printed p.403 (1 March 2004 manuscript).
-/

@[expose] public section
noncomputable section
namespace MathieuCode.M22Quintet.DualAction

namespace CocodeFlag

/-- The invariant code term with underlying space V8. -/
def codeEight (F : CocodeFlag) : Subrepresentation codeAction :=
  annihilatorSubrepresentation F.two

/-- The invariant code term with underlying space V9. -/
def codeNine (F : CocodeFlag) : Subrepresentation codeAction :=
  annihilatorSubrepresentation F.one

@[simp] theorem codeEight_space (F : CocodeFlag) : F.codeEight.toSubmodule = V8 := by
  change annihilator F.two.toSubmodule = annihilator V2
  rw [F.two_eq]

@[simp] theorem codeNine_space (F : CocodeFlag) : F.codeNine.toSubmodule = V9 := by
  change annihilator F.one.toSubmodule = annihilator V1
  rw [F.one_eq]

/-- The code flag is a chief series for the actual Q-action. -/
theorem code_chief (F : CocodeFlag) :
    (⊥ : Subrepresentation codeAction) ⋖ V4Subrepresentation ∧
    V4Subrepresentation ⋖ F.codeEight ∧ F.codeEight ⋖ F.codeNine ∧
    F.codeNine ⋖ (⊤ : Subrepresentation codeAction) := by
  have htop : annihilatorSubrepresentation (⊤ : Subrepresentation cocodeAction) =
      (⊥ : Subrepresentation codeAction) := annihilatorOrderIso.map_top
  have hbot : annihilatorSubrepresentation (⊥ : Subrepresentation cocodeAction) =
      (⊤ : Subrepresentation codeAction) := annihilatorOrderIso.map_bot
  have hsix : annihilatorSubrepresentation V6Subrepresentation = V4Subrepresentation := rfl
  have h01 : (⊥ : Subrepresentation codeAction) ⋖ V4Subrepresentation :=
    Eq.mp (congrArg₂ (fun A B : Subrepresentation codeAction => A ⋖ B) htop hsix)
      (annihilator_covBy F.chief6top)
  have h48 : V4Subrepresentation ⋖ F.codeEight :=
    Eq.mp (congrArg (fun A : Subrepresentation codeAction => A ⋖ F.codeEight) hsix)
      (annihilator_covBy F.chief26)
  have h89 : F.codeEight ⋖ F.codeNine := annihilator_covBy F.chief12
  have h9top : F.codeNine ⋖ (⊤ : Subrepresentation codeAction) :=
    Eq.mp (congrArg (fun A : Subrepresentation codeAction => F.codeNine ⋖ A) hbot)
      (annihilator_covBy F.chief01)
  exact ⟨h01, h48, h89, h9top⟩


/-- Dimensions of the canonical annihilator terms. -/
theorem code_dimensions (F : CocodeFlag) :
    Module.finrank (ZMod 2) V4 = 4 ∧ Module.finrank (ZMod 2) V8 = 8 ∧
      Module.finrank (ZMod 2) V9 = 9 :=
  code_flag_dimensions F.dim1 F.dim2 F.dim6

/-- Strictness is also exposed on the underlying canonical vector spaces. -/
theorem code_strict (F : CocodeFlag) :
    (⊥ : Submodule (ZMod 2) M22Code) < V4 ∧ V4 < V8 ∧ V8 < V9 ∧ V9 < ⊤ :=
  code_flag_strict F.two_le_six F.dim1 F.dim2 F.dim6

end CocodeFlag

namespace CocodeActionData
variable {F : CocodeFlag} {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- The natural marking is constructed from the cocode quotient marking. -/
def codeNaturalEquiv (D : CocodeActionData F E) :
    V4 ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5) := naturalEquiv D.naturalQuotient

theorem codeNaturalEquiv_equivariant (D : CocodeActionData F E) (g : Q) (v : V4) :
    D.codeNaturalEquiv (V4Subrepresentation.toRepresentation g v) =
      BinaryPermutation.naturalRepresentation (Fin 5) (D.quotientMap g)
        (D.codeNaturalEquiv v) :=
  naturalEquiv_equivariant D.quotientMap D.naturalQuotient
    D.naturalQuotient_equivariant g v

end CocodeActionData
end MathieuCode.M22Quintet.DualAction
