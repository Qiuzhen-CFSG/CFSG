module
public import Theory.Representation.BinaryAlternatingSixModels.CatalogueSource
public import CFSG.Quasithin.ChapterG.Section05.Irreducibles

/-!
# Native catalogue and Steinberg recognition for G.5

The actual alternating tensor is irreducible, and the flag-module argument
exhausts both the alternating and symmetric binary simple modules. These
results discharge the model premise of G.5.2 on the original two parabolics.
The conclusion is equivariantly the top reduced homology of the literal
binary symplectic building, via its duad–syntheme incidence model.

The F₄ scalar-extension decomposition in G.5.1(3) is a separate statement;
this module proves the binary catalogues, their degrees, and G.5.2.
Source: Aschbacher–Smith G.5.1–2, printed pp.342–343.
-/
public section
open Representation Theory.SpecificGroups.SymmetricSix BinaryAlternatingSix
namespace CFSG.Quasithin.ChapterG.Section05

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem alternating_classification_source (ρ : Representation (ZMod 2) G V)
    [IsIrreducible ρ] : IsAlternatingModel ρ := alternating_classify ρ

theorem symmetric_classification_source (ρ : Representation (ZMod 2) G0 V)
    [IsIrreducible ρ] : IsSymmetricModel ρ := symmetric_classify ρ

theorem alternating_degrees_source (ρ : Representation (ZMod 2) G V)
    [IsIrreducible ρ] :
    Module.finrank (ZMod 2) V = 1 ∨ Module.finrank (ZMod 2) V = 4 ∨ Module.finrank (ZMod 2) V = 16 :=
  alternating_degrees ρ

theorem tensor_steinberg_source :
    IsIrreducible alternatingTensor ∧ Nonempty (tensorAction.Equiv SymmetricCatalogue.topHomologyRepresentation) :=
  ⟨alternatingTensor_irreducible, ⟨SymmetricCatalogue.tensorHomologyEquiv alternatingTensor_irreducible⟩⟩

theorem tensor_recognition_source (ρ : Representation (ZMod 2) G0 V) [IsIrreducible ρ]
    (h₁ : HasInvariantLine (ρ.comp G.subtype) G1)
    (h₂ : HasInvariantLine (ρ.comp G.subtype) G2) : Nonempty (ρ.Equiv tensorAction) :=
  SymmetricCatalogue.tensor_recognition alternatingTensor_irreducible ρ h₁ h₂

theorem steinberg_recognition_source (ρ : Representation (ZMod 2) G0 V) [IsIrreducible ρ]
    (h₁ : HasInvariantLine (ρ.comp G.subtype) G1)
    (h₂ : HasInvariantLine (ρ.comp G.subtype) G2) :
    Nonempty (ρ.Equiv SymmetricCatalogue.topHomologyRepresentation) :=
  SymmetricCatalogue.homology_recognition alternatingTensor_irreducible ρ h₁ h₂
end CFSG.Quasithin.ChapterG.Section05
