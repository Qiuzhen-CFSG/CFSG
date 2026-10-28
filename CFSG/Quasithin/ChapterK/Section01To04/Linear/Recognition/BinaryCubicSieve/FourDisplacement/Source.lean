module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve

/-!
# Source applications of SL₄ multiple-support displacement

Apply the adjacent estimate to the literal marked component action and its
diagram twist, and the endpoint estimate to the marked action. Their combined
displacement bound feeds the existing degree and module-recognition consumers.
This preserves the supplied L ≃ SL₄(2), faithfulness, irreducibility and the
orthogonal intertwiner on the original L.

The unconditional source applications discharge the displacement premise
using `multiple_support_displacement`; finite dimension, faithfulness and
irreducibility all come from `SourceHypothesis`. The conditional APIs remain
available. Keeping this module separate lets the binary sieve import the core
without an import cycle.

Source: Aschbacher–Smith, K.3.2, printed pp.451,454–455; GM04 Table 7.
-/

public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement

open Representation Representation.BinaryOffender Representation.BinaryLinearRecognition
open ChapterG.Section09
open ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- Apply the two root-family estimates to the actual source component
marking. Faithfulness and irreducibility of the diagram twist are derived. -/
theorem source_displacement_of_root_estimates {K : GroupClass}
    (h : SourceHypothesis K ρ L) (e : L ≃* FourSmallModules.Group)
    (hadj : ∀ σ : Representation (ZMod 2) FourSmallModules.Group V,
      Function.Injective σ → IsIrreducible σ → InitialAdjacentDisplacement σ)
    (hend : ∀ σ : Representation (ZMod 2) FourSmallModules.Group V,
      Function.Injective σ → IsIrreducible σ → EndpointDisplacement σ) :
    FourMultipleSupportDisplacement (modelAction ρ e) := by
  let σ := modelAction ρ e
  have hf := modelAction_injective ρ h.faithful e
  have hi := modelAction_irreducible ρ h.irreducible e
  exact multiple_support_displacement_of_root_estimates σ (hadj σ hf hi)
    (hadj (diagramTwist σ) (diagramTwist_injective hf) (diagramTwist_irreducible hi))
    (hend σ hf hi)

/-- The existing degree-window consumer, with its displacement premise
reduced to the two independent root-family estimates. -/
theorem four_finrank_le_ten_of_root_estimates {K : GroupClass}
    (h : SourceHypothesis K ρ L) (e : L ≃* FourSmallModules.Group)
    (hadj : ∀ σ : Representation (ZMod 2) FourSmallModules.Group V,
      Function.Injective σ → IsIrreducible σ → InitialAdjacentDisplacement σ)
    (hend : ∀ σ : Representation (ZMod 2) FourSmallModules.Group V,
      Function.Injective σ → IsIrreducible σ → EndpointDisplacement σ) :
    Module.finrank (ZMod 2) V ≤ 10 :=
  four_finrank_le_ten_of_displacement h e
    (source_displacement_of_root_estimates h e hadj hend)

/-- The existing module-recognition consumer, retaining the literal
representation on L and its actual orthogonal intertwiner. -/
theorem four_small_modules_of_root_estimates {K : GroupClass}
    (h : SourceHypothesis K ρ L) (e : L ≃* FourSmallModules.Group)
    (hadj : ∀ σ : Representation (ZMod 2) FourSmallModules.Group V,
      Function.Injective σ → IsIrreducible σ → InitialAdjacentDisplacement σ)
    (hend : ∀ σ : Representation (ZMod 2) FourSmallModules.Group V,
      Function.Injective σ → IsIrreducible σ → EndpointDisplacement σ) :
    Module.finrank (ZMod 2) V = 4 ∨
      Quasiequivalent (ρ.comp L.subtype) orthogonalEightAction :=
  four_small_modules_of_displacement h e
    (source_displacement_of_root_estimates h e hadj hend)

/-- The proved multiple-support estimate on the actual marked source component.
All representation hypotheses are supplied by the original Chapter K input. -/
theorem source_displacement {K : GroupClass}
    (h : SourceHypothesis K ρ L) (e : L ≃* FourSmallModules.Group) :
    FourMultipleSupportDisplacement (modelAction ρ e) := by
  let : FiniteDimensional (ZMod 2) V := h.finite_module
  exact multiple_support_displacement (modelAction ρ e)
    (modelAction_injective ρ h.faithful e)
    (modelAction_irreducible ρ h.irreducible e)

/-- The binary SL₄ degree window from the ambient source cubic-ratio bound,
with the multiple-support displacement premise discharged. -/
theorem four_finrank_le_ten {K : GroupClass}
    (h : SourceHypothesis K ρ L) (e : L ≃* FourSmallModules.Group) :
    Module.finrank (ZMod 2) V ≤ 10 :=
  four_finrank_le_ten_of_displacement h e (source_displacement h e)

/-- The binary SL₄ source module alternatives, retaining the actual action on L
and its orthogonal intertwiner, with no extra displacement premise. -/
theorem four_small_modules {K : GroupClass}
    (h : SourceHypothesis K ρ L) (e : L ≃* FourSmallModules.Group) :
    Module.finrank (ZMod 2) V = 4 ∨
      Quasiequivalent (ρ.comp L.subtype) orthogonalEightAction :=
  four_small_modules_of_displacement h e (source_displacement h e)

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement
