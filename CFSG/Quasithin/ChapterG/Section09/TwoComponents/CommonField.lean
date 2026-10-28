module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField.Interfaces
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField.Comparison
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField.Evaluation

/-!
# Assembly of the common-field construction in G.9.3

Distinct components commute. The constituent construction therefore supplies
actual faithful irreducible subrepresentations for both restrictions, proves
that each restriction is homogeneous, and constructs its full finite Schur
field. Constituent comparison under the given quasiequivalence or duality
identifies the binary dimensions and Schur-field orders. The common-field
construction aligns the scalar actions and proves tensor evaluation bijective.
The final adapter recovers the unchanged `TensorConstructionTheorem`, including
equal factor dimensions and equivariance for both original component actions.

`tensorConstruction` discharges both premises of the retained conditional
adapter. Neither quadratic actors nor any component classification is used.

Source: Aschbacher--Smith, combined manuscript, G.9.3, printed p.356,
first paragraph.
-/

public noncomputable section

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField

universe u v

/-- The source component hypotheses produce two actual faithful homogeneous
constituents; no tensor identification or classification hypothesis is used. -/
theorem component_constituents
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L L₂ : Subgroup G)
    (hρ : Function.Injective ρ)
    (hL : Theory.GroupTheory.IsComponent G L)
    (hL₂ : Theory.GroupTheory.IsComponent G L₂) (hne : L ≠ L₂)
    (hirr : Representation.IsIrreducible (ρ.comp (L ⊔ L₂).subtype)) :
    Nonempty (ConstituentData ρ L × ConstituentData ρ L₂) := by
  obtain ⟨C⟩ := exists_constituentData ρ L L₂
    (hL.commutator_eq_bot_of_ne hL₂ hne) hirr hρ
  obtain ⟨D⟩ := exists_constituentData ρ L₂ L
    (hL₂.commutator_eq_bot_of_ne hL hne.symm)
    ((sup_comm L L₂) ▸ hirr) hρ
  exact ⟨C, D⟩

/-- Assemble the unchanged source contract from the constituent comparison
and common-field tensor realization theorems. -/
theorem tensorConstruction_of_comparison_and_realization
    (comparison : ConstituentComparisonTheorem.{u,v})
    (realization : TensorRealizationTheorem.{u,v}) : TensorConstructionTheorem.{u,v} := by
  intro G _ _ V _ _ _ ρ L L₂ hρ hL hL₂ hne hirr hq
  obtain ⟨C, D⟩ := component_constituents ρ L L₂ hρ hL hL₂ hne hirr
  have hcomp := comparison ρ L L₂ C D hq
  obtain ⟨T⟩ := realization ρ L L₂ C D
    (hL.commutator_eq_bot_of_ne hL₂ hne) hirr hcomp.schur_card
  exact ⟨T.toTensorData hcomp⟩

/-- Distinct components acting irreducibly together, with restrictions
quasiequivalent up to duality, admit the common-field tensor construction of
G.9.3. This includes faithful irreducible constituents, their actual embeddings,
full scalar endomorphism rings, equal factor dimensions and tensor equivariance. -/
theorem tensorConstruction : TensorConstructionTheorem.{u,v} :=
  tensorConstruction_of_comparison_and_realization constituentComparison tensorRealization

end CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField
