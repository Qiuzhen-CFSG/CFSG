module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.CentralizerReduction
public import Theory.GroupTheory.PRadical.NormalizerRestriction

/-!
# Radical normalizers in the extraspecial centralizer branch

Suppose the whole normalizer of a radical two-subgroup P normalizes an
elementary X, and C(X) lies in the actual O₂(C(t)) for a 2A-involution t.
The centralizer enlargement produces a nontrivial pure-2A subgroup Y whose
normalizer contains N(P). Radical saturation puts Y inside P. In the actual
local M = N(Y), the normalizer of P is the full ambient N(P), and P remains
radical with precisely the same normalizer core under the inclusion maps.

This is the literal radical application of the extraspecial residual branch
of Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Proposition 2.2.3,
p.491. The Figure 2/isotropic-space placement of C(X) and the classification
of pure-2A normalizers remain separate source obligations of the cover family.
The conclusion here names N(Y), not one of the four final native locals.
-/

public section
open Subgroup
namespace Janko4.LocalStructure.ElementaryNormalizerCover
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- Radical saturation and restriction for the native extraspecial branch.
All normalizers and cores use the literal subgroup inclusions. -/
theorem radical_pure_local_of_centralizer_in_involution_core
    (P : Subgroup Model) (hP : P.IsPRadical 2)
    (t : Model) (ht : IsConj a t) (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model))
    (hC : centralizer (X : Set Model) ≤ (centralizer ({t} : Set Model)).pCoreIn 2) :
    ∃ Y M : Subgroup Model,
      Y ≠ ⊥ ∧ IsElementaryAbelian 2 Y ∧ Y ≤ P ∧
      (∀ y ∈ Y, y ≠ 1 → IsConj a y) ∧
      M = normalizer (Y : Set Model) ∧ IsTwoLocal M ∧
      normalizer (P : Set Model) ≤ M ∧ P ≤ M ∧
      (normalizer (P.subgroupOf M : Set M)).map M.subtype =
        normalizer (P : Set Model) ∧
      (P.subgroupOf M).IsPRadical 2 ∧
      (normalizer (P.subgroupOf M : Set M)).pCoreIn 2 = P.subgroupOf M ∧
      ((normalizer (P.subgroupOf M : Set M)).pCoreIn 2).map M.subtype = P := by
  obtain ⟨Y, hYne, _, _, hYe, hNY, hYp⟩ :=
    centralizer_in_involution_core_pure_reduction t ht X hC
  let := hYe
  let M := normalizer (Y : Set Model)
  have hNM : normalizer (P : Set Model) ≤ M := hNX.trans hNY
  have hPM : P ≤ M := P.le_normalizer.trans hNM
  have hYP : Y ≤ P := le_of_normalizer_le_normalizer_of_pCore_normalizer_le
    P Y hP.isPGroup (IsElementaryAbelian.isPGroup 2 Y) hP.2.le hNM
  have hn : normalizer (P : Set Model) ≤ normalizer (M : Set Model) :=
    hNM.trans M.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf M hPM hn
  refine ⟨Y, M, hYne, hYe, hYP, hYp, rfl,
    ⟨Y, hYne, IsElementaryAbelian.isPGroup 2 Y, rfl⟩, hNM, hPM, ?_,
    hP.subgroupOf_of_normalizer_normalizes M hPM hn, hcore, ?_⟩
  · rw [← subgroupOf_normalizer_eq hPM, map_subgroupOf_eq_of_le hNM]
  · rw [hcore, map_subgroupOf_eq_of_le hPM]

end Janko4.LocalStructure.ElementaryNormalizerCover
