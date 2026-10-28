module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import Theory.SpecificGroups.Suzuki.ElementaryNormalizer

/-!
# Weak-closure normalizers in the Suzuki model

A family with a nontrivial member in the standard root group has nontrivial
weak closure there. The unique fixed point of each nonidentity root element
then puts the weak-closure normalizer inside the proper Borel.

This is the normalizer step for Aschbacher--Smith E.1.14(1), printed p.214,
using the ovoid geometry of Huppert--Blackburn III, XI.3.3. Construction of
the elementary family and confinement of its E-members are separate steps.
-/

public section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.Suzuki

open Subgroup BenderSuzuki.MatrixGroups

/-- A nontrivial member of the family in the root group makes its weak closure
nontrivial, so its normalizer lies in the Borel. Confinement of E-members is an
additional requirement for the lower obstruction. -/
theorem weakClosure_normalizer_le_borel (m : ℕ) (hm : 0 < m)
    (Ω : Set (Subgroup (SuzukiMatrixGroup m)))
    (hΩ : ∃ A ∈ Ω, A ≤ SuzukiRootSubgroup m ∧ A ≠ ⊥) :
    normalizer (weakClosure (SuzukiRootSubgroup m) Ω : Set (SuzukiMatrixGroup m)) ≤
      SuzukiBorelSubgroup m := by
  apply suzuki_normalizer_le_borel_of_le_root m hm _ _ (weakClosure_le _ _)
  obtain ⟨A, hA, hAF, hne⟩ := hΩ
  intro h
  apply hne
  apply bot_unique
  calc
    A ≤ weakClosure (SuzukiRootSubgroup m) Ω := le_sSup ⟨hA, hAF⟩
    _ = ⊥ := h


end CFSG.Quasithin.ChapterE.ExceptionalValues.Suzuki
