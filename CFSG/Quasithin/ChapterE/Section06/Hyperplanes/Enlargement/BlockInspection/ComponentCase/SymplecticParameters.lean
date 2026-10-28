module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase.Reduction
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary

/-!
# The two possible symplectic parameters in E.6.23

Corank two and the complete E.6.8(2) local structure restrict the parameter
to n = 1 or n = 2. At n = 1 the existing polar isomorphism identifies the
literal derived subgroup Sp₄(2)' with A₆. At n = 2 only the maximal-parabolic
branch survives, retaining the actual root action. Its block exclusion is
still required by the final assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8(2)
and E.6.23, printed pp.247,254 (PDF pp.258,265).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase
open Components
variable {G : Type*} [Group G] {M V A X : Subgroup G}

/-- The binary endpoint is the actual derived symplectic group, identified
with A₆ through the established polar representation. -/
theorem binary_symplectic_model (b : SymplecticDerivedModel X 1) : Chapter1.Section02.LocalModels.IsAlternating X 6 := by
  obtain ⟨_, F, _, _, hF, ⟨e⟩⟩ := b
  exact ⟨e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simpa using hF))⟩

/-- Corank two permits only the binary endpoint or the parameter-four
maximal-parabolic root action. -/
theorem symplectic_parameters {n : ℕ} (hr : actionCorank V X = 2) (b : SymplecticAlternative M V A X n) :
    n = 1 ∨ (n = 2 ∧ MaximalParabolic X (X ⊓ M) ∧ SymplecticRootAction X V 2) := by
  have hn := b.model.1
  rcases b.local_structure with ⟨_, ⟨hd, _⟩ | ⟨_, hd⟩⟩ | ⟨hp, ha, hd⟩
  · left
    omega
  · omega
  · right
    have hn2 : n = 2 := hd.symm.trans hr
    exact ⟨hn2, hp, hn2 ▸ ha⟩

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase
