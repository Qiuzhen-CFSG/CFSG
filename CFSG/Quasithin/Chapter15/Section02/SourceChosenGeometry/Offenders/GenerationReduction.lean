module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Definitions
public import Theory.GroupTheory.QuadraticCommutatorNormality

/-!
# Relative normality from the source offender generators

Quadraticity makes A centralize [V,A intersect O2(H)]. The source X
centralizes V and hence this commutator. Together with T-normality and
H= <X,A,T>, this proves H-normality. The same generators centralize a
seed L whose H-orbit span is the literal O^2(H), so that residual centralizes
the plane too. This is the relative ambient version of the quadratic
commutator normality argument, retaining the original embeddings in G.

Source: Aschbacher--Smith 15.2.11, printed p.1111. Constructing X and L
from the distinguished wreath factors is a separate source obligation.
-/

public section

open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor

namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
variable {G : Type*} [Group G]

/-- The generation argument of 15.2.11, with its actual orbit-span residual. -/
theorem plane_normality_of_generation {H T V A X L : Subgroup G}
    (hBV : A ⊓ twoCoreIn H ≤ normalizer (V : Set G))
    (hquad : ⁅⁅conjugateSpan H V,A⁆,A⁆ = ⊥)
    (hXV : X ≤ centralizer (V : Set G))
    (hTZ : T ≤ normalizer (⁅V,A ⊓ twoCoreIn H⁆ : Subgroup G))
    (hgen : H = (X ⊔ A) ⊔ T)
    (hLX : L ≤ X ⊔ A) (hspan : ChosenGeometry.residual H = conjugateSpanBy L H) :
    H ≤ normalizer (⁅V,A ⊓ twoCoreIn H⁆ : Subgroup G) ∧
      ChosenGeometry.residual H ≤ centralizer (⁅V,A ⊓ twoCoreIn H⁆ : Subgroup G) := by
  have hZV : ⁅V,A ⊓ twoCoreIn H⁆ ≤ V :=
    le_normalizer_iff_commutator_le_left.mp hBV
  have hVU : V ≤ conjugateSpan H V := by
    rw [conjugateSpan_eq]
    exact le_conjugateSpanBy _ _
  have hZA : ⁅⁅V,A ⊓ twoCoreIn H⁆,A⁆ = ⊥ := bot_unique
    ((commutator_mono (commutator_mono hVU inf_le_left) le_rfl).trans hquad.le)
  have hAZ : A ≤ centralizer (⁅V,A ⊓ twoCoreIn H⁆ : Subgroup G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hZA)
  have hXZ : X ⊔ A ≤ centralizer (⁅V,A ⊓ twoCoreIn H⁆ : Subgroup G) :=
    sup_le (hXV.trans (centralizer_le hZV)) hAZ
  have hHZ : H ≤ normalizer (⁅V,A ⊓ twoCoreIn H⁆ : Subgroup G) := by
    exact hgen.le.trans (sup_le (hXZ.trans (Subgroup.centralizer_le_normalizer _)) hTZ)
  refine ⟨hHZ,?_⟩
  rw [hspan]
  exact conjugateSpanBy_le (hLX.trans hXZ)
    (hHZ.trans (normalizer_le_normalizer_centralizer _))

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
