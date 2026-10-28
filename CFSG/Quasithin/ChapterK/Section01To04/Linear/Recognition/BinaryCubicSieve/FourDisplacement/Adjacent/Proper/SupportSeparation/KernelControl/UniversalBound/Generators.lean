module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.SupportSeparation.KernelControl.Quotient
import Mathlib.Tactic.FinCases

/-!
# The universal cyclic generator and its literal root relations

The image of the regular basis vector at `g` is the `g`-translate of the
universal seed. Each seed relation vanishes in the given quotient, hence this
seed satisfies exactly the proper adjacent highest-vector relations. These
identities supply the original relations for the geometric flag construction;
no tensor comparison or dimension hypothesis is used.

Source application: Aschbacher–Smith, K.3.2, printed pp.451,454–455;
Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Proposition 4.8(3), pp.27–28. This is a finite binary highest-vector calculation,
not an invocation of an absolute highest-weight classification.
-/

@[expose] public section

open Representation
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.SupportSeparation.KernelControl

/-- The image of a literal regular basis vector in the given quotient. -/
noncomputable def universalGenerator (g : Group) : Universal :=
  relations.mkQ (MonoidAlgebra.single g 1)

/-- The induced action is left multiplication on regular basis images. -/
theorem universalGenerator_action (g h : Group) :
    universalRepresentation g (universalGenerator h) = universalGenerator (g * h) := by
  change relations.mkQ (regular g (MonoidAlgebra.single h 1)) = _
  simp only [regular, Representation.ofMulAction_single, smul_eq_mul, universalGenerator]

private theorem seedRelation_zero {r : Free} (hr : r ∈ seedRelations) : relations.mkQ r = 0 := by
  apply (Submodule.Quotient.mk_eq_zero relations).mpr
  apply Submodule.subset_span
  exact ⟨1, r, hr, by simp⟩

/-- The universal seed satisfies the specified proper adjacent root relations. -/
theorem universalGenerator_highest :
    LocalHighestVector universalRepresentation {0, 1} (universalGenerator 1) := by
  constructor
  · intro i j hij
    rw [universalGenerator_action, mul_one]
    apply sub_eq_zero.mp
    change relations.mkQ (MonoidAlgebra.single _ 1) - relations.mkQ (MonoidAlgebra.single 1 1) = 0
    rw [← map_sub]
    exact seedRelation_zero (Or.inl ⟨i, j, hij, rfl⟩)
  · intro i hi
    have hi2 : i = 2 := by fin_cases i <;> simp_all
    subst i
    rw [universalGenerator_action, mul_one]
    apply sub_eq_zero.mp
    change relations.mkQ (MonoidAlgebra.single _ 1) - relations.mkQ (MonoidAlgebra.single 1 1) = 0
    rw [← map_sub]
    exact seedRelation_zero (Or.inr (Or.inl rfl))
  · intro i hi
    rw [universalGenerator_action, universalGenerator_action, mul_one, mul_one]
    change relations.mkQ (MonoidAlgebra.single 1 1) + relations.mkQ (MonoidAlgebra.single _ 1) +
      relations.mkQ (MonoidAlgebra.single _ 1) = 0
    rw [← map_add, ← map_add]
    exact seedRelation_zero (Or.inr (Or.inr ⟨i, hi, rfl⟩))
end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.SupportSeparation.KernelControl
