module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Assembly
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Involution
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.CoreFusion.Transport

/-!
# Unconditional construction of the Mathieu source-local data

The measured 21/45 fusion orientation supplies every ambient normalizer
classification. The explicit point-core orbit excludes the second involution
class from z's class, so the residual-fixed four-subgroup and cubic XI
normalizer construction apply without additional inputs. Assemble these
proved conclusions with the literal marked intersection clauses, and orient
the original marking to obtain `SourceData` directly from `MathieuFusion`.

The hypotheses imply the conclusions without requiring ambient simplicity;
in particular this supplies the full local input in the finite simple setup.
It does not assert the later ambient M₂₄ recognition theorem.

Source: Aschbacher, *Sporadic Groups* (1994), 39.4, 40.3–40.5 and the marked
local data used in 41.1–41.2, printed pp.214–221.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

/-- The full source 40.4(2) assertion for the actual second involution class.
The original two-core, residual, quotient, cubic lift and product XI are
retained. No centralizer or fusion-exclusion premise remains. -/
theorem involutionCentralizerData_exists (hcounts : MathieuFusionOrientation F)
    (t : G) (ht : t ∈ F.plane ⊓ F.threeSpace) (hclass : SecondInvolutionClass F t) :
    Nonempty (InvolutionCentralizerData F t) :=
  involutionCentralizerData_of_not_fused F hcounts t ht.2
    (secondInvolutionClass_ne_one F t hclass) (secondInvolutionClass_not_fused F hcounts t hclass)

/-- All literal local conclusions of 40.3–40.5 and the marked normalizer
intersections follow from the oriented Mathieu fusion counts. -/
def LocalData.ofFusion (hcounts : MathieuFusionOrientation F) : LocalData F :=
  LocalData.ofInvolutionData F hcounts (involutionCentralizerData_exists F hcounts)

/-- Orient the original marking and construct the complete corrected
source-normalizer data, with no extra classification or involution premises. -/
def SourceData.ofFusion (hfusion : F.MathieuFusion) : SourceData F where
  oriented := orient F hfusion
  localData := LocalData.ofFusion _ (orient F hfusion).counts

/-- Existence form of the complete source-local construction. This applies
in particular to the finite simple, nonweakly-closed setup of §§39–41;
the measured Mathieu fusion hypothesis already suffices for these conclusions. -/
theorem sourceData_exists (hfusion : F.MathieuFusion) : Nonempty (SourceData F) :=
  ⟨SourceData.ofFusion F hfusion⟩

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
