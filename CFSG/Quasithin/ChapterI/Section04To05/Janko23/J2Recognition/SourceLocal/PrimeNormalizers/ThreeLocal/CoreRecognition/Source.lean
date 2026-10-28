module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SevenRatio
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreRecognition.SylowInputs
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.SecondNormalizer.CentralizerAlternative
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Actors.Recognition

/-!+# The perfect A₆ centralizer cover from the earlier source conclusions

For L = C_G(X) and K = E(C_G(t)), the selected geometry gives the second
cubic-centralizer alternatives. These supply the independent Sylow calculation:
the two-part of |L| is eight, and L contains a nonabelian ambient Sylow three.
The constructed inverting involution gives [N_G(X):L] = 2. The preliminary
`seven_normalizer_ratio`, through the Frattini calculation, then removes the
possible seven factor and gives |L| = 1080 and [L:KX] = 6.

The nonnormal embedded A₅ has a faithful six-coset action on L/X. This identifies
the literal quotient with A₆; the nonabelian Sylow three forces L to be perfect,
with center exactly X. All premises of the conditional core recognition are
discharged here. The final application combines this cover with the independently
constructed actors to produce the existing `CentralizerCalculation` contract.

Only the exact 47.1–47.2 conclusions in `EarlierConclusions` remain as source
inputs. Their production belongs to the earlier source theorems. No assertion
from printed 47.4 or later Sylow-fusion calculation is used.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.3, printed p.262.
-/

@[expose] public section

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
namespace EarlierConclusions

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {D : Seed G}
variable (E : EarlierConclusions D)
include E

/-- The independent Sylow inputs, with the second-centralizer alternatives proved. -/
theorem source_core_sylow_data : CoreSylowData D :=
  E.core_sylow_data (SecondNormalizer.centralizerAlternatives E.geometry)

/-- Frattini's argument and the preliminary seven ratio determine the exact order. -/
theorem centralizer_card : Nat.card (C D) = 1080 :=
  E.centralizer_card_of_core_sylow E.source_core_sylow_data E.centralizer_index

/-- The extra seven factor is excluded in the literal centralizer. -/
theorem not_seven_dvd_centralizer : ¬ 7 ∣ Nat.card (C D) := by
  rw [E.centralizer_card]
  decide

/-- The perfect A₆ cover and the literal relative index, with no local premise left. -/
theorem core_recognition :
    Theory.GroupTheory.IsQuasisimple (C D) ∧
    Nonempty ((C D ⧸ XC D) ≃* alternatingGroup (Fin 6)) ∧
    (InvolutionGeometry.rootComponent E.geometry.t ⊔ D.X).relIndex (C D) = 6 :=
  E.core_recognition_of_sylow_data E.source_core_sylow_data E.centralizer_index

/-- Perfectness of the actual first cubic centralizer. -/
theorem centralizer_perfect : Group.IsPerfect (C D) :=
  E.core_recognition.1.toIsPerfect

/-- Its center is the original seed subgroup inside the centralizer. -/
theorem centralizer_center : Subgroup.center (C D) = XC D :=
  E.centralizer_center_of_card E.centralizer_card

/-- Coordinates on the literal quotient, constructed by the six-coset recognition. -/
noncomputable def coreQuotientEquiv : (C D ⧸ XC D) ≃* alternatingGroup (Fin 6) :=
  (E.alternatingQuotient_of_card E.centralizer_card).some

/-- The covering map is the original quotient projection in these coordinates. -/
theorem coreCoverMap_apply (c : C D) :
    E.coreCoverMap E.centralizer_card c =
      E.coreQuotientEquiv (QuotientGroup.mk' (XC D) c) := rfl

/-- Actual application to the extension-recognition input: both the cover premises
and the independent actor premises are now discharged by 47.1–47.2. -/
theorem centralizerCalculation : Nonempty (CentralizerCalculation D) :=
  E.centralizerCalculation_of_cover E.centralizer_perfect E.core_recognition.2.1

end EarlierConclusions
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
