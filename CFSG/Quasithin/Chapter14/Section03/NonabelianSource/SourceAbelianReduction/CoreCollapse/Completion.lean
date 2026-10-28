module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.Source
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.RecognitionQuotient

/-!
# Original 14.3.22 core collapse

The constructed opposite centralizer has the required actual G₂(2) quotient.
This discharges the last premise of the source transfer assembly and proves
O₂(H)=U under exactly the terminal solvability, self-centralization and outside
nonfusion inputs. The assembly splits only the perfect residual cover and uses
its index-two product with the central involution, as required by the source
correction; it does not assume a split of the whole centralizer.

Source: Aschbacher--Smith 14.3.22, printed pp.998--999; refs/quasithin.pdf.
The parent nonabelian reduction supplies the three earlier source inputs.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G]
open Recognition Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.Candidates.ComponentStructure
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)

include hG hempty hM hu hmany hcard e hnot hne hgP hgH hs



/-- Original 14.3.22: the two-core of H is precisely U. The three earlier
source inputs are unchanged; opposite-centralizer recognition is discharged.
The transfer step uses the perfect residual and its index-two product with
⟨w⟩, without splitting the whole centralizer. -/
theorem source_core_eq_U
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (hout : OutsidePointNonfusion F (sourceResidual M Mc)) : F.H.pCoreIn 2 = F.U := by
  apply source_core_eq_U_of_quotient_recognition
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hout
  intro hc z d a s
  exact OppositeCentralizer.source_triple_quotient_recognition
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself

/-- Apply the established core equality to the literal final RU-fusion
contradiction. Only the three earlier nonabelian source inputs remain. -/
theorem source_false_of_nonabelian_local_inputs
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (hout : OutsidePointNonfusion F (sourceResidual M Mc)) : False := by
  exact false_of_core_eq_span hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    (source_core_eq_U hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hout) hout

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse
