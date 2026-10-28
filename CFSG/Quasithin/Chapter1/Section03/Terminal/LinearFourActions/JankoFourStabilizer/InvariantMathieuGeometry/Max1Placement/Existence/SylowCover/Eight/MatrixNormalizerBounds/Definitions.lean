module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.NormalizerRows
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.MatrixWords

/-!
# The three specified literal Sylow eights

These definitions use the marked words in the actual matrix two-subgroup,
with zero-based indices. They assert neither the presentation relations nor
exhaustive coverage. The coverage adapter keeps both the coverage calculation
and the ambient normalizer calculation explicit until their producers finish.

Source context: Aschbacher–Smith A.3.12, printed pp.47–48, and the literal
word provenance in `SylowNormalEights.MatrixWords`.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open Subgroup
open Janko4.OuterReduction.OddIndex
open Janko4.LocalStructure.SylowNormalEights.MatrixWords
open CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover

/-- The three prescribed generating triples, inside the literal two-subgroup. -/
noncomputable def F : Fin 3 → Subgroup twoSubgroup :=
  ![closure {pcGenerator 18, pcGenerator 19, pcGenerator 20},
    closure {pcGenerator 17, pcGenerator 19, pcGenerator 20},
    closure {pcGenerator 17 * pcGenerator 18, pcGenerator 19, pcGenerator 20}]

/-- The images use the actual inclusion into the J₄ model. -/
noncomputable def U (i : Fin 3) : Subgroup Janko4.Model :=
  (F i).map twoSubgroup.subtype

@[simp] theorem F_zero : F 0 = closure {pcGenerator 18, pcGenerator 19, pcGenerator 20} := rfl
@[simp] theorem F_one : F 1 = closure {pcGenerator 17, pcGenerator 19, pcGenerator 20} := rfl
@[simp] theorem F_two : F 2 = closure
    {pcGenerator 17 * pcGenerator 18, pcGenerator 19, pcGenerator 20} := rfl

theorem U_le_twoSubgroup (i : Fin 3) : U i ≤ twoSubgroup := map_subtype_le _

/-- The actual catalogue obligation, without centralizer-profile assumptions. -/
def Coverage : Prop :=
  ∀ A : Subgroup twoSubgroup, A.Normal → IsElementaryAbelian 2 A →
    Nat.card A = 8 → A ≤ Subgroup.upperCentralSeries twoSubgroup 3 → ∃ i, A = F i

/-- Literal coverage transfers the three ambient bounds to the existing
row contract. The profile index need not identify the chosen generating triple. -/
theorem normalizerRows_of_coverage
    (hcover : Coverage) (hbounds : ∀ i, EightNormalizerAlternative (U i)) :
    SylowEightNormalizerRows := by
  intro A hAn hAe hAc hAZ _ _
  obtain ⟨i, rfl⟩ := hcover A hAn hAe hAc hAZ
  exact hbounds i

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
