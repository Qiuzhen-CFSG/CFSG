module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Contracts
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.Normalizer
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.ModelEight
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.FusionSylow
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.TwentyOne

/-!
# Assembly of Janko's three-local conclusions

The involution-normalizer data yield ambient order-three fusion,
self-centralizing elementary Sylow three-subgroups of order nine, and an
actual nonabelian subgroup of order twenty-one. The normalizer action and
Burnside fusion then give the order alternative 72 or 144.

The final assembly discharges the three premises of the general reduction
using the imported constructions. The Case II model equivalence and
`InvolutionNormalizerData` remain explicit inputs for the parent local analysis.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Sections 3–4, pp.7–8, Lemmas 8–9.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
universe u

/-- Assemble the three-local output after proving fusion, the actual Sylow
structure, and the nonabelian subgroup of order 21. -/
public theorem threeLocalData_of_three_fusion_sylow_and_twenty_one
    {G : Type u} [Group G] [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer)
    (hf : ∀ x : G, orderOf x = 3 → IsConj x (CaseII.into D k CaseII.c))
    (hP : ∀ P : Sylow 3 G,
      IsElementaryAbelian 3 P ∧ Nat.card P = 9 ∧ centralizer (P : Set G) = P)
    (h21 : ∃ A : Subgroup G, Nat.card A = 21 ∧ ∃ x y : A, x * y ≠ y * x) :
    ThreeLocalData D k := by
  refine ⟨hf, hP, ?_, h21⟩
  intro P
  let := (hP P).1
  apply normalizer_card_of_elementary_nine_fusion P (hP P).2.1 (hP P).2.2
  intro x y hx hy
  exact (hf x hx).trans (hf y hy).symm

/-- The involution normalizers imply the selected three-local conclusions of
Janko's Lemmas 8–9, including both possible Sylow three-normalizer orders. -/
public theorem threeLocalData_of_involution_normalizers
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (h2 : InvolutionNormalizerData D k) :
    ThreeLocalData D k := by
  obtain ⟨hf, hP⟩ := three_fusion_and_sylow_of_involution_normalizers D k h2
  exact threeLocalData_of_three_fusion_sylow_and_twenty_one D k hf hP
    (nonabelian_twenty_one_of_involution_normalizers D k h2)

end Theory.GroupTheory.HeldM22A10.M22Identification
