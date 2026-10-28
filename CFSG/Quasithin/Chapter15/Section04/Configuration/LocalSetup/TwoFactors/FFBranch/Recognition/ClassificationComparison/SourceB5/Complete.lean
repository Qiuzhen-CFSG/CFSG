module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SourceB5.Quasisimple
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.Complete

/-!
# Complete corrected B.5 input for the literal mixed-factor consumer

The original finite SQTK cover and all FF hypotheses are passed to the
proved lower classification. The returned module factors, internal product,
fixed-space quotient and hyperplane clauses are retained verbatim through
the coordinate maps. The adequate outer A₆--C₃ group alternative is unchanged.
The complete earlier B.5.1 and general B.5.6 implications are then assembled
for the full known-simple catalogue, with no remaining classification input.

Source: Aschbacher--Smith B.5.1--12, applied in15.4.18--20.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.SourceB5
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V}

theorem factorNatural (h : ChapterB.SourceInduction.FactorNatural ρ) : FactorNatural ρ := by
  cases h with
  | linearTwo F h => obtain ⟨e⟩ := h; exact .linearTwo (field F) ⟨action e⟩
  | symmetricFive h => obtain ⟨e⟩ := h; exact .symmetricFive ⟨action e⟩
  | linearThree F ho h => obtain ⟨e⟩ := h; exact .linearThree (field F) ho ⟨action e⟩

theorem factorCase {A : Subgroup D} {U : Subrepresentation ρ}
    (h : ChapterB.SourceInduction.SourceFactorCase ρ A U) : SourceFactorCase ρ A U := by
  cases h with
  | natural hm hn => exact .natural hm (factorNatural hn)
  | doubleNatural F ho hm hn => obtain ⟨e⟩ := hn; exact .doubleNatural (field F) ho hm ⟨action e⟩
  | exceptional hm he => exact .exceptional hm (four he)

def pair (h : ChapterB.SourceInduction.SourceTwoFactorCase ρ) : SourceTwoFactorCase ρ where
  first := h.first
  second := h.second
  product := ⟨h.product.equiv,h.product.apply_eq⟩
  firstSpace := h.firstSpace
  secondSpace := h.secondSpace
  decomposition := h.decomposition
  firstCase := factorCase h.firstCase
  secondCase := factorCase h.secondCase

theorem hyperplaneSecond {A : Subgroup D} {U : Subrepresentation ρ}
    (h : ChapterB.SourceInduction.HyperplaneSecondCase ρ A U) : HyperplaneSecondCase ρ A U := by
  cases h with
  | linearThree r hr hn => obtain ⟨e⟩ := hn; exact .linearThree r hr ⟨action e⟩
  | linearTwo F hn => obtain ⟨e⟩ := hn; exact .linearTwo (field F) ⟨action e⟩

def hyperplane (h : ChapterB.SourceInduction.HyperplaneCase ρ) : HyperplaneCase ρ where
  first := h.first
  second := h.second
  product := ⟨h.product.equiv,h.product.apply_eq⟩
  firstEquiv := h.firstEquiv
  firstDimension := h.firstDimension
  disjoint := h.disjoint
  moved_eq := h.moved_eq
  hyperplane := h.hyperplane
  secondSpace := h.secondSpace
  secondSpace_eq := h.secondSpace_eq
  secondCase := hyperplaneSecond h.secondCase

theorem alternative [Finite D] (h : ChapterB.SourceInduction.AdequateAlternative ρ) :
    ProjectiveLine.AdequateSourceAlternative ρ := by
  rcases h with h | h
  · exact .trivial h
  cases h with
  | quasisimple hq hc => exact .quasisimple hq (quasisimpleConclusion hc)
  | symmetricThree h => exact .symmetricThree ⟨h.equiv,h.decomposition,h.dimension⟩
  | twoFactors h => exact .twoFactors (pair h)
  | outerSixThree h => exact .outerSixThree h
  | hyperplane h => exact .hyperplane (hyperplane h)

theorem hypothesis [Finite D] {K : GroupClass.{u}} (h : FFHypothesis K ρ) :
    ChapterB.SourceInduction.FFHypothesis K ρ := by
  refine ⟨h.finite_module,h.faithful,h.twoCore,h.generated,?_⟩
  obtain ⟨q⟩ := h.quotient
  exact ⟨{
    Cover := q.Cover
    coverGroup := q.coverGroup
    coverFinite := q.coverFinite
    kernel := q.kernel
    kernelNormal := q.kernelNormal
    sqtk := q.sqtk
    equiv := q.equiv }⟩

theorem classification :
    ProjectiveLine.AdequateCompleteClassificationInput.{u,v} KnownSimple.IsKnownSimple where
  quasisimple := quasisimpleInput
    (ChapterB.QuasisimpleSource.SourceCompletion.knownSimple_quasisimpleClassificationInput
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (ChapterA.SQTKStructure.a36Input_of_theoremsAC
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
      ChapterB.SourceClassification.irreducibleClassification_knownSimple
      ChapterB.SourceInduction.nonbinaryG2RootPairInput)
  general := fun _ _ _ _ _ _ ρ h =>
    alternative (ChapterB.SourceInduction.adequateAlternative_knownSimple ρ (hypothesis h))
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.SourceB5
