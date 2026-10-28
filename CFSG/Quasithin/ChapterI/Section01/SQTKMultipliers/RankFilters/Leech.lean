module

public import CFSG.Quasithin.ChapterI.Section01.SQTKMultipliers.RankFilters.Leech.KernelReduction
public import CFSG.Quasithin.ChapterI.Section01.SQTKMultipliers.RankFilters.Leech.Co1
public import CFSG.Quasithin.ChapterI.Section01.SQTKMultipliers.RankFilters.Leech.Co2
public import CFSG.Quasithin.ChapterI.Section01.SQTKMultipliers.RankFilters.Leech.Suz
public import CFSG.KnownSimple.LeechCarrierContribution
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.LeechSections.Co3
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.LeechClassicalSectionRanks
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.FischerCentralizerSections
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co3.CentralizerSection.TwoKernel
import all CFSG.Quasithin.ChapterA.Section02.Sporadic.LeechSections.Co3

/-!
# Local rank exclusions for the four Leech sporadics

Each fixed carrier has three-rank at least three in an actual involution
centralizer. For Co₃, coprime-kernel lifting applies to its literal classical
quotient: the checked two-graph calculation proves a two-group kernel, and
projectivization preserves that kernel. For Co₁, Co₂ and Suz, checked words
directly embed an elementary abelian group of order 27 in the existing
centralizing numerator. Thus all four groups fail quasithinness and hence
strong quasithinness, independently of A.2.15's induction on sections.

The direct embeddings discharge the other three exclusions without assertions
about their action kernels. The older conditional kernel reductions remain
available with their original statements, including the precise restriction
and projectivization conventions of the classical quotients.

The equivalence applications cover every finite simple group identified with
the fixed ATLAS models; in fact simplicity is unnecessary for these rank
obstructions. `not_stronglyQuasithin_of_identification` assembles all four
exclusions with no extra premises. `remaining_leech_identifications` applies
them to the actual seven-entry known-simple carrier contribution, leaving only
J₂, HS and McL as possible strongly quasithin entries in that contribution.

The private `import all` edge unfolds the old Co₃ record only to connect its
literal map to the separately proved kernel theorem, preserving the old API.

Source: Aschbacher--Smith, A.2.19 and I.1.3, printed pp.40--41 and 407 in
`refs/quasithin.pdf`; GLS3 Tables 5.3j, k, l and o.
-/

public section
namespace CFSG.Quasithin.ChapterI.SQTKMultipliers.RankFilters.Leech
open ChapterA

/-- The exact Co₃ quotient packaged by the chapter has a two-group kernel. -/
theorem co3_quotient_kernel_isPGroup :
    IsPGroup 2 Sporadic.LeechSections.co3QuotientData.quotientMap.ker :=
  _root_.Sporadic.LeechRelated.Co3.CentralizerSection.quotientMap_kernel_isPGroup

/-- Co₃ fails quasithinness through its actual nonsplit centralizer quotient. -/
theorem co3_not_quasithin : ¬ IsQuasithin _root_.Sporadic.LeechRelated.Co3.Carrier :=
  Sporadic.LeechSections.co3QuotientData.not_quasithin_of_rank
    co3_quotient_kernel_isPGroup 3 (by decide) leechPSp6Two_primeRank_three_gt_two

/-- In particular the fixed Co₃ model is not strongly quasithin. -/
theorem co3_not_stronglyQuasithin :
    ¬ IsStronglyQuasithin _root_.Sporadic.LeechRelated.Co3.Carrier :=
  fun h => co3_not_quasithin h.quasithin

/-- The fixed Co₁ model is not strongly quasithin. -/
theorem co1_not_stronglyQuasithin :
    ¬ IsStronglyQuasithin _root_.Sporadic.LeechRelated.Co1.Carrier :=
  fun h => co1_not_quasithin h.quasithin

/-- The fixed sporadic Suz model is not strongly quasithin. -/
theorem suz_not_stronglyQuasithin :
    ¬ IsStronglyQuasithin _root_.Sporadic.LeechRelated.Suz.Carrier :=
  fun h => suz_not_quasithin h.quasithin

variable {G : Type*} [Group G] [Finite G]

/-- The Co₁ local-rank obstruction transports through the actual carrier isomorphism. -/
theorem co1_not_quasithin_of_equiv
    (e : G ≃* _root_.Sporadic.LeechRelated.Co1.Carrier) : ¬ IsQuasithin G :=
  fun h => co1_not_quasithin (Theory.GroupTheory.isQuasithin_of_equiv e h)

/-- An actual identification with Co₃ excludes quasithinness of the source group. -/
theorem co3_not_quasithin_of_equiv
    (e : G ≃* _root_.Sporadic.LeechRelated.Co3.Carrier) : ¬ IsQuasithin G :=
  fun h => co3_not_quasithin (Theory.GroupTheory.isQuasithin_of_equiv e h)

/-- The unconditional Co₃ catalogue exclusion for I.1.3. -/
theorem co3_not_stronglyQuasithin_of_equiv
    (e : G ≃* _root_.Sporadic.LeechRelated.Co3.Carrier) : ¬ IsStronglyQuasithin G :=
  fun h => co3_not_quasithin_of_equiv e h.quasithin

/-- The four literal model alternatives all violate the two-local odd-rank bound. -/
theorem not_quasithin_of_identification
    (he : Nonempty (G ≃* _root_.Sporadic.LeechRelated.Co1.Carrier) ∨
      Nonempty (G ≃* _root_.Sporadic.LeechRelated.Co2.Carrier) ∨
      Nonempty (G ≃* _root_.Sporadic.LeechRelated.Co3.Carrier) ∨
      Nonempty (G ≃* _root_.Sporadic.LeechRelated.Suz.Carrier)) :
    ¬ IsQuasithin G := by
  rcases he with h | h | h | h <;> rcases h with ⟨e⟩
  · exact co1_not_quasithin_of_equiv e
  · exact co2_not_quasithin_of_equiv e
  · exact co3_not_quasithin_of_equiv e
  · exact suz_not_quasithin_of_equiv e

/-- The unconditional four-model exclusion used by the I.1.3 SQTK catalogue filter. -/
theorem not_stronglyQuasithin_of_identification
    (he : Nonempty (G ≃* _root_.Sporadic.LeechRelated.Co1.Carrier) ∨
      Nonempty (G ≃* _root_.Sporadic.LeechRelated.Co2.Carrier) ∨
      Nonempty (G ≃* _root_.Sporadic.LeechRelated.Co3.Carrier) ∨
      Nonempty (G ≃* _root_.Sporadic.LeechRelated.Suz.Carrier)) :
    ¬ IsStronglyQuasithin G :=
  fun h => not_quasithin_of_identification he h.quasithin

/-- Applying the four exclusions to the literal seven-entry catalogue contribution
leaves only the three other entries. This does not assert that those entries are SQTK. -/
theorem remaining_leech_identifications (hG : IsStronglyQuasithin G)
    (h : KnownSimple.IsLeechSporadicCarrier G) :
    Nonempty (G ≃* _root_.Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty (G ≃* _root_.Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty (G ≃* _root_.Sporadic.LeechRelated.McL.Carrier) := by
  obtain ⟨name, ⟨e⟩⟩ := h
  cases name with
  | j2 => exact Or.inl ⟨e⟩
  | hs => exact Or.inr (Or.inl ⟨e⟩)
  | mcl => exact Or.inr (Or.inr ⟨e⟩)
  | co1 => exact (co1_not_stronglyQuasithin_of_equiv e hG).elim
  | co2 => exact (co2_not_stronglyQuasithin_of_equiv e hG).elim
  | co3 => exact (co3_not_stronglyQuasithin_of_equiv e hG).elim
  | suz => exact (suz_not_stronglyQuasithin_of_equiv e hG).elim

/-- The original conditional kernel route, retained with its public statement.
The unconditional assembly above uses direct rank witnesses in three cases. -/
theorem not_stronglyQuasithin_of_identification_of_kernels
    (h1 : IsPGroup 2 _root_.Sporadic.LeechRelated.Co1.CentralizerSection.quotientMap.ker)
    (h2 : IsPGroup 2 _root_.Sporadic.LeechRelated.Co2.CentralizerSection.symplecticMap.ker)
    (hs : IsPGroup 2 _root_.Sporadic.LeechRelated.Suz.CentralizerSection.blockAction.ker)
    (he : Nonempty (G ≃* _root_.Sporadic.LeechRelated.Co1.Carrier) ∨
      Nonempty (G ≃* _root_.Sporadic.LeechRelated.Co2.Carrier) ∨
      Nonempty (G ≃* _root_.Sporadic.LeechRelated.Co3.Carrier) ∨
      Nonempty (G ≃* _root_.Sporadic.LeechRelated.Suz.Carrier)) :
    ¬ IsStronglyQuasithin G := by
  rcases he with h | h | h | h <;> rcases h with ⟨e⟩
  · exact co1_not_stronglyQuasithin_of_equiv_of_kernel h1 e
  · exact co2_not_stronglyQuasithin_of_equiv_of_kernel h2 e
  · exact co3_not_stronglyQuasithin_of_equiv e
  · exact suz_not_stronglyQuasithin_of_equiv_of_kernel hs e

end CFSG.Quasithin.ChapterI.SQTKMultipliers.RankFilters.Leech
