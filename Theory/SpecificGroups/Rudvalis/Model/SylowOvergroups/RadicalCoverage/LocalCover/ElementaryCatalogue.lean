module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Reduction
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.Coverage
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.ElementTests
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.SpanChecks
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FinCases

/-!
# The six-subgroup catalogue for the fixed Rudvalis local subgroup

For a subgroup E normal inside the fixed `localP`, every element of E squares
to one and commutes with its four generator conjugates when E is elementary
abelian. An elementwise certificate places each nonidentity element in one
of the six candidates and conjugates it to that candidate's top generator.
Five checked normal-span identities then force the whole candidate into E.
Choose the largest such candidate; the two terminal generators do not commute,
so the other terminal branch cannot occur. This proves equality with E.

`elementaryCatalogue` supplies the two finite premises of
`elementaryCatalogue_of_normalFormCertificates` using the independent coverage
and element-test proofs on the published coordinates. It establishes the
catalogue without Sylow or ambient-order assumptions or ambient-normalizer bounds.

Source: the fixed ATLAS degree-4060 words in `LocalCover.Data`. This concrete
calculation supports the [Asc86b] argument cited in Aschbacher--Smith, printed
p.511 (PDF p.528), with local structures in GLS3 Table 5.3r. The source does
not state this particular word catalogue; all word facts used here are proved
on the original permutation carrier.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
open Subgroup CatalogueCertificate
open scoped IsMulCommutative

private theorem normalized_conj_mem {E : Subgroup Model}
    (hn : localP ≤ normalizer (E : Set Model)) (w : List (Fin 8))
    {x : Model} (hx : x ∈ E) : localWord w * x * (localWord w)⁻¹ ∈ E :=
  (Subgroup.mem_normalizer_iff.mp (hn (localWord_mem w)) x).mp hx

/-- In any subgroup normalized by the fixed local subgroup, the top marked
word generates the whole corresponding candidate under conjugation. -/
public theorem elementary_le_of_generator_mem (E : Subgroup Model)
    (hn : localP ≤ normalizer (E : Set Model)) (i : Fin 6)
    (hi : elementaryGenerator i ∈ E) : elementary i ≤ E := by
  have down (j : Fin 5) (hj : elementaryGenerator (successor j) ∈ E) :
      elementaryGenerator (predecessor j) ∈ E := by
    rw [← normalSpan_step j]
    exact E.mul_mem (E.inv_mem hj) (normalized_conj_mem hn _ hj)
  fin_cases i
  · apply (Subgroup.closure_le _).mpr
    exact Set.singleton_subset_iff.mpr hi
  · have h0 := down 0 hi
    apply (Subgroup.closure_le _).mpr
    exact Set.insert_subset_iff.mpr ⟨h0, Set.singleton_subset_iff.mpr hi⟩
  · have h1 := down 1 hi
    have h0 := down 0 h1
    apply (Subgroup.closure_le _).mpr
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨h0, h1, hi⟩
  · have h2 := down 2 hi
    have h1 := down 1 h2
    have h0 := down 0 h1
    apply (Subgroup.closure_le _).mpr
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨h0, h1, h2, hi⟩
  · have h3 := down 3 hi
    have h2 := down 2 h3
    have h1 := down 1 h2
    have h0 := down 0 h1
    apply (Subgroup.closure_le _).mpr
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨h0, h1, h2, h3, hi⟩
  · have h3 := down 4 hi
    have h2 := down 2 h3
    have h1 := down 1 h2
    have h0 := down 0 h1
    apply (Subgroup.closure_le _).mpr
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨h0, h1, h2, h3, hi⟩

private theorem elementary_le_of_index (i j : Fin 6) (h : i ≤ j)
    (hne : ¬ (i = 4 ∧ j = 5)) : elementary i ≤ elementary j := by
  fin_cases i <;> fin_cases j
  all_goals try simp at h
  all_goals try simp at hne
  all_goals
    apply Subgroup.closure_mono
    simp [Set.subset_def]

/-- The four-conjugate test is necessary for membership in any relatively
normal elementary subgroup. No Sylow or ambient normality premise is used. -/
public theorem passesElementTest_of_mem (E : Subgroup Model)
    (hn : localP ≤ normalizer (E : Set Model)) [IsElementaryAbelian 2 E]
    {x : Model} (hx : x ∈ E) : PassesElementTest x := by
  refine ⟨elemPow_eq_one_of_isElementaryAbelian x hx, ?_⟩
  intro j
  exact setLike_mul_comm hx
    ((Subgroup.mem_normalizer_iff.mp (hn (localGenerators_mem j)) x).mp hx)

/-- The certified normal-span steps turn an elementwise orbit cover into
completeness of the six fixed subgroups. The elementwise cover is an explicit
remaining finite calculation, not an assumed subgroup classification. -/
public theorem elementaryCatalogue_of_elementTestCover
    (hcover : ∀ x ∈ localP, PassesElementTest x → ElementTestResult x) :
    ElementaryCatalogue := by
  classical
  intro E hE hEP hn hEA
  let := hEA
  have hresult (x : Model) (hx : x ∈ E) :
      x = 1 ∨ ∃ i : Fin 6, x ∈ elementary i ∧ elementaryGenerator i ∈ E := by
    rcases hcover x (hEP hx) (passesElementTest_of_mem E hn hx) with h | ⟨i, w, hxi, hw⟩
    · exact Or.inl h
    · refine Or.inr ⟨i, hxi, ?_⟩
      rw [← hw]
      exact normalized_conj_mem hn w hx
  let s : Finset (Fin 6) := Finset.univ.filter (fun i => elementaryGenerator i ∈ E)
  have hs : s.Nonempty := by
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE
    rcases hresult x x.property with he | ⟨i, _, hi⟩
    · exact (hx (Subtype.ext he)).elim
    · exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image (fun i => i) hs
  have hiE : elementaryGenerator i ∈ E := (Finset.mem_filter.mp hi).2
  refine ⟨i, le_antisymm ?_ (elementary_le_of_generator_mem E hn i hiE)⟩
  intro x hx
  rcases hresult x hx with rfl | ⟨j, hxj, hjE⟩
  · exact (elementary i).one_mem
  · have hji : j ≤ i := hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjE⟩)
    have hne : ¬ (j = 4 ∧ i = 5) := by
      rintro ⟨rfl, rfl⟩
      exact terminal_not_commute (setLike_mul_comm hjE hiE)
    exact elementary_le_of_index j i hji hne hxj

/-- Catalogue assembly from independent completeness and finite-test
certificates for the same published normal forms. -/
public theorem elementaryCatalogue_of_normalFormCertificates
    (hcover : NormalFormCover) (htest : NormalFormTest) : ElementaryCatalogue := by
  apply elementaryCatalogue_of_elementTestCover
  intro x hx hpass
  obtain ⟨n, rfl⟩ := hcover x hx
  exact htest n hpass

/-- Every nontrivial elementary abelian two-subgroup contained in `localP`
and normalized by `localP` equals one of the six fixed candidates. The
normal-form coverage and finite element test are both proved on the actual
degree-4060 carrier, so no additional certificate or Sylow premise remains. -/
public theorem elementaryCatalogue : ElementaryCatalogue :=
  elementaryCatalogue_of_normalFormCertificates normalFormCover normalFormTest

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
