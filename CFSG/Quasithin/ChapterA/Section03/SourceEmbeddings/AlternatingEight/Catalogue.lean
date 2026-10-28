module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.Sections
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.OddBenderExclusion
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.EvenRankTwoComplete
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.Sporadic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.ContainingModels
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock
/-!
# Restricted A₈ containing-component alternatives

The full Theorem C carrier catalogue leaves only equality, PSL₅(2), M₂₄
and J₄ for a local A₈ section normalized by a full Sylow two-subgroup.
Odd families are excluded by their Sylow derived groups; even rank-two
families by local geometry and faithful Sylow actions; alternating rows by
order; and the sporadic rows by their actual local and element-order data.
The containing-component theorem applies this exhaustive dispatcher through
the literal ambient two-core quotient and excludes the central three-covers.

Source: Aschbacher–Smith A.3.12 and15.3.32(3), printed pp.47–48 and1133.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
/-- The exhaustive simple-carrier list for the original normalized local A₈ section. -/
theorem simple_models (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (hm : TheoremCModel G) :
    B = ⊤ ∨ ClassicalGroup.IsPSL G 5 2 ∨
      Nonempty (G ≃* Sporadic.Mathieu.M24) ∨ Nonempty (G ≃* Janko4.Model) := by
  cases hm with
  | alternating n hn he => exact .inl (eq_top_of_alternating B h hn he.some)
  | linear_odd p e hp ho he hs hm =>
    exact (not_linearFourTwo_section_of_odd_model
      (.linear_two p e hp ho (by rcases he with rfl | rfl <;> decide) hm) B h).elim
  | three_odd p hp ho un hm =>
    cases un
    · exact (not_linearFourTwo_section_of_odd_model (.linear_three p hp ho hm) B h).elim
    · exact (not_linearFourTwo_section_of_odd_model (.unitary_three p hp ho hm) B h).elim
  | rank_one hm => exact (not_linearFourTwo_section_of_bender_model S B hB hn h hm).elim
  | rank_two hm =>
    exfalso
    cases hm with
    | linear n hn' hm => exact not_rankTwo S hB hn h (.linear hn' hm)
    | symplectic n hn' hm => exact not_rankTwo S hB hn h (.symplectic hn' hm)
    | g2 n hn' hm => exact not_rankTwo S hB hn h (.g2 hn' hm)
    | triality n hn' hm => exact not_rankTwo S hB hn h (.triality hn' hm)
    | ree m hm he =>
      exact not_rankTwo S hB hn h
        (.ree_f4 m hm rfl ((ReeF4.exists_localBlockInput_mulEquiv_iff G m).mp he))
    | symplectic_derived he => exact not_rankTwo S hB hn h (.symplectic_derived rfl he)
    | g2_derived he => exact not_rankTwo S hB hn h (.g2_derived rfl he)
    | tits he => exact not_rankTwo S hB hn h (.tits rfl he)
  | binary_linear n hn' hm =>
    rcases hn' with rfl | rfl
    · exact .inl (eq_top_of_binary_four B h hm)
    · exact .inr (.inl hm)
  | sporadic name hne he =>
    exact .inr (.inr (sporadic_m24_or_j4 S B hB hn h name hne he))
  | janko_one he => exact (not_janko_one h he.some).elim
omit [IsSimpleGroup G] in
/-- The restricted A.3.12 conclusion for the original local A₈ component, with
all simple-model and central-cover branches discharged. -/
theorem restricted_containing_models
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hsection : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) :
    B = K ∨ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2 ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model) :=
  containing_models simple_models hG T hB hK hBK hTB hsection

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
