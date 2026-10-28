module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.OddModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.EvenModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.BinaryLinearModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.OtherSporadic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.MathieuTwentyTwo
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.MathieuTwentyFour
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock
/-!
# The exceptional containing catalogue reduced to J₄

The full simple Theorem C catalogue is inspected for a normalized local
J₂, M₂₃ or PSL₃(4) section. Odd, rank-one, binary higher-linear and all
unwanted sporadic rows are excluded by actual Sylow and local-quotient
calculations. The rank-two rows force equality. The acceptable enlarged
J₂ and M₂₃ components are retained, together with J₄ as the sole remaining
proper-containing row. This theorem does not assume or assert the
unproved J₄ local-overgroup exclusion.

Source: Aschbacher–Smith A.3.12 and 13.6.27, pp.47–48,934.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- The literal simple-containing conclusion, preserving the one remaining J₄ row. -/
theorem simple_models (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : IsModel (B ⧸ pCore 2 B)) (hm : TheoremCModel G) :
    B = ⊤ ∨ Nonempty (G ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty (G ≃* Sporadic.Mathieu.M23) ∨ Nonempty (G ≃* Janko4.Model) := by
  cases hm with
  | alternating n hn he =>
    apply Or.inl
    apply eq_top_of_card_le B h
    rw [Nat.card_congr he.some.toEquiv]
    obtain ⟨hn5, hn8⟩ := hn
    interval_cases n <;> rw [nat_card_alternatingGroup] <;> norm_num [Nat.factorial]
  | linear_odd p e hp ho he hs hm =>
    exact (not_section_of_odd_model
      (.linear_two p e hp ho (by rcases he with rfl | rfl <;> decide) hm) B h).elim
  | three_odd p hp ho un hm =>
    cases un
    · exact (not_section_of_odd_model (.linear_three p hp ho hm) B h).elim
    · exact (not_section_of_odd_model (.unitary_three p hp ho hm) B h).elim
  | rank_one hm => exact (not_section_of_bender_model S B hB hn h hm).elim
  | rank_two hm =>
    apply Or.inl
    cases hm with
    | linear n hn' hm => exact eq_top_of_rankTwo S hB hn h (.linear hn' hm)
    | symplectic n hn' hm => exact eq_top_of_rankTwo S hB hn h (.symplectic hn' hm)
    | g2 n hn' hm => exact eq_top_of_rankTwo S hB hn h (.g2 hn' hm)
    | triality n hn' hm => exact eq_top_of_rankTwo S hB hn h (.triality hn' hm)
    | ree m hm he =>
      exact eq_top_of_rankTwo S hB hn h
        (.ree_f4 m hm rfl ((ReeF4.exists_localBlockInput_mulEquiv_iff G m).mp he))
    | symplectic_derived he => exact eq_top_of_rankTwo S hB hn h (.symplectic_derived rfl he)
    | g2_derived he => exact eq_top_of_rankTwo S hB hn h (.g2_derived rfl he)
    | tits he => exact eq_top_of_rankTwo S hB hn h (.tits rfl he)
  | binary_linear n hn' hm => exact (not_section_of_binaryFour_or_Five S B hB hn h hn' hm).elim
  | sporadic name hne he =>
    obtain ⟨e⟩ := he
    cases name with
    | m11 => exact (not_mathieu_eleven h e).elim
    | m12 => exact (not_mathieu_twelve h e).elim
    | m22 => exact (not_mathieu_twentyTwo S B hn h e).elim
    | m23 => exact Or.inr (Or.inr (Or.inl ⟨e⟩))
    | m24 => exact (not_mathieu_twentyFour S B hB hn h e).elim
    | j2 => exact Or.inr (Or.inl ⟨e⟩)
    | j3 => exact (hne rfl).elim
    | j4 => exact Or.inr (Or.inr (Or.inr ⟨e⟩))
    | hs => exact (not_higmanSims S B hB hn h e).elim
    | he => exact (not_held S B hB hn h e).elim
    | ru => exact (not_rudvalis S B hB hn h e).elim
  | janko_one he => exact (not_janko_one h he.some).elim

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
