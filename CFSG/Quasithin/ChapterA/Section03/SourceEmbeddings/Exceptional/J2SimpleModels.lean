module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.OddModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.EvenModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.SporadicModels
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
/-!
# The complete simple-containing catalogue for a local J₂ section

Every simple Theorem C carrier is inspected with the original smaller
local component and full Sylow subgroup. Odd and rank-one families are
excluded by their Sylow structure, rank-two families force equality,
and the actual sporadic normalizer calculations exclude proper overgroups.
The remaining alternating and binary-linear orders do not admit a J₂ section.

Thus a local J₂ section normalized by the full Sylow is the entire simple
containing group. This is the restricted A.3.12 conclusion used to lift
the original exceptional J₂ seed in 13.6.27.
Source: Aschbacher–Smith A.3.12, pp.47–48, and 13.6.27, p.934.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

omit [Finite G] [IsSimpleGroup G] in
private theorem j2_dvd (B : Subgroup G)
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.LeechRelated.J2.Carrier)) :
    604800 ∣ Nat.card G := by
  obtain ⟨e⟩ := h
  have hc : Nat.card (B ⧸ pCore 2 B) = 604800 :=
    (Nat.card_congr e.toEquiv).trans
      Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier
  rw [← hc]
  exact (card_quotient_dvd_card _).trans B.card_subgroup_dvd_card

omit [Finite G] [IsSimpleGroup G] in
private theorem not_binary_linear {d : ℕ} (hd : d = 4 ∨ d = 5)
    (B : Subgroup G)
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.LeechRelated.J2.Carrier))
    (hm : ClassicalGroup.IsPSL G d 2) : False := by
  have hc := j2_dvd B h
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  rw [Nat.card_congr e.toEquiv] at hc
  let : NeZero d := ⟨by omega⟩
  have ho := Atlas.ExceptionalSupport.card_psl_mul (F := F) d
  rw [hF] at ho
  rcases hd with rfl | rfl <;> norm_num [Fin.prod_univ_succ] at ho <;>
    rw [ho] at hc <;> norm_num at hc

/-- Exhaustive simple-carrier equality for the original normalized local J₂ section. -/
theorem eq_top_of_jankoTwo_theoremC (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.LeechRelated.J2.Carrier))
    (hm : TheoremCModel G) : B = ⊤ := by
  have hsection : IsModel (B ⧸ pCore 2 B) := Or.inl h
  cases hm with
  | alternating n hn he =>
    have hd := j2_dvd B h
    rw [Nat.card_congr he.some.toEquiv] at hd
    obtain ⟨hn5, hn8⟩ := hn
    interval_cases n <;> rw [nat_card_alternatingGroup] at hd <;> norm_num [Nat.factorial] at hd
  | linear_odd p e hp ho he hs hm =>
    exact (not_section_of_odd_model
      (.linear_two p e hp ho (by rcases he with rfl | rfl <;> decide) hm) B hsection).elim
  | three_odd p hp ho un hm =>
    cases un
    · exact (not_section_of_odd_model (.linear_three p hp ho hm) B hsection).elim
    · exact (not_section_of_odd_model (.unitary_three p hp ho hm) B hsection).elim
  | rank_one hm => exact (not_section_of_bender_model S B hB hn hsection hm).elim
  | rank_two hm =>
    cases hm with
    | linear n hn' hm => exact eq_top_of_rankTwo S hB hn hsection (.linear hn' hm)
    | symplectic n hn' hm => exact eq_top_of_rankTwo S hB hn hsection (.symplectic hn' hm)
    | g2 n hn' hm => exact eq_top_of_rankTwo S hB hn hsection (.g2 hn' hm)
    | triality n hn' hm => exact eq_top_of_rankTwo S hB hn hsection (.triality hn' hm)
    | ree m hm he =>
      exact eq_top_of_rankTwo S hB hn hsection
        (.ree_f4 m hm rfl ((ReeF4.exists_localBlockInput_mulEquiv_iff G m).mp he))
    | symplectic_derived he => exact eq_top_of_rankTwo S hB hn hsection (.symplectic_derived rfl he)
    | g2_derived he => exact eq_top_of_rankTwo S hB hn hsection (.g2_derived rfl he)
    | tits he => exact eq_top_of_rankTwo S hB hn hsection (.tits rfl he)
  | binary_linear n hn' hm => exact (not_binary_linear hn' B h hm).elim
  | sporadic name hne he => exact eq_top_of_jankoTwo_sporadic S B hB hn h name hne he
  | janko_one he => exact (not_janko_one hsection he.some).elim

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
