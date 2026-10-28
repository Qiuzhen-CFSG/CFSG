module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.AlternatingSmall
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Bender
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import Theory.SpecificGroups.OddThreeRank
public import Theory.SpecificGroups.PSL2.OddAutomorphismRank

/-!
# Carrier exclusions for a large local alternating-five section

An elementary two-subgroup of order at least sixteen rules out the odd
Theorem C models, whose two-rank is at most two, and alternating groups of
degree at most seven, whose Sylow two-subgroups have order at most eight.
The full-Sylow local-component condition excludes alternating eight and
the binary higher-linear models through their actual parabolic geometry.
The properness condition excludes the Bender models through their solvable
proper Sylow overgroups. Thus only the rank-two and sporadic source C rows
remain. The smaller subgroup retains its literal two-core quotient throughout.

Source: Aschbacher–Smith A.2.4 and A.3.12, printed pp.33,47–48, in the
quasisimple point-component inspection of 10.2.9, printed pp.751–752.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.CarrierSieve
variable {G : Type*} [Group G] [Finite G]

/-- A large elementary subgroup excludes all three odd Theorem C families. -/
theorem not_odd_model (E : Subgroup G) (hE : IsElementaryAbelian 2 E)
    (hc : 16 ≤ Nat.card E) : ¬ Section02.IsTheoremCOddModel G := by
  intro hm
  have hr : primeRank 2 G ≤ 2 := by
    cases hm with
    | linear_two p n hp ho _ hm =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
      have hn : 1 ≤ n := by
        have hlarge : 1 < Nat.card F := Finite.one_lt_card
        by_contra hn
        have hz : n = 0 := by omega
        simp only [hz, pow_zero] at hF
        omega
      let : Finite PGL(2,F) :=
        Finite.of_surjective Matrix.ProjGenLinGroup.mk
          Matrix.ProjGenLinGroup.mk_surjective
      rw [primeRank_equiv 2 e]
      exact (Theory.GroupTheory.primeRank_le_of_injective 2
        Matrix.ProjectiveSpecialLinearGroup.toPGL
        Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).trans
          (Theory.PSL2.odd_pgl_two_rank F ⟨p, n, hp, ho, hn, hF⟩)
    | linear_three p hp ho hm =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
      rw [primeRank_equiv 2 e]
      exact Theory.SpecificGroups.OddThreeRank.psl3_primeRank_two_le hp ho hF
    | unitary_three p hp ho hm =>
      obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := hm
      let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
        Finite.of_equiv G e.toEquiv
      rw [primeRank_equiv 2 e]
      exact Theory.SpecificGroups.OddThreeRank.psu3_primeRank_two_le J hp ho hF hconj
  have hbound := (primeRank_le_iff_elementary_card_le G).mp hr E hE
  norm_num at hbound
  omega

private theorem small_alternating_two_rank {n : ℕ} (hn : n ≤ 7) :
    primeRank 2 (alternatingGroup (Fin n)) ≤ 3 := by
  let P : Sylow 2 (alternatingGroup (Fin n)) := Classical.choice inferInstance
  rw [P.primeRank_eq]
  apply (primeRank_le_iff_elementary_card_le P).mpr
  intro E _
  apply E.card_le_card_group.trans
  rw [P.card_eq_multiplicity]
  interval_cases n
  · have hc : Nat.card (alternatingGroup (Fin 0)) = 1 := Nat.card_unique
    rw [hc]
    simp
  · have hc : Nat.card (alternatingGroup (Fin 1)) = 1 := Nat.card_unique
    rw [hc]
    simp
  all_goals rw [nat_card_alternatingGroup, Nat.card_fin]; decide +kernel

/-- The entire alternating part of Theorem C is incompatible with the
actual full-Sylow alternating-five section and a large elementary subgroup. -/
theorem not_alternating_model
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (E : Subgroup G) (hE : IsElementaryAbelian 2 E) (hc : 16 ≤ Nat.card E)
    {n : ℕ} (hn : n ≤ 8) (e : G ≃* alternatingGroup (Fin n)) : False := by
  by_cases he : n = 8
  · subst n
    exact AlternatingSmall.not_section_eight S B hB eB e
  · have hr : primeRank 2 G ≤ 3 := by
      rw [primeRank_equiv 2 e]
      exact small_alternating_two_rank (by omega)
    have hbound := (primeRank_le_iff_elementary_card_le G).mp hr E hE
    norm_num at hbound
    omega

/-- Proper full-Sylow local components exclude the complete Bender family. -/
theorem not_bender_model [IsQuasisimple G]
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    (hproper : B ≠ ⊤) : ¬ ClassificationModels.IsBenderModel G := by
  intro hm
  have ht : (⊤ : Subgroup G).IsCComponent :=
    (show IsComponent G ⊤ from ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  exact hproper (eq_of_bender_containing_component S hB ht le_top
    (hm.of_mulEquiv topEquiv))

/-- Applying the four exclusions to the literal source catalogue leaves
only rank-two and sporadic carriers for the point-component inspection. -/
theorem rank_two_or_sporadic [IsQuasisimple G]
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    (hproper : B ≠ ⊤) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (E : Subgroup G) (hE : IsElementaryAbelian 2 E) (hc : 16 ≤ Nat.card E)
    (hm : Section02.IsTheoremCModel G) :
    (∃ f, Section02.IsTheoremCRankTwoModel G f) ∨
      Section02.IsTheoremCSporadicModel G := by
  cases hm with
  | alternating n hn e =>
    exact (not_alternating_model S B hB eB E hE hc hn e.some).elim
  | odd hm => exact (not_odd_model E hE hc hm).elim
  | bender hm => exact (not_bender_model S B hB hproper hm).elim
  | rank_two f hm => exact .inl ⟨f, hm⟩
  | linear_binary n hn hm =>
    exact (BinaryLinear.not_section_binary_linear S B hB eB hn hm).elim
  | sporadic hm => exact .inr hm

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.CarrierSieve
