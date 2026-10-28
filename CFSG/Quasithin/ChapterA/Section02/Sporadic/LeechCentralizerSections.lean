module

public import CFSG.Quasithin.ChapterA.Section02.Sporadic.CentralizerQuotientOperations
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1.Involution
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.CentralizerRankObstruction
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.LeechClassicalSectionRanks
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.LeechSections.Co1
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.LeechSections.Co2
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.LeechSections.Co3
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.LeechSections.Suz

/-!
# The Leech sporadic centralizer sections for A.2.19

GLS3 Tables 5.3j, 5.3k, 5.3l and 5.3o give 2A centralizers with sections
Sp₆(2), Sp₆(2), Ω₈⁺(2) and Ω₆⁻(2) ≅ U₄(2), respectively, for
Co₃, Co₂, Co₁ and sporadic Suz. The first is a double cover. In the last case
the table gives the full O₆⁻(2) quotient; the simple index-two subgroup must
be pulled back. Normality is inside each numerator, not in the ambient sporadic
group. The unitary parameter 2 denotes the fixed field, so its matrices are
over a field of order 4.

The four imported constructions supply actual involutions and centralizing
numerators in the fixed ATLAS carriers, with surjections onto these exact
classical models. The intrinsic target theorems establish nonabelian simplicity
and 3-rank greater than two. Transporting the quotient data along an actual
ambient isomorphism and using centerlessness gives a simple section of a
proper two-local subgroup, strictly smaller than the ambient group.

`co1`, `co2`, `co3` and `suz` require only the source ambient finiteness and
nonabelian simplicity, together with the actual fixed-carrier identification.
Every local quotient, comparison, simplicity and rank premise is discharged.
`false_of_identification_and_section_rank_bound` connects these four witnesses
to the simple-section consequence of A.2.15(2). That earlier induction
consequence remains explicit: the parent A.2.19 assembly supplies it and
retains the covering-group reductions and final sporadic elimination.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), A.2.19, printed pp. 40--41 (PDF pp. 51--52), and
GLS3 section 5.3, local source `refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

public section

namespace CFSG.Quasithin.ChapterA.LeechCentralizerSections

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- The actual Co₁ centralizer section onto the binary split-eight group. -/
theorem co1 (hG : ¬ IsMulCommutative G)
    (e : G ≃* _root_.Sporadic.LeechRelated.Co1.Carrier) :
    InvolutionCentralizerRankObstruction G (ClassicalOrthogonal.POmegaPlus 4 (ZMod 2)) :=
  (LeechSections.Co1.classicalQuotientData.transport e.symm).rankObstruction_of_simple hG
    leechPOmega8PlusTwo_simple leechPOmega8PlusTwo_nonabelian
    leechPOmega8PlusTwo_primeRank_three_gt_two

/-- The actual Co₂ centralizer section onto the binary symplectic six-group. -/
theorem co2 (hG : ¬ IsMulCommutative G)
    (e : G ≃* _root_.Sporadic.LeechRelated.Co2.Carrier) :
    InvolutionCentralizerRankObstruction G (ClassicalGroup.PSp 3 (ZMod 2)) :=
  (LeechSections.co2CentralizerQuotient.transport e.symm).rankObstruction_of_simple hG
    leechPSp6Two_simple leechPSp6Two_nonabelian leechPSp6Two_primeRank_three_gt_two

/-- The nonsplit Co₃ centralizer supplies a quotient onto the symplectic group. -/
theorem co3 (hG : ¬ IsMulCommutative G)
    (e : G ≃* _root_.Sporadic.LeechRelated.Co3.Carrier) :
    InvolutionCentralizerRankObstruction G (ClassicalGroup.PSp 3 (ZMod 2)) :=
  (Sporadic.LeechSections.co3QuotientData.transport e.symm).rankObstruction_of_simple hG
    leechPSp6Two_simple leechPSp6Two_nonabelian leechPSp6Two_primeRank_three_gt_two

/-- The sporadic Suz section uses the simple minus orthogonal target. -/
theorem suz (hG : ¬ IsMulCommutative G)
    (e : G ≃* _root_.Sporadic.LeechRelated.Suz.Carrier) :
    InvolutionCentralizerRankObstruction G (ClassicalGroup.POmegaMinus 3 (ZMod 2)) :=
  (SuzCentralizerSection.quotientData.transport e.symm).rankObstruction_of_simple hG
    leechPOmega6MinusTwo_simple leechPOmega6MinusTwo_nonabelian
    leechPOmega6MinusTwo_primeRank_three_gt_two

/-- All four fixed-carrier alternatives produce the actual source obstruction. -/
theorem exists_obstruction (hG : ¬ IsMulCommutative G)
    (he : Nonempty (G ≃* _root_.Sporadic.LeechRelated.Co1.Carrier) ∨
      Nonempty (G ≃* _root_.Sporadic.LeechRelated.Co2.Carrier) ∨
      Nonempty (G ≃* _root_.Sporadic.LeechRelated.Co3.Carrier) ∨
      Nonempty (G ≃* _root_.Sporadic.LeechRelated.Suz.Carrier)) :
    ∃ (S : Type) (_ : Group S), InvolutionCentralizerRankObstruction G S := by
  rcases he with h | h | h | h <;> rcases h with ⟨e⟩
  · exact ⟨_, inferInstance, co1 hG e⟩
  · exact ⟨_, inferInstance, co2 hG e⟩
  · exact ⟨_, inferInstance, co3 hG e⟩
  · exact ⟨_, inferInstance, suz hG e⟩

/-- The A.2.19 application for these four simple ambient models. The earlier
A.2.15(2) rank bound is supplied by the parent simultaneous-induction proof. -/
theorem false_of_identification_and_section_rank_bound (hG : ¬ IsMulCommutative G)
    (he : Nonempty (G ≃* _root_.Sporadic.LeechRelated.Co1.Carrier) ∨
      Nonempty (G ≃* _root_.Sporadic.LeechRelated.Co2.Carrier) ∨
      Nonempty (G ≃* _root_.Sporadic.LeechRelated.Co3.Carrier) ∨
      Nonempty (G ≃* _root_.Sporadic.LeechRelated.Suz.Carrier))
    (hsource : ∀ (M : Subgroup G), M ≠ ⊤ → IsTwoLocal M →
      ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T],
        ¬ IsMulCommutative T → Section02.IsSectionOf T M → primeRank 3 T ≤ 2) :
    False := by
  obtain ⟨S, inst, h⟩ := exists_obstruction hG he
  let := inst
  exact h.false_of_section_rank_bound hsource

end CFSG.Quasithin.ChapterA.LeechCentralizerSections
