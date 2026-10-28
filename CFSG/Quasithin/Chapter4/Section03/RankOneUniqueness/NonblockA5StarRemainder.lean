module

public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockA5BinaryFiveExclusion
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockA5LinearThreeExclusion
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesFinite
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalA5EightExclusion
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalA5SymplecticAlignment
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalA5G2Alignment

/-!
# The remaining actual star components in the original A₅ configuration

Apply the complete C.2.7 catalogue to the unchanged constrained source
component. The original normal seed excludes the binary five-space and
eight-point rows. The original chosen permutation core excludes SL₃;
the rank-one, six-point and derived binary G₂ exclusions remove the other
small rows. Only Sp₄, G₂ and A₇ remain. The literal normal-seed alignments
force the two Lie-type coefficient fields to have four elements.

These are markings of the actual star image, not identifications of the
whole two-core quotient or a claim that the source component is a block.
No row-selection or module-classification callback is an assumption.
Source: Aschbacher--Smith C.2.7, C.4.5--8 and original 4.3.7--10,
pp.145--154 and 615--617, specialized to the original A₅ module.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open ChapterC ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- The original A₅ configuration leaves exactly these three possible star
families; the two binary Lie-type rows have the forced field degree two. -/
theorem a5_star_remainder
    (d : Chapter13.Section05.A5Source.Context T L V V₁ V₂ V₃)
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K) :
    (∃ F : BinaryField, F.degree = 2 ∧ Nonempty
      (starImage (K c) (c.I.pCoreIn 2) (K c) ≃*
        Theory.SpecificGroups.SymplecticFour.Sp F.Carrier)) ∨
    (∃ F : BinaryField, F.degree = 2 ∧ Nonempty
      (starImage (K c) (c.I.pCoreIn 2) (K c) ≃* Atlas.G2.Model F.Carrier)) ∨
    Nonempty (starImage (K c) (c.I.pCoreIn 2) (K c) ≃* alternatingGroup (Fin 7)) := by
  have hn : (L.subgroupOf (c.H ⊓ normalizer (L : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer inf_le_right
  cases c.block_star_models hf with
  | linearTwo F e => exact (c.block_star_not_linearTwo hf F e).elim
  | linearThree F e => exact (not_linearThree_star_of_a5 d c hf F e).elim
  | symplectic F hF e =>
    have hfour := (c.c28.constrained_normal_a5_symplectic_alignment hn d.quotient
      c.K c.component c.quotient c.block_source_outside hf e F.card_eq hF).1
    have hdegree : F.degree = 2 := Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
      (show 2 ^ F.degree = 2 ^ 2 from F.card_eq.symm.trans hfour)
    exact Or.inl ⟨F,hdegree,⟨e⟩⟩
  | g2 F hF e =>
    have hlarge : 4 ≤ Nat.card F.Carrier := by
      rw [F.card_eq]
      exact (show 4 = 2 ^ 2 from rfl).trans_le
        (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hF)
    have hfour := (c.c28.constrained_normal_a5_g2_alignment hn d.quotient
      c.K c.component c.quotient c.block_source_outside hf e hlarge).1
    have hdegree : F.degree = 2 := Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
      (show 2 ^ F.degree = 2 ^ 2 from F.card_eq.symm.trans hfour)
    exact Or.inr (Or.inl ⟨F,hdegree,⟨e⟩⟩)
  | g2DerivedTwo e => exact (c.block_star_not_g2DerivedTwo hf e).elim
  | alternating n hd e =>
    rcases hd with rfl | rfl | rfl | rfl
    · exact (c.block_star_not_alternatingFive hf e).elim
    · exact (c.block_star_not_alternatingSix hf e).elim
    · exact Or.inr (Or.inr ⟨e⟩)
    · exact (c.c28.no_constrained_normal_a5_star_alternating_eight hn d.quotient
        c.K c.component c.quotient c.block_source_outside hf e).elim
  | linearFiveTwo e => exact (not_linearFiveTwo_star_of_a5 c hf d.quotient e).elim
  | tripleSix _ e => exact (c.block_star_central_not_alternatingSix hf e).elim

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
