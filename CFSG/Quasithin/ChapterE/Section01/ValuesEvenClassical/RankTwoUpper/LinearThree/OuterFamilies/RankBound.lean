module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.Action
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank

/-!
# Source application of the sharp outer-actor rank bound

The faithful action on the actual PSL₃ socle transports the intrinsic
rank bound to the source ambient elementary subgroup. This
supplies the numerical step used before the centralizer witness in the
large-family argument. The family application discharges the rank premise
of `parabolics_le_of_model_calculations`, leaving only its independent
centralizer witness. The original conditional fixed-group adapter is retained.

Source: Aschbacher–Smith E.1.1–6 and E.1.14(1), printed pp.209–214.
-/

public section
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable Matrix.PSL3Even.OuterElementaryRank

namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
variable [IsSimpleGroup (generalizedFitting G)]

/-- Apply the literal fixed-group calculations through the actual socle action. -/
theorem outer_rank_le_of_fixed_calculations
    (e : generalizedFitting G ≃* PSL(3,F)) {f : ℕ} (hf : 0 < f)
    (hF : Nat.card F = 2 ^ f)
    (houterRank : primeRank 2 (standardOuter F) ≤ 2)
    (hfixed : ∀ a : MulAut PSL(3,F), a ∈ standard F → a ^ 2 = 1 →
      a ∉ MulAut.innerSubgroup PSL(3,F) → primeRank 2 a.fixedSubgroup ≤ f)
    (hmixedFixed : ∀ a : MulAut PSL(3,F), IsGraphField a → a ^ 2 = 1 →
      primeRank 2 a.fixedSubgroup ≤ f - 1)
    (hselect : ∀ E : Subgroup (MulAut PSL(3,F)), IsElementaryAbelian 2 E →
      E ≤ standard F →
      primeRank 2 (E.map (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)))) = 2 →
      ∃ a ∈ E, IsGraphField a)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (houter : ¬ A ≤ generalizedFitting G) : Group.rank A ≤ f + 1 :=
  outer_rank_le_of_model_bound e
    (rank_le_of_fixed_calculations hf hF houterRank hfixed hmixedFixed hselect)
    A hA houter

/-- The sharp ambient rank bound, with all intrinsic model premises discharged. -/
theorem outer_rank_le
    (e : generalizedFitting G ≃* PSL(3,F)) {f : ℕ} (hf : 0 < f)
    (hF : Nat.card F = 2 ^ f)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (houter : ¬ A ≤ generalizedFitting G) : Group.rank A ≤ f + 1 :=
  outer_rank_le_of_model_bound e (rank_le_of_not_le_inner hf hF) A hA houter

/-- In the large outer-family branch of E.1.14(1), the numerical rank
premise is now proved. The independent centralizer witness, including its
E1/E2 and generation clauses, remains with the source assembly owner. -/
theorem parabolics_le_of_centralizer_witness
    (e : generalizedFitting G ≃* PSL(3,F)) (T : Sylow 2 G) {f : ℕ}
    (hf : 0 < f) (hF : Nat.card F = 2 ^ f)
    (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (hlocal : ∀ A : Subgroup G, IsElementaryAbelian 2 A →
      A ≤ (T : Subgroup G) → ¬ A ≤ generalizedFitting G → Group.rank A = f + 1 →
      HasCentralizerLocalWitness (generalizedFitting G) T A)
    (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω)
    (hex : ∃ A ∈ Ω, A ≤ (T : Subgroup G) ∧ A ≠ ⊥)
    (houter : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ →
      ¬ A ≤ generalizedFitting G)
    (hlarge : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ → f < Group.rank A) :
    let M := eFamilySubgroup f (T : Subgroup G) Ω ⊔
      normalizer (weakClosure (T : Subgroup G) Ω : Set G)
    (pointParabolic F).map (linearThreeEmbedding (generalizedFitting G) e) ≤ M ∧
      (lineParabolic F).map (linearThreeEmbedding (generalizedFitting G) e) ≤ M :=
  parabolics_le_of_model_calculations e T hf hLT (rank_le_of_not_le_inner hf hF)
    hlocal Ω hΩ hex houter hlarge

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies
