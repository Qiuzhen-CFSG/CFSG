/-
Authors: OpenAI
-/

module
public import Submission.FeitThompson.BGsection3.Defs

public import Submission.FeitThompson.Representation.CyclicQuotientExtension
public import Submission.FeitThompson.Representation.SolvableDimension
public import Submission.FeitThompson.LinearAlgebra.PrimitiveRootEigenspaces
public import Submission.FeitThompson.Representation.ExtraspecialFixedPoints
public import Submission.FeitThompson.Representation.TwoDimensionalOddOrder
public import Submission.FeitThompson.Representation.ElementaryAbelianAutomorphisms
public import Submission.FeitThompson.GeneratorRank
public import Submission.FeitThompson.BGsection4.Defs
import Submission.FeitThompson.PCore.PCore
import Submission.FeitThompson.PGroup.NormalSubgroups
import Submission.FeitThompson.Representation.ElementaryAbelianAutomorphisms
import Mathlib.GroupTheory.Schreier

/-! # Definitions for BG Section 5 -/

section

/-- Elementary abelian `p`-subgroups of order `p^n`. -/
@[expose] public def elementaryAbelianSubgroupsOfRank (p n : ℕ) (G : Type*) [Group G] :
    Set (Subgroup G) :=
  {A | Nat.card A = p ^ n ∧ IsElementaryAbelian p A}

/-- Maximal elementary abelian `p`-subgroups. -/
@[expose] public def maximalElementaryAbelianSubgroups (p : ℕ) (G : Type*) [Group G] :
    Set (Subgroup G) :=
  {A | IsElementaryAbelian p A ∧
    ∀ B : Subgroup G, A ≤ B → IsElementaryAbelian p B → A = B}

/- The group rank, defined through elementary abelian subgroups. -/
-- @[expose] public noncomputable def groupRank (G : Type*) [Group G] : ℕ :=
--   sSup {n : ℕ | ∃ p : ℕ, Nat.Prime p ∧
--     ∃ A : Subgroup G, A ∈ elementaryAbelianSubgroupsOfRank p n G}

/-- Blackburn's `SCN_n(G)`: self-centralizing normal subgroups of rank at least `n`. -/
@[expose] public noncomputable def scnSubgroups (n : ℕ) (G : Type*) [Group G] :
    Set (Subgroup G) :=
  {A | A.Normal ∧ Subgroup.centralizer (A : Set G) = A ∧ n ≤ groupRank A}

/-- The subgroup `Ω₁(Z(G))` inside `G`. -/
@[expose] public def Ω₁Z (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  (omega₁ (G := Subgroup.center G) (p := p)).map (Subgroup.center G).subtype

/-- The subgroup `Ω₁(Z₂(G))` inside `G`. -/
@[expose] public abbrev Ω₁Z₂ (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  z2OmegaCandidate p

@[expose] public abbrev CΩ₁Z₂ (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  Subgroup.centralizer (Ω₁Z₂ p G : Set G)

/-- A finite `p`-group is narrow if it has rank at most two, or if it admits a subgroup of
order `p` whose centralizer splits with a cyclic complement. -/
@[expose] public noncomputable def IsNarrowPGroup
    (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  IsPGroup p G ∧ (groupRank G ≤ 2 ∨ (∃ R₀ R₁ : Subgroup G, Nat.card R₀ = p ∧ IsCyclic R₁ ∧
      Disjoint R₀ R₁ ∧ Subgroup.centralizer (R₀ : Set G) = R₀ ⊔ R₁))

end

public theorem generatorRank_le_natCard_local
    (G : Type*) [Group G] [Finite G] :
    generatorRank G ≤ Nat.card G := by
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨S, hS_card, _hS_top⟩ := Group.rank_spec G
  calc
    generatorRank G = Group.rank G := generatorRank_eq_group_rank G
    _ = S.card := by rw [← hS_card]
    _ ≤ Fintype.card G := by simpa using Finset.card_le_univ S
    _ = Nat.card G := by simp [Nat.card_eq_fintype_card]

public theorem generatorRank_le_groupRank_of_commutative_pgroup
    {p : ℕ} [Fact p.Prime]
    (G : Type*) [Group G] [Finite G] [IsMulCommutative G] [Fact (IsPGroup p G)] :
    generatorRank G ≤ groupRank G := by
  have hprimeRank_le_natCard : ∀ q : ℕ, primeRank q G ≤ Nat.card G := by
    intro q
    rw [primeRank]
    refine csSup_le ?_ ?_
    · exact ⟨0, ⊥, IsPGroup.of_bot (p := q) (G := G), inferInstance, zero_le _⟩
    · intro n hn
      rcases hn with ⟨A, _hAp, _hAcomm, hnA⟩
      exact hnA.trans <| (generatorRank_le_natCard_local A).trans (Subgroup.card_le_card_group A)
  have htop_rank : generatorRank (⊤ : Subgroup G) = generatorRank G := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr Subgroup.topEquiv
  have hprimeRank : generatorRank G ≤ primeRank p G := by
    rw [primeRank]
    refine le_csSup ?_ ?_
    · exact ⟨Nat.card G, fun n hn => by
        rcases hn with ⟨A, _hAp, _hAcomm, hnA⟩
        exact hnA.trans <| (generatorRank_le_natCard_local A).trans (Subgroup.card_le_card_group A)⟩
    · exact ⟨⊤, by simpa using (Fact.out : IsPGroup p G).to_subgroup (⊤ : Subgroup G),
        inferInstance, by simp [htop_rank]⟩
  rw [groupRank]
  refine le_csSup ?_ ?_
  · exact ⟨Nat.card G, fun n hn => by
      rcases hn with ⟨q, _hq, hnq⟩
      exact hnq.trans (hprimeRank_le_natCard q)⟩
  · exact ⟨p, Fact.out, hprimeRank⟩
