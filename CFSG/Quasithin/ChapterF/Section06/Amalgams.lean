module

public import CFSG.Quasithin.ChapterF.Section06.Elementary.Quotient
public import CFSG.Quasithin.ChapterF.Section06.Amalgams.WeakBN
public import CFSG.Quasithin.ChapterF.Section06.Amalgams.CaseOne

/-!
# Entry to the Goldschmidt amalgam classification

Apply the proved F.6.5(1) quotient transport without changing its maps.
The quotient vertices either satisfy the genuine source F.1.1 hypotheses,
or one vertex has a normal cubic residual centralizing its two-core and
its generalized Fitting subgroup is not a two-group. The imported first
case identifies the actual (S₃,C₂,S₃) amalgam, including both embeddings.

Source: Aschbacher–Smith Remark F.6.4 and Lemma F.6.5, printed pp.304–305.
The remaining exceptional identifications, the mixed-vertex order bound
and the F.1.12 six-case specialization are still required for full F.6.5.
This module does not assert the unproved eleven-case enumeration.
-/

public section

namespace CFSG.Quasithin.ChapterF
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

 theorem IsGoldschmidtTriple.source_branch_or_cubic_residual
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥) :
    Source.HypothesisF11 (goldschmidtVertices G₁ G₂) (G₁ ⊓ G₂) ∨
      (¬ IsPGroup 2 (generalizedFitting G₁)) ∧ Nat.card (pResidual 2 G₁) = 3 ∧
        (pCore 2 G₁).map G₁.subtype ≤ centralizer ((pResidual 2 G₁).map G₁.subtype : Set G) ∨
      (¬ IsPGroup 2 (generalizedFitting G₂)) ∧ Nat.card (pResidual 2 G₂) = 3 ∧
        (pCore 2 G₂).map G₂.subtype ≤ centralizer ((pResidual 2 G₂).map G₂.subtype : Set G) := by
  classical
  by_cases h₁ : generalizedFitting G₁ = pCore 2 G₁
  · by_cases h₂ : generalizedFitting G₂ = pCore 2 G₂
    · exact Or.inl (h.source_hypothesis_of_characteristic_two hcore h₁ h₂)
    · exact Or.inr (Or.inr ⟨fun hp => h₂
        ((SymmetricThreeTwoCore.generalizedFitting_isTwoGroup_iff h.quotient_right.some).mp hp),
        h.symm.local_residual_order_three h₂, h.symm.local_core_centralizes_residual h₂⟩)
  · exact Or.inr (Or.inl ⟨fun hp => h₁
      ((SymmetricThreeTwoCore.generalizedFitting_isTwoGroup_iff h.quotient_left.some).mp hp),
      h.local_residual_order_three h₁, h.local_core_centralizes_residual h₁⟩)

 theorem IsGoldschmidtTriple.quotient_source_branch_or_cubic_residual
    (h : IsGoldschmidtTriple G₁ G₂) :
    let q := QuotientGroup.mk' (pCore 2 G)
    let A := G₁.map q
    let B := G₂.map q
    Source.HypothesisF11 (goldschmidtVertices A B) (A ⊓ B) ∨
      (¬ IsPGroup 2 (generalizedFitting A)) ∧ Nat.card (pResidual 2 A) = 3 ∧
        (pCore 2 A).map A.subtype ≤ centralizer ((pResidual 2 A).map A.subtype : Set (G ⧸ pCore 2 G)) ∨
      (¬ IsPGroup 2 (generalizedFitting B)) ∧ Nat.card (pResidual 2 B) = 3 ∧
        (pCore 2 B).map B.subtype ≤ centralizer ((pResidual 2 B).map B.subtype : Set (G ⧸ pCore 2 G)) :=
  h.quotient_twoCore.source_branch_or_cubic_residual h.quotient_twoCore_eq_bot
end CFSG.Quasithin.ChapterF
