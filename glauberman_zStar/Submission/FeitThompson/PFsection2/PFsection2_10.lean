module

public import Submission.FeitThompson.PFsection2.Basic

/-!
# Peterfalvi, Section 2: Theorem (2.10)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section2
universe u

/-! ## (2.10) -/

@[expose] public noncomputable def dadeInclusionExclusionSum {G : Type u}
    [Group G] [Finite G] (L : Subgroup G) (H : G → Subgroup G)
    (reps : Finset (Set G))
    (αB : (B : Set G) → Section1.ClassFunction (MOfSet H L B)) :
    Section1.ClassFunction G :=
  fun g => -(reps.sum fun B =>
    ((-1 : ℂ) ^ Nat.card B) * Section1.inducedCF (MOfSet H L B) (αB B) g)

@[expose] public def proposition_2_10_1_statement {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G)
    (_h : Hypothesis2 A L H) (α : Section1.ClassFunction L) : Prop :=
  CFOn L A α →
    ∀ ⦃B : Set G⦄, B.Nonempty → B ⊆ A →
      ∀ x : L,
        ∀ (αB : Section1.ClassFunction (MOfSet H L B))
          (αBx : Section1.ClassFunction (MOfSet H L (setConjugateBy (x : G) B))),
            alphaBSpec H α B αB →
              alphaBSpec H α (setConjugateBy (x : G) B) αBx →
                Section1.inducedCF (MOfSet H L (setConjugateBy (x : G) B)) αBx =
                  Section1.inducedCF (MOfSet H L B) αB

@[expose] public def proposition_2_10_2_statement {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (_h : Hypothesis2 A L H) : Prop :=
  ∀ ⦃B : Set G⦄, B.Nonempty → B ⊆ A →
    ∀ ⦃a : G⦄, a ∈ A →
      centralizerIn (HInter H B) a = HInter H (B ∪ {a})

@[expose] public def dadeInductionFormulaTerm {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (α : Section1.ClassFunction L) (g a : G) (B : Set G)
    (hAL : ∀ a ∈ A, a ∈ L) (ha : a ∈ A) : ℂ :=
  (α ⟨a, hAL a ha⟩) * (Nat.card (MOfSet H L B) : ℂ)⁻¹ *
    ∑ b : {b : G // b ∈ normalizerIn L B ∧ conjugateInSubgroup L a b},
      (Nat.card (transporterSet g
        (rightTranslateSet (HInter H B : Set G) (b : G))) : ℂ)

@[expose] public def proposition_2_10_3_statement {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G)
    (_h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L) (α : Section1.ClassFunction L) : Prop :=
  CFOn L A α →
    ∀ ⦃B : Set G⦄, B.Nonempty → B ⊆ A →
      ∀ αB : Section1.ClassFunction (MOfSet H L B),
        alphaBSpec H α B αB →
          (∀ g : G, g ∉ dadeSupport A H →
            Section1.inducedCF (MOfSet H L B) αB g = 0) ∧
          (∀ ⦃g a : G⦄, (ha : a ∈ A) → g ∈ conjugateSet (cosetProduct a (H a)) →
            Section1.inducedCF (MOfSet H L B) αB g =
              dadeInductionFormulaTerm A L H α g a B hAL ha)

@[expose] public def proposition_2_10_statement {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G)
    (_h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L) : Prop :=
  ∀ (reps : Finset (Set G))
    (α : Section1.ClassFunction L)
    (αB : (B : Set G) → Section1.ClassFunction (MOfSet H L B)),
      IsRepresentativeSystemForNonemptySubsets A L reps →
        CFOn L A α →
          (∀ B ∈ reps, alphaBSpec H α B (αB B)) →
            dadeTransform H hAL α =
              dadeInclusionExclusionSum L H reps αB

end Section2
