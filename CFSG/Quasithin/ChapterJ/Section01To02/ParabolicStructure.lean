module

public import CFSG.Quasithin.ChapterJ.Defs
public import CFSG.Quasithin.ChapterJ.Section01To02.Preliminaries
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.Center
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.Transvections
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.CoreEquality
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.SylowChoice
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.ConjugateIntersections
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.NaturalNormalizer

/-!
# Center and parabolic structure for groups of type Ru

J.2.1 and all five clauses of J.2.2 follow from the genuine Ru1/Ru2 setup
and its source Sylow choice. The Sylow-choice bridge also constructs such
a setup from the original existential IsTypeRu hypotheses, preserving the
original center and hence all Ru2 groups and coordinate maps.

The parabolic core computation gives QS = O₂(L₁T) = R₁ and Q ≤ K.
F.9.7 supplies the H-equivariant commutator dual on Q/HC; its restriction
to K is the actual natural SL₂(4) module with the inherited quotient marking.
The full shear action of Q on U and the absence of binary transvections
in the S₅ dual action discharge the distinct-conjugate intersection argument.
All normality is relative to the indicated local group. The quotient Q/HC
corrects the printed U/HC typo in the proof of J.2.2(3).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.1–2, printed pp.432–433 (PDF pp.443–444).
-/

public section
namespace CFSG.Quasithin.ChapterJ
open Subgroup Representation
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G]

/-- J.2.1, with the center equality and its order. -/
theorem lemma_J_2_1 (d : LocalSetup G) :
    (d.T : Subgroup G) ≤ d.L ∧
    d.toTypeRuSetup.Z = d.V ⊓ centralizer ((d.T : Subgroup G) : Set G) ∧
    Nat.card d.toTypeRuSetup.Z = 2 :=
  ⟨d.T_le_L, d.center_eq, d.card_Z⟩

/-- J.2.2(1), with the two-residual and relative two-cores. -/
theorem lemma_J_2_2_one (d : LocalSetup G) :
    d.toTypeRuSetup.H ⊓ d.L = d.toTypeRuSetup.L₁ ⊔ (d.T : Subgroup G) ∧
    d.toTypeRuSetup.Q ⊔ d.toTypeRuSetup.S =
      (d.toTypeRuSetup.L₁ ⊔ (d.T : Subgroup G)).pCoreIn 2 ∧
    (d.toTypeRuSetup.L₁ ⊔ (d.T : Subgroup G)).pCoreIn 2 = d.toTypeRuSetup.R₁ ∧
    d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.K :=
  ⟨d.H_inf_L, d.Q_sup_S_eq_parabolic_core, d.parabolic_core_eq_R₁, d.Q_le_K⟩

/-- J.2.2(2), as an actual group isomorphism. -/
theorem lemma_J_2_2_two (d : LocalSetup G) :
    Nonempty (d.toTypeRuSetup.U ≃* Multiplicative (Fin 5 → ZMod 2)) := d.equiv_U

/-- J.2.2(3), discharging the earlier residual containment. -/
theorem lemma_J_2_2_three_source (d : LocalSetup G) :
    let _ : (d.toTypeRuSetup.Q.subgroupOf d.toTypeRuSetup.K).Normal :=
      d.toTypeRuSetup.Q_normal_in_K
    Nonempty ((d.toTypeRuSetup.K ⧸ d.toTypeRuSetup.Q.subgroupOf d.toTypeRuSetup.K) ≃*
      alternatingGroup (Fin 5)) ∧
    (∀ q : G, q ∈ d.toTypeRuSetup.HC ↔ q ∈ d.toTypeRuSetup.Q ∧
      ∀ k ∈ d.toTypeRuSetup.K, ⁅k, q⁆ ∈ d.toTypeRuSetup.U) ∧
    Nonempty (BinaryConjugationSection d.toTypeRuSetup.K d.toTypeRuSetup.Q d.toTypeRuSetup.HC
      (SL2FourNatural.naturalRepresentation.comp d.toTypeRuSetup.naturalQuotientMap)) :=
  lemma_J_2_2_three d d.Q_le_K

/-- J.2.2(4), as equality of the actual action image with all shears of center Z. -/
theorem lemma_J_2_2_four (d : LocalSetup G) (σ : d.toTypeRuSetup.U → G) :
    (∃ q : d.toTypeRuSetup.Q, ∀ u : d.toTypeRuSetup.U,
      (q : G) * u * (q : G)⁻¹ = σ u) ↔
    ∃ f : d.toTypeRuSetup.U →* d.toTypeRuSetup.Z,
      (∀ z : d.toTypeRuSetup.Z, f ⟨z, d.ru2.natural.kernel_le z.property⟩ = 1) ∧
      ∀ u : d.toTypeRuSetup.U, σ u = (f u : G) * u := d.transvection_image σ

/-- J.2.2(5), with every earlier section and model premise discharged. -/
theorem lemma_J_2_2_five_source (d : LocalSetup G) (l : G) (hl : l ∈ d.L)
    (hne : d.toTypeRuSetup.U.map (MulAut.conj l).toMonoidHom ≠ d.toTypeRuSetup.U) :
    let Uα := d.toTypeRuSetup.U.map (MulAut.conj l).toMonoidHom
    Uα ≤ d.toTypeRuSetup.H ∧
      Nat.card ((Uα.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap) = 2 ∧
      Uα ⊓ d.toTypeRuSetup.HC = d.V :=
  lemma_J_2_2_five d d.dualSection d.noRankOne l hl hne

/-- All five clauses of J.2.2 from the source setup, with literal conjugate
and quotient maps and no additional structural or representation premises. -/
theorem lemma_J_2_2 (d : LocalSetup G) :
    let _ : (d.toTypeRuSetup.Q.subgroupOf d.toTypeRuSetup.K).Normal :=
      d.toTypeRuSetup.Q_normal_in_K
    (d.toTypeRuSetup.H ⊓ d.L = d.toTypeRuSetup.L₁ ⊔ (d.T : Subgroup G) ∧
      d.toTypeRuSetup.Q ⊔ d.toTypeRuSetup.S =
        (d.toTypeRuSetup.L₁ ⊔ (d.T : Subgroup G)).pCoreIn 2 ∧
      (d.toTypeRuSetup.L₁ ⊔ (d.T : Subgroup G)).pCoreIn 2 = d.toTypeRuSetup.R₁ ∧
      d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.K) ∧
    Nonempty (d.toTypeRuSetup.U ≃* Multiplicative (Fin 5 → ZMod 2)) ∧
    (Nonempty ((d.toTypeRuSetup.K ⧸ d.toTypeRuSetup.Q.subgroupOf d.toTypeRuSetup.K) ≃*
        alternatingGroup (Fin 5)) ∧
      (∀ q : G, q ∈ d.toTypeRuSetup.HC ↔ q ∈ d.toTypeRuSetup.Q ∧
        ∀ k ∈ d.toTypeRuSetup.K, ⁅k, q⁆ ∈ d.toTypeRuSetup.U) ∧
      Nonempty (BinaryConjugationSection d.toTypeRuSetup.K d.toTypeRuSetup.Q d.toTypeRuSetup.HC
        (SL2FourNatural.naturalRepresentation.comp d.toTypeRuSetup.naturalQuotientMap))) ∧
    (∀ σ : d.toTypeRuSetup.U → G,
      (∃ q : d.toTypeRuSetup.Q, ∀ u : d.toTypeRuSetup.U,
        (q : G) * u * (q : G)⁻¹ = σ u) ↔
      ∃ f : d.toTypeRuSetup.U →* d.toTypeRuSetup.Z,
        (∀ z : d.toTypeRuSetup.Z, f ⟨z, d.ru2.natural.kernel_le z.property⟩ = 1) ∧
        ∀ u : d.toTypeRuSetup.U, σ u = (f u : G) * u) ∧
    (∀ l ∈ d.L,
      let Uα := d.toTypeRuSetup.U.map (MulAut.conj l).toMonoidHom
      Uα ≠ d.toTypeRuSetup.U → Uα ≤ d.toTypeRuSetup.H ∧
        Nat.card ((Uα.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap) = 2 ∧
        Uα ⊓ d.toTypeRuSetup.HC = d.V) := by
  exact ⟨lemma_J_2_2_one d, lemma_J_2_2_two d, lemma_J_2_2_three_source d,
    lemma_J_2_2_four d, lemma_J_2_2_five_source d⟩

end CFSG.Quasithin.ChapterJ
