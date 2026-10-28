module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Triality.SourceAlignment.Automorphisms
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.NormalForm.Coefficients

/-!
# Source field automorphisms meet the triality inner-diagonal group trivially

In characteristic two the genuine graph-field fixed group equals its elementary
subgroup. Consequently its conjugation action on the elementary central quotient
has exactly the inner automorphisms as image. The existing coefficient separation
theorem uses the two opposite Borels to put an inner conjugator in the torus;
the folded root parameter then detects the coefficient automorphism. Normality
of the inner subgroup extends this separation to Aut-conjugates.

The source field predicate retains the prime-to-three order condition of GLS3
Definition 2.5.13(c)(1). The coefficient separation used here holds for the full
cubic coefficient group, including its graph part. No simplicity, automorphism
coverage, or additional geometric hypothesis is needed.

`sourceField_eq_one_of_mem_innerDiagonal_of_q_eq` supplies the literal separation
premise of `RawConfiguration.field_disjoint_part` and the subsequent raw Cartan
extraction. The raw configuration and final alignment remain with their owners.

Sources: Aschbacher–Smith, Notation A.2.5, printed p.33, and A.3.15(5), pp.50–51
(`refs/quasithin.pdf`); GLS3 §§2.2 and 2.5, especially 2.2.6, 2.5.12(c), and
Definition 2.5.13 (`refs/KGroup/GLS3/chapter2.tex`). All maps use the original
graph-field fixed group and the elementary subgroup's own central quotient.
-/

public section
noncomputable section
open Triality.Standard Triality.Standard.OuterOdd
open Triality.Standard.ConcreteBruhat.FixedDescent

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Triality.SourceAlignment

/-- The actual fixed-point conjugation image is the inner group in characteristic two. -/
theorem innerDiagonal_eq_inner (P : Parameters) (hp : P.prime = 2) :
    innerDiagonal P = MulAut.innerSubgroup (Carrier P) := by
  apply le_antisymm
  · rintro a ⟨g, rfl⟩
    let y : ElementaryGroup P := ⟨g, (elementarySubgroup_eq_top P hp).ge trivial⟩
    exact ⟨toCarrier P y, (fixedConjugation_inner P y).symm⟩
  · exact inner_le_innerDiagonal P

/-- Even the full cubic coefficient group meets the fixed-point conjugation image trivially. -/
theorem coefficientAction_mem_innerDiagonal_iff (P : Parameters) (hp : P.prime = 2)
    (σ : CoefficientAut P) : coefficientAction P σ ∈ innerDiagonal P ↔ σ = 1 := by
  rw [innerDiagonal_eq_inner P hp]
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  exact Triality.Standard.EvenField.NormalForm.coefficientAction_mem_inner_iff n hn σ

/-- A source field automorphism induced by a fixed-point conjugation is trivial. -/
theorem sourceField_eq_one_of_mem_innerDiagonal (P : Parameters) (hp : P.prime = 2)
    (a : MulAut (Carrier P)) (ha : IsSourceFieldAutomorphism P a)
    (hi : a ∈ innerDiagonal P) : a = 1 := by
  obtain ⟨σ, _, hc⟩ := ha
  have hn : (innerDiagonal P).Normal := by
    rw [innerDiagonal_eq_inner P hp]
    infer_instance
  obtain ⟨b, hb⟩ := isConj_iff.mp hc.symm
  have hσ : coefficientAction P σ ∈ innerDiagonal P :=
    hb ▸ hn.conj_mem a hi b
  have he := (coefficientAction_mem_innerDiagonal_iff P hp σ).mp hσ
  subst σ
  simpa only [map_one, isConj_one_right] using hc

/-- The separation premise required by raw A.3.15(5), with its exact field-order range. -/
theorem sourceField_eq_one_of_mem_innerDiagonal_of_q_eq (P : Parameters)
    (n : ℕ) (hq : P.q = 2 ^ n) (hn : 1 < n)
    (a : MulAut (Carrier P)) (ha : IsSourceFieldAutomorphism P a)
    (hi : a ∈ innerDiagonal P) : a = 1 := by
  have hp : P.prime = 2 := by
    rw [P.eq_binaryParameters_of_q_eq n (by omega) hq]
    rfl
  exact sourceField_eq_one_of_mem_innerDiagonal P hp a ha hi

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Triality.SourceAlignment
