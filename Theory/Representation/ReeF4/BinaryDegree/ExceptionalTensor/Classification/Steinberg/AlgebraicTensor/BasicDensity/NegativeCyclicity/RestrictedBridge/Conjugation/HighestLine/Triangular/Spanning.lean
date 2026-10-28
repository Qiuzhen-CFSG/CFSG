module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge.Conjugation.HighestLine.Triangular.Cartan

/-!
# Reordering the quotient root algebra into three blocks

The negative, Cartan and positive blocks require no internal ordering.
Cartan/root commutators allow a Cartan factor to cross a negative word, and a
positive factor to cross a Cartan word. Induction on the negative word then
moves a positive factor across it, provided mixed root commutators are linear
combinations of roots and simple Cartan operators. The generated algebra acts
by left multiplication on the resulting span. Quotient density finishes the
spanning argument.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), §2, structure equations 2.1–2.6 and monomials 2.8;
DOI 10.1017/S0027763000011016.
-/

public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

namespace SimpleCyclicQuotient
open HighestLine
variable {B : AlgebraicFactor F} {v : B.Space} (Q : SimpleCyclicQuotient B v)

/-- The linear span of all root operators and the four simple Cartan brackets. -/
@[expose] def rootCartanSpan : Submodule F (Module.End F Q.Space) :=
  Submodule.span F (Set.range Q.operator ∪ Set.range Q.cartanOperator)

/-- A triangular word belongs to its defining span. -/
theorem triangularWord_mem (l : List NegativeRoot) (h : List (Fin 4))
    (r : List PositiveRoot) : Q.triangularWord l h r ∈ Q.triangularSpan :=
  Submodule.subset_span ⟨l, h, r, rfl⟩

private theorem triangularWord_cons_negative (n : NegativeRoot) (l : List NegativeRoot)
    (h : List (Fin 4)) (r : List PositiveRoot) :
    Q.triangularWord (n :: l) h r = Q.operator n.val * Q.triangularWord l h r := by
  simp only [triangularWord, List.map_cons, List.prod_cons, mul_assoc]

private theorem mul_mem_of_triangularWord (A : Module.End F Q.Space)
    (hA : ∀ l h r, A * Q.triangularWord l h r ∈ Q.triangularSpan)
    {a : Module.End F Q.Space} (ha : a ∈ Q.triangularSpan) :
    A * a ∈ Q.triangularSpan := by
  have hle : Q.triangularSpan ≤ Q.triangularSpan.comap (LinearMap.mulLeft F A) := by
    apply Submodule.span_le.mpr
    rintro a ⟨l, h, r, rfl⟩
    exact hA l h r
  exact hle ha

private theorem negative_mul_mem (n : NegativeRoot) {a : Module.End F Q.Space}
    (ha : a ∈ Q.triangularSpan) : Q.operator n.val * a ∈ Q.triangularSpan := by
  apply Q.mul_mem_of_triangularWord _ _ ha
  intro l h r
  rw [← Q.triangularWord_cons_negative]
  exact Q.triangularWord_mem _ _ _

private theorem swap_mul (A D C : Module.End F Q.Space) :
    (A * D - D * A) * C + D * (A * C) = A * (D * C) := by
  noncomm_ring

private theorem cartan_mul_word_mem (i : Fin 4) (l : List NegativeRoot)
    (h : List (Fin 4)) (r : List PositiveRoot) :
    Q.cartanOperator i * Q.triangularWord l h r ∈ Q.triangularSpan := by
  induction l with
  | nil =>
    simpa only [triangularWord, List.map_nil, List.prod_nil, List.map_cons,
      List.prod_cons, one_mul, mul_assoc] using Q.triangularWord_mem [] (i :: h) r
  | cons n l ih =>
    rw [Q.triangularWord_cons_negative, ← swap_mul, Q.cartan_operator_commutator,
      smul_mul_assoc]
    exact Q.triangularSpan.add_mem
      (Q.triangularSpan.smul_mem _ (Q.negative_mul_mem n (Q.triangularWord_mem l h r)))
      (Q.negative_mul_mem n ih)

private theorem cartan_mul_mem (i : Fin 4) {a : Module.End F Q.Space}
    (ha : a ∈ Q.triangularSpan) : Q.cartanOperator i * a ∈ Q.triangularSpan :=
  Q.mul_mem_of_triangularWord _ (Q.cartan_mul_word_mem i) ha

private theorem positive_cartan_word_mem (h : List (Fin 4)) (r : List PositiveRoot) :
    ∀ p : PositiveRoot, Q.operator p.val * Q.triangularWord [] h r ∈ Q.triangularSpan := by
  induction h with
  | nil =>
    intro p
    simpa only [triangularWord, List.map_nil, List.prod_nil, List.map_cons,
      List.prod_cons, one_mul, mul_one] using Q.triangularWord_mem [] [] (p :: r)
  | cons i h ih =>
    intro p
    have he : Q.triangularWord [] (i :: h) r =
        Q.cartanOperator i * Q.triangularWord [] h r := by
      simp only [triangularWord, List.map_nil, List.prod_nil, List.map_cons,
        List.prod_cons, one_mul, mul_assoc]
    have hc : Q.operator p.val * Q.cartanOperator i -
        Q.cartanOperator i * Q.operator p.val =
        -(typeF4RootPairing.pairingIn ℤ p.val (typeF4SimpleRootIndex i) : F) •
          Q.operator p.val := by
      rw [← neg_sub (Q.cartanOperator i * Q.operator p.val), Q.cartan_operator_commutator,
        neg_smul]
    rw [he, ← swap_mul, hc, smul_mul_assoc]
    exact Q.triangularSpan.add_mem (Q.triangularSpan.smul_mem _ (ih p))
      (Q.cartan_mul_mem i (ih p))

/-- Mixed commutator containment suffices for three-block spanning. The premise
concerns only individual operator brackets, not word spanning or irreducibility. -/
theorem triangularSpan_eq_top_of_mixed_commutators
    (hcomm : ∀ (p : PositiveRoot) (n : NegativeRoot),
      Q.operator p.val * Q.operator n.val - Q.operator n.val * Q.operator p.val ∈
        Q.rootCartanSpan) : Q.triangularSpan = ⊤ := by
  have hpos (l : List NegativeRoot) : ∀ h r (p : PositiveRoot),
      Q.operator p.val * Q.triangularWord l h r ∈ Q.triangularSpan := by
    induction l with
    | nil => exact fun h r p => Q.positive_cartan_word_mem h r p
    | cons n l ih =>
      intro h r p
      have hbracket : (Q.operator p.val * Q.operator n.val -
          Q.operator n.val * Q.operator p.val) * Q.triangularWord l h r ∈
          Q.triangularSpan := by
        have hle : Q.rootCartanSpan ≤ Q.triangularSpan.comap
            (LinearMap.mulRight F (Q.triangularWord l h r)) := by
          apply Submodule.span_le.mpr
          intro a ha
          rcases ha with ⟨s, rfl⟩ | ⟨i, rfl⟩
          · by_cases hs : typeF4RootPairing_base.IsPos s
            · exact ih h r ⟨s, hs⟩
            · exact Q.negative_mul_mem ⟨s, hs⟩ (Q.triangularWord_mem l h r)
          · exact Q.cartan_mul_word_mem i l h r
        exact hle (hcomm p n)
      rw [Q.triangularWord_cons_negative, ← swap_mul]
      exact Q.triangularSpan.add_mem hbracket (Q.negative_mul_mem n (ih h r p))
  have hroot (s : F4Chevalley.Root) : ∀ a ∈ Q.triangularSpan,
      Q.operator s * a ∈ Q.triangularSpan := by
    intro a ha
    by_cases hs : typeF4RootPairing_base.IsPos s
    · exact Q.mul_mem_of_triangularWord _ (fun l h r => hpos l h r ⟨s, hs⟩) ha
    · exact Q.negative_mul_mem ⟨s, hs⟩ ha
  have hstable (A : Module.End F Q.Space) (hA : A ∈ Algebra.adjoin F (Set.range Q.operator)) :
      ∀ a ∈ Q.triangularSpan, A * a ∈ Q.triangularSpan := by
    induction hA using Algebra.adjoin_induction with
    | mem A hA => obtain ⟨s, rfl⟩ := hA; exact hroot s
    | algebraMap c =>
      intro a ha
      simpa only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] using
        Q.triangularSpan.smul_mem c ha
    | add A D hA hD ihA ihD =>
      intro a ha
      simpa only [add_mul] using Q.triangularSpan.add_mem (ihA a ha) (ihD a ha)
    | mul A D hA hD ihA ihD =>
      intro a ha
      simpa only [mul_assoc] using ihA (D * a) (ihD a ha)
  apply top_unique
  intro A _
  have hone : (1 : Module.End F Q.Space) ∈ Q.triangularSpan := by
    simpa only [triangularWord, List.map_nil, List.prod_nil, mul_one] using
      Q.triangularWord_mem [] [] []
  have hA : A ∈ Algebra.adjoin F (Set.range Q.operator) := by
    rw [Q.operator_adjoin_eq_top]
    trivial
  simpa only [mul_one] using hstable A hA 1 hone

end SimpleCyclicQuotient
end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
