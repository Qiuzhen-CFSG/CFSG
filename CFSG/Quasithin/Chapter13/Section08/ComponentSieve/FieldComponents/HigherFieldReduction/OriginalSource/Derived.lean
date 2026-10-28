module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.External

/-!
# Derived-carrier exclusions and signed field parameters

Keep the actual torus model and its field parameters in the original Borel
argument. An inner marked actor gives an external cubic, hence three-rank at
most one in K. An outer actor forces the same model to have the exceptional
linear or unitary parameters. The derived Sp₄ and G₂ models have neither
exceptional parameter flag, and their concrete rank-two witnesses contradict
the external bound. They are therefore excluded outright for n > 1.

The signed degree-three rank witnesses likewise force n=2 in even linear
degree and n=3 in odd unitary degree. The final source application retains
all remaining projective and special models and their exact parity bounds.
The external representation and exceptional-field contradictions, and the
whole-quotient binary exclusion, remain with qt-d-138-fields-source.
Source: Aschbacher–Smith, 13.8.20, printed pp.954–955 (1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open LocalBorel LocalBorel.CentralizingCalculation
open ExternalModules TorusModels.Assembly
open Chapter1.Section02.LocalModels Components.Models
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

private theorem outer_parameters {n : ℕ} {unitary four : Bool}
    [(Source.starImage H K).Normal]
    (d : LocalBorel.CentralizingCalculation.SourceContext.{u,0}
      T H K L V V₁ V₂ V₃ M G₁ n unitary four)
    (t : ((T : Subgroup G) ⊓ L : Subgroup G))
    (ho : OuterStarAction H K (QuotientGroup.mk' (pCore 2 H) (d.actorElement t)))
    (hfix : FixesTorus (residualAt (sourceSylow H K (T : Subgroup G) d.sylow_H))
      (markedActor H K (T : Subgroup G) (d.actorElement t) t.property.1))
    (hsmall : commutatorOrder (residualAt (sourceSylow H K (T : Subgroup G) d.sylow_H))
      (markedActor H K (T : Subgroup G) (d.actorElement t) t.property.1) ≤ 3) :
    (four = true ∧ n = 2) ∨ (unitary = true ∧ n = 3) := by
  apply d.model.small_outer_fixer_exception d.degree
    (sourceSylow H K (T : Subgroup G) d.sylow_H)
    (starActor H K (T : Subgroup G)).range
    (starActor_twoGroup H K (T : Subgroup G) d.sylow_H)
    (starActor_innerSylow H K (T : Subgroup G) d.sylow_H)
    (fun a ha => ?_)
    (markedActor H K (T : Subgroup G) (d.actorElement t) t.property.1)
    ⟨⟨QuotientGroup.mk' (pCore 2 H) (d.actorElement t),
      ⟨d.actorElement t,t.property.1,rfl⟩⟩,rfl⟩
    ((markedActor_outer_iff H K (T : Subgroup G) (d.actorElement t) t.property.1).mpr ho)
    hfix hsmall
  obtain ⟨s,rfl⟩ := ha
  exact starActor_stable H K (T : Subgroup G) d.sylow_H s

/-- On the actual specified model, either the external cubic consumes one
three-rank, or the prescribed outer actor forces exactly the exceptional
field parameters. The model's parameters and both marking flags are retained. -/
theorem source_model_rank_reduction
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    {n : ℕ} {unitary four : Bool} (hn : 1 < n)
    (m : Model.{u,0} (Source.starImage H K) n unitary four) :
    primeRank 3 K ≤ 1 ∨ (four = true ∧ n = 2) ∨ (unitary = true ∧ n = 3) := by
  let : (K.subgroupOf H).Normal := c.component.normal
  let : (Source.starImage H K).Normal :=
    c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  let i := sourceInput c hn m
  rcases local_quotient_alternatives c.localSetup with ⟨e,he⟩ | ⟨e,he⟩
  · obtain ⟨a⟩ := LocalFitting.ordinary_natural c.localSetup e he
    let d := i.ordinarySourceContext a
    obtain ⟨_,t,_,hb⟩ := i.sylowBorelAlternative_ordinary a
    rcases hb with hx | ho
    · exact Or.inl (Structure.external_cubic_rank KnownSimple.IsKnownSimple
        H K (one L T V₁) (source_sqtk c) i.component_le c.component.component
        (residual_isPPerfect _)
        (AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource.source_residual_quotient_card
          a (one L T V₁) rfl) hx.1).2.2.2
    · have hc := d.marked_calculation_ordinary a t
      exact Or.inr (outer_parameters d t ho.2 hc.2.1 hc.2.2)
  · obtain ⟨a⟩ := local_covered_flag_model c.localSetup e he
    have hfactor := CoverFactorization.source_factorization a
    let d := i.coveredSourceContext a hfactor
    obtain ⟨_,t,_,_,hb⟩ := i.sylowBorelAlternative_covered a hfactor
    rcases hb with hx | ho
    · exact Or.inl (Structure.external_cubic_rank KnownSimple.IsKnownSimple
        H K (plus L T V₁) (source_sqtk c) i.component_le c.component.component
        (residual_isPPerfect _) (a.plus_core_card hfactor) hx.1).2.2.2
    · have hc := d.marked_calculation_covered a hfactor t
      exact Or.inr (outer_parameters d t ho.2 hc.2.1 hc.2.2)

/-- The higher-field derived symplectic and G₂ rows are impossible in the
original source configuration. Their actual derived groups have three-rank
at least two, while neither torus model admits the exceptional outer case. -/
theorem source_no_higher_derived
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (n : ℕ) (hn : 1 < n) :
    ¬ (IsSp4DerivedAt (K ⧸ pCore 2 K) (2^n) ∨
      IsG2DerivedAt (K ⧸ pCore 2 K) (2^n)) := by
  intro h
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  let q := (Components.componentStarEquiv H K hKH c.component.component).symm
  have hr : primeRank 3 (K ⧸ pCore 2 K) ≤ primeRank 3 K :=
    primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup
  rcases h with h | h
  · obtain ⟨F,hF,hfin,hc,⟨e⟩⟩ := h
    let := hF
    let := hfin
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hc)
    have hl := Structure.ModelReduction.derivedRanks.symplectic F n hn hc
    rw [← primeRank_equiv 3 e] at hl
    have hgt : 2 < Nat.card F := by
      rw [hc]
      simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) hn
    let m : Model.{u,0} (Source.starImage H K) n false false :=
      .symplecticFour F hc
        (q.trans (e.trans
          (Theory.SpecificGroups.SymplecticFour.derivedEquivFull_of_card_gt_two hgt)))
        Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram
    have hred := source_model_rank_reduction c hn m
    simp only [Bool.false_eq_true,false_and,or_false] at hred
    omega
  · obtain ⟨F,hF,hfin,hc,⟨e⟩⟩ := h
    let := hF
    let := hfin
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hc)
    have hl := Structure.ModelReduction.derivedRanks.g2 F n hn hc
    rw [← primeRank_equiv 3 e] at hl
    have hgt : 2 < Nat.card F := by
      rw [hc]
      simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) hn
    let m : Model.{u,0} (Source.starImage H K) n false false :=
      .g2 F hc (q.trans (e.trans (Atlas.G2.DerivedEvenOrder.derivedEquivModel hn hc)))
        (Atlas.G2.LieAutomorphismExtensions.semilinearAction_bijective hgt).2
    have hred := source_model_rank_reduction c hn m
    simp only [Bool.false_eq_true,false_and,or_false] at hred
    omega

/-- The signed degree-three rows of three-rank at least two have only the
exceptional field size: linear degree two or unitary degree three. -/
theorem source_signed_three_parameters
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (unitary : Bool) (n : ℕ) (hn : 1 < n)
    (hm : (2^n)%3 = if unitary then 2 else 1)
    (h : IsPSLSign (K ⧸ pCore 2 K) unitary 3 (2^n) ∨
      IsSLSign (K ⧸ pCore 2 K) unitary 3 (2^n)) :
    n = if unitary then 3 else 2 := by
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  let q := (Components.componentStarEquiv H K hKH c.component.component).symm
  have hr : primeRank 3 (K ⧸ pCore 2 K) ≤ primeRank 3 K :=
    primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup
  have hp := Nat.BinaryTorusParity.two_pow_mod_three n
  cases unitary with
  | false =>
    have hpar : Even n := by
      simp only [Bool.false_eq_true,if_false] at hm
      rw [Nat.even_iff]
      split_ifs at hp <;> omega
    rcases h with h | h
    · obtain ⟨F,hF,hfin,hc,⟨e⟩⟩ := h
      let := hF
      let := hfin
      let : Fintype F := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow
        (by simpa only [Nat.card_eq_fintype_card] using hc)
      have hl := Structure.ModelReduction.signedThreeRanks.linear_projective F n hn hc hpar
      rw [← primeRank_equiv 3 e] at hl
      let m : Model.{u,0} (Source.starImage H K) n false true :=
        .projectiveLinearThree F hc (q.trans e)
          (Matrix.PSL3.OuterSolvable.standard_eq_top_of_two_power_card F (by omega) hc)
      have hred := source_model_rank_reduction c hn m
      simp only [Bool.false_eq_true,true_and,false_and,or_false,if_false] at hred ⊢
      omega
    · obtain ⟨F,hF,hfin,hc,⟨e⟩⟩ := h
      let := hF
      let := hfin
      let : Fintype F := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow
        (by simpa only [Nat.card_eq_fintype_card] using hc)
      have hl := Structure.ModelReduction.signedThreeRanks.linear_special F n hn hc hpar
      rw [← primeRank_equiv 3 e] at hl
      let m : Model.{u,0} (Source.starImage H K) n false true :=
        .specialLinearThree F hc (q.trans e)
          (Matrix.PSL3.OuterSolvable.standard_eq_top_of_two_power_card F (by omega) hc)
      have hred := source_model_rank_reduction c hn m
      simp only [Bool.false_eq_true,true_and,false_and,or_false,if_false] at hred ⊢
      omega
  | true =>
    have hpar : Odd n := by
      simp only [if_true] at hm
      rw [Nat.odd_iff]
      split_ifs at hp <;> omega
    rcases h with h | h
    · obtain ⟨F,hF,hfin,J,hc,hconj,⟨e⟩⟩ := h
      let := hF
      let := hfin
      let J' := BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
      have hf : Nat.card {x : F // J'.conj x = x} = 2^n :=
        FiniteField.card_fixed_of_quadratic_frobenius J'.conj 2 n (by omega) hc hconj
      let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J') :=
        BenderSuzuki.External.huppert_II_10_13 J' (2^n)
          (by simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) hn) hc hf
      have hl := Structure.ModelReduction.signedThreeRanks.unitary_projective F J n hn hc hconj hpar
      rw [← primeRank_equiv 3 e] at hl
      let m : Model.{u,0} (Source.starImage H K) n true false :=
        .projectiveUnitaryThree F J hc hconj (q.trans e)
          (BenderSuzuki.MatrixGroups.HermitianForm.EvenSemilinear.semilinear_coverage
            J' rfl (by omega) hc hconj)
      have hred := source_model_rank_reduction c hn m
      simp only [Bool.false_eq_true,true_and,false_and,false_or,if_true] at hred ⊢
      omega
    · obtain ⟨F,hF,hfin,J,hc,hconj,⟨e⟩⟩ := h
      let := hF
      let := hfin
      have hl := Structure.ModelReduction.signedThreeRanks.unitary_special F J n hn hc hconj hpar
      rw [← primeRank_equiv 3 e] at hl
      let J' := BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
      let m : Model.{u,0} (Source.starImage H K) n true false :=
        .specialUnitaryThree F J hc hconj (q.trans e)
          (BenderSuzuki.MatrixGroups.HermitianForm.EvenSemilinear.special_semilinear_coverage
            J' rfl (by omega) hc hconj)
      have hred := source_model_rank_reduction c hn m
      simp only [Bool.false_eq_true,true_and,false_and,false_or,if_true] at hred ⊢
      omega

/-- Apply both derived-row exclusions to the literal higher-field sieve. -/
theorem source_higher_field_signed_models
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hfield : HigherFieldAlternative (K ⧸ pCore 2 K)) :
    ∃ n : ℕ, 1 < n ∧
      (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^n) ∨
        ∃ unitary : Bool, IsPSLSign (K ⧸ pCore 2 K) unitary 3 (2^n) ∨
          IsSLSign (K ⧸ pCore 2 K) unitary 3 (2^n)) := by
  obtain ⟨n,hn,h⟩ := hfield
  refine ⟨n,hn,?_⟩
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (source_no_higher_derived c n hn h).elim

/-- The surviving signed rows have the source parities or the exceptional
field size. This applies the rank reduction to both projective and special
models, retaining the literal two-core quotient. -/
theorem source_higher_field_parameter_list
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hfield : HigherFieldAlternative (K ⧸ pCore 2 K)) :
    ∃ n : ℕ, 1 < n ∧
      (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^n) ∨
        ∃ unitary : Bool,
          (IsPSLSign (K ⧸ pCore 2 K) unitary 3 (2^n) ∨
            IsSLSign (K ⧸ pCore 2 K) unitary 3 (2^n)) ∧
          ((unitary = false ∧ (Odd n ∨ n = 2)) ∨
            (unitary = true ∧ (Even n ∨ n = 3)))) := by
  obtain ⟨n,hn,h⟩ := source_higher_field_signed_models c hfield
  refine ⟨n,hn,?_⟩
  rcases h with h | ⟨unitary,h⟩
  · exact Or.inl h
  · refine Or.inr ⟨unitary,h,?_⟩
    have hp := Nat.BinaryTorusParity.two_pow_mod_three n
    cases unitary with
    | false =>
      refine Or.inl ⟨rfl,?_⟩
      rcases Nat.even_or_odd n with he | ho
      · exact Or.inr (source_signed_three_parameters c false n hn
          (by simpa [Nat.even_iff.mp he] using hp) h)
      · exact Or.inl ho
    | true =>
      refine Or.inr ⟨rfl,?_⟩
      rcases Nat.even_or_odd n with he | ho
      · exact Or.inl he
      · exact Or.inr (source_signed_three_parameters c true n hn
          (by simpa [Nat.odd_iff.mp ho] using hp) h)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
