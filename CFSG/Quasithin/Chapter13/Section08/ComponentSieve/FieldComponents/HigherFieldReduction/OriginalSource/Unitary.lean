module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.Multiplicity
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.MultiplicitySections
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.Applications

/-!
# Excluding even-degree unitary components in the original source

The original quadratic actor constructs a faithful FF multiplicity module.
Minimal-offender replacement then supplies a genuine irreducible central
section, with the original component identified with its generalized Fitting
subgroup. The corrected native B.4 classification excludes an even-degree
projective unitary component in the external-cubic branch.

In the outer branch the original marked torus calculation applies to the
specified unitary model and forces degree three, contradicting even degree.
The canonical special-to-projective isomorphism handles the full special
unitary row as well. Both exclusions feed the original field catalogue and
apply to every component of an unrestricted original overgroup via the
published reduced context. No FF realization or field-exclusion premise
remains in these even-unitary results.

The remaining external linear and exceptional field branches, binary
exclusion and final field-source assembly stay with qt-d-138-fields-source.
The earlier source context remains with qt-d-1381-source.
Source: Aschbacher–Smith, 13.8.20(a), printed p.954, with B.1.5, B.1.11,
B.4.2 and the literal torus calculation of 13.8.20.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory InvertedCubicTensor
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ExternalModules ExternalModules.FFSections
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K X : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The external even-degree unitary row is impossible: its actual faithful
multiplicity module has an FF offender and an irreducible FF central section,
contrary to the native source classification. -/
theorem source_external_unitary_false
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁)
    (ha : ExternalXAlternative H K X) (hx : ExternalSourceData H K X)
    (hseed : V₃ = ⁅V₃,X⁆)
    {Q : Type*} [Field Q] [Finite Q]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 Q)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (hQ : Nat.card Q = 2 ^ (2*n))
    (hconj : ∀ x, J.conj x = x ^ (2^n))
    (e : Source.starImage H K ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :
    False := by
  let : IsQuasisimple (Source.starImage H K) :=
    (SolvableSource.component_fitting_source c.localSetup c.maximal c.f9
      c.centralizer c.noncentral_core c.earlier1339 c.component.local_overgroup K
      c.component.component).2
  obtain ⟨s,_,_,_,A,_,_,μ,_,hf,hoff,hfit,hS⟩ := source_external_ff_multiplicity c act X ha hx hseed
  have hFF : IsFFModule μ := ⟨A.subgroupOf (Source.starImage H K ⊔ A),hoff⟩
  have hnot := unitary_not_ff_of_generated_fitting
    (V := multiplicitySpace (V := SeedAction.Space H V₃ V₁) (act.representation.comp s)) (Source.starImage H K) A
    μ hf hfit hx.2.2.2.2.1 hS J hn heven hQ hconj e
  exact hnot hFF

/-- Only the two projective linear families remain in the original external
branch; the even-unitary case is discharged without any FF-section premise. -/
theorem source_external_linear_carriers
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁)
    (ha : ExternalXAlternative H K X) (hx : ExternalSourceData H K X)
    (hseed : V₃ = ⁅V₃,X⁆) :
    ∃ n : ℕ, 1 < n ∧
      (ClassicalGroup.IsPSL (Source.starImage H K) 2 (2^n) ∨
        (Odd n ∧ ClassicalGroup.IsPSL (Source.starImage H K) 3 (2^n))) := by
  cases hx.2.2.2.1 with
  | linearTwo n hn h => exact ⟨n,hn,Or.inl h⟩
  | linearThree n hn ho h => exact ⟨n,hn,Or.inr ⟨ho,h⟩⟩
  | unitaryThree n hn he h =>
    obtain ⟨Q,hQf,hQfin,J,hQ,hconj,⟨e⟩⟩ := h
    exact (source_external_unitary_false c act ha hx hseed J (by omega) he
      (by simpa only [pow_mul,Nat.mul_comm] using hQ) hconj e).elim

open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open LocalBorel LocalBorel.CentralizingCalculation TorusModels.Assembly

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
private theorem outer_parameters_for_model {n : ℕ} {unitary four : Bool}
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

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- Any original outer actor forces the parameters of the specified model,
not merely those of an unmarked alternative isomorphic carrier. -/
theorem source_outer_model_parameters
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    {n : ℕ} {unitary four : Bool} (hn : 1 < n)
    (m : Model.{u,0} (Source.starImage H K) n unitary four)
    (t : ((T : Subgroup G) ⊓ L : Subgroup G))
    (ho : OuterStarAction H K
      (QuotientGroup.mk' (pCore 2 H)
        ⟨t.val,c.component.local_overgroup.1.2 (mem_sup_right t.property.1)⟩)) :
    (four = true ∧ n = 2) ∨ (unitary = true ∧ n = 3) := by
  let : (K.subgroupOf H).Normal := c.component.normal
  let : (Source.starImage H K).Normal :=
    c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  let i := sourceInput c hn m
  rcases local_quotient_alternatives c.localSetup with ⟨e,he⟩ | ⟨e,he⟩
  · obtain ⟨a⟩ := LocalFitting.ordinary_natural c.localSetup e he
    let d := i.ordinarySourceContext a
    have hc := d.marked_calculation_ordinary a t
    exact outer_parameters_for_model d t ho hc.2.1 hc.2.2
  · obtain ⟨a⟩ := local_covered_flag_model c.localSetup e he
    have hfactor := CoverFactorization.source_factorization a
    let d := i.coveredSourceContext a hfactor
    have hc := d.marked_calculation_covered a hfactor t
    exact outer_parameters_for_model d t ho hc.2.1 hc.2.2

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- Neither Borel branch admits an even-degree projective unitary component
under the original source assumptions. -/
theorem source_no_even_projective_unitary
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (n : ℕ) (hn : 1 < n) (heven : Even n) :
    ¬ ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 (2^n) := by
  intro hmodel
  have hfield : HigherFieldAlternative (K ⧸ pCore 2 K) :=
    ⟨n,hn,Or.inr (Or.inl ⟨true,Or.inl hmodel⟩)⟩
  obtain ⟨Q,hQf,hQfin,J,hQ,hconj,⟨e⟩⟩ := hmodel
  let : IsElementaryAbelian 2 (Source.UH H V₃) :=
    c.localSetup.uh_elementary c.component.local_overgroup
  let : (Source.starImage H K).Normal :=
    c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  let b := (Components.componentStarEquiv H K hKH c.component.component).symm.trans e
  have hF9 := c.f9 H c.component.local_overgroup
  let act := Comparison.conjugationAction (c.localSetup.line_le_uh H) hF9.plus_le_H
    (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    hF9.commutator_UH_QH_le_point
  obtain ⟨_,_,_,X,t,_,_,hseed,hcases⟩ := source_borel_structure c hfield
  rcases hcases with ⟨ha,_,hx⟩ | ho
  · exact source_external_unitary_false c act ha.1 hx hseed J (by omega) heven
      (by simpa only [pow_mul,Nat.mul_comm] using hQ) hconj b
  · let J' := BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
    have hf : Nat.card {x : Q // J'.conj x = x} = 2^n :=
      FiniteField.card_fixed_of_quadratic_frobenius J'.conj 2 n (by omega) hQ hconj
    let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J') :=
      BenderSuzuki.External.huppert_II_10_13 J' (2^n)
        (by simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) hn) hQ hf
    let m : Model.{u,0} (Source.starImage H K) n true false :=
      .projectiveUnitaryThree Q J hQ hconj b
        (BenderSuzuki.MatrixGroups.HermitianForm.EvenSemilinear.semilinear_coverage
          J' rfl (by omega) hQ hconj)
    have hh := source_outer_model_parameters c hn m t ho.2
    simp only [Bool.false_eq_true,false_and,true_and,false_or] at hh
    subst n
    norm_num at heven

open Chapter1.Section02.LocalModels

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- The canonical special-to-projective map also discharges the full SU row;
its scalar kernel is trivial in even field degree. -/
theorem source_no_even_unitary
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (n : ℕ) (hn : 1 < n) (heven : Even n) :
    ¬ (IsPSLSign (K ⧸ pCore 2 K) true 3 (2^n) ∨
      IsSLSign (K ⧸ pCore 2 K) true 3 (2^n)) := by
  rintro (h | h)
  · exact source_no_even_projective_unitary c n hn heven h
  · obtain ⟨Q,hQf,hQfin,J,hQ,hconj,⟨e⟩⟩ := h
    exact source_no_even_projective_unitary c n hn heven
      ⟨Q,hQf,hQfin,J,hQ,hconj,⟨e.trans
        (BenderSuzuki.MatrixGroups.HermitianForm.EvenProjectiveComparison.specialProjectiveEquiv
          J heven hconj)⟩⟩

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- The original full field catalogue now retains only the exceptional
unitary field of order eight; all even unitary degrees have been excluded. -/
theorem source_higher_field_refined_list
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hfield : HigherFieldAlternative (K ⧸ pCore 2 K)) :
    ∃ n : ℕ, 1 < n ∧
      (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^n) ∨
        ∃ unitary : Bool,
          (IsPSLSign (K ⧸ pCore 2 K) unitary 3 (2^n) ∨
            IsSLSign (K ⧸ pCore 2 K) unitary 3 (2^n)) ∧
          ((unitary = false ∧ (Odd n ∨ n = 2)) ∨
            (unitary = true ∧ n = 3))) := by
  obtain ⟨n,hn,h | ⟨unitary,hm,hp⟩⟩ := source_higher_field_parameter_list c hfield
  · exact ⟨n,hn,Or.inl h⟩
  · refine ⟨n,hn,Or.inr ⟨unitary,hm,?_⟩⟩
    rcases hp with h | ⟨rfl,he | he⟩
    · exact Or.inl h
    · exact (source_no_even_unitary c n hn he hm).elim
    · exact Or.inr ⟨rfl,he⟩

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- Apply the even-unitary exclusion to every original component, without
assuming that the original overgroup is generated by this component. -/
theorem original_no_even_unitary
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9 : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (n : ℕ) (hn : 1 < n) (heven : Even n) :
    ¬ (IsPSLSign (K ⧸ pCore 2 K) true 3 (2^n) ∨
      IsSLSign (K ⧸ pCore 2 K) true 3 (2^n)) := by
  let c := Overgroups.context_of_original d h hF9 hcentral hcomm hH
  exact source_no_even_unitary (Overgroups.reducedContext c K hKH hK) n hn heven

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- The refined full catalogue applies on the intrinsic two-core quotient
of every component in an unrestricted original overgroup. -/
theorem original_higher_field_refined_list
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9 : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hfield : HigherFieldAlternative (K ⧸ pCore 2 K)) :
    ∃ n : ℕ, 1 < n ∧
      (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^n) ∨
        ∃ unitary : Bool,
          (IsPSLSign (K ⧸ pCore 2 K) unitary 3 (2^n) ∨
            IsSLSign (K ⧸ pCore 2 K) unitary 3 (2^n)) ∧
          ((unitary = false ∧ (Odd n ∨ n = 2)) ∨
            (unitary = true ∧ n = 3))) := by
  let c := Overgroups.context_of_original d h hF9 hcentral hcomm hH
  exact source_higher_field_refined_list (Overgroups.reducedContext c K hKH hK) hfield

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
