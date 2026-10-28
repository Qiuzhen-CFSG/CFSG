module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.Linear
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.CartanExclusion

/-!
# Completing the field-four component case

A concrete PSL₂(4) quotient gives n(H) ≤ 2 in both the normal and paired
branches. The original lower bound n(H) ≥ n > 1 forces n(H) = n = 2.
The established Hall/Cartan argument then gives relative normality, so
the component is the actual embedded O²(H), and the full parameter,
model, supplement and escape conclusion follows in this row.

The same argument removes this endpoint from the paired numerical sieve.
The original SL₃/Sp₄ marking and preceding 11.0.4 residual and cubic
clauses remain explicit, with their discharge retained by
qt-d-1222-shadow-linear-geometry. General recognition and the larger
field rows remain with the parameter-component owner; this module
neither relabels an arbitrary model exponent as n(H) nor asserts an
unconditional 11.3.5--6 theorem.
Source: Aschbacher--Smith, 11.3.4--6, printed pp.771--772.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.ChapterB.QuasisimpleSource
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

/-- The binary field-four row is normal relative to the original H.
Its model bound and the original n > 1 force both parameters to be two. -/
theorem ComponentSeed.normal_of_field_four (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ 2))
    (hmark : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∨
      Nonempty (ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))))
    (hres : ∀ r : ℕ, r.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          r ∣ 2 ^ S.field.degree - 1 ∧ 3 < r) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          r ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual r (normalizer (L : Set G)) =
        L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    (K.subgroupOf H).Normal := by
  have hu := s.linear_parameter_le h pr hc hs (by decide) hm
  have hl := degree_le_parameter h pr hc hs
  have hnon := S.nonbinary
  have hk : ChapterE.generationParameter H = 2 := by omega
  have hnfield : ChapterE.generationParameter H = S.field.degree := by omega
  have hm' : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ ChapterE.generationParameter H) :=
    hk.symm ▸ hm
  exact s.normal_of_paired_cartan h pr hc hs hm' (.inl hnfield) hmark hres hcubic

/-- Under the original natural marking and preceding source clauses,
a paired component has field exponent at least three or is Suzuki. -/
theorem ComponentSeed.paired_large_binary_models (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    (hmark : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∨
      Nonempty (ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))))
    (hres : ∀ r : ℕ, r.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          r ∣ 2 ^ S.field.degree - 1 ∧ 3 < r) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          r ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual r (normalizer (L : Set G)) =
        L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    (∃ f : ℕ, 3 ≤ f ∧ ChapterE.generationParameter H ≤ f ∧
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) ∨
    (∃ m : ℕ, 1 ≤ m ∧ ChapterE.generationParameter H ≤ 2 * m + 1 ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) := by
  rcases s.paired_binary_models h pr hc hs hn with ⟨f,hf,hu,hm⟩ | hm
  · have hf3 : 3 ≤ f := by
      by_contra hf3
      have hf2 : f = 2 := by omega
      exact hn (s.normal_of_field_four h pr hc hs (hf2 ▸ hm) hmark hres hcubic)
    exact Or.inl ⟨f,hf3,hu,hm⟩
  · exact Or.inr hm

/-- Complete the parameter and outside-component conclusion in the actual
PSL₂(4) model case. No recognition-at-the-minimum premise is used. -/
theorem ComponentSeed.conclusion_of_field_four (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ 2))
    (hmark : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∨
      Nonempty (ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))))
    (hres : ∀ r : ℕ, r.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          r ∣ 2 ^ S.field.degree - 1 ∧ 3 < r) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          r ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual r (normalizer (L : Set G)) =
        L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    Conclusion S H := by
  have hu := s.linear_parameter_le h pr hc hs (by decide) hm
  have hl := degree_le_parameter h pr hc hs
  have hnon := S.nonbinary
  have hk : ChapterE.generationParameter H = 2 := by omega
  have hnfield : ChapterE.generationParameter H = S.field.degree := by omega
  have hm' : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ ChapterE.generationParameter H) :=
    hk.symm ▸ hm
  have hn := s.normal_of_field_four h pr hc hs hm hmark hres hcubic
  exact assemble h ⟨K,s.component,s.span,hm',fun _ => s.normal_iff_eq_residual.mp hn⟩ hnfield

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
