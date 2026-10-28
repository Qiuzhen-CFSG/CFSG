module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.SourceAlternatives
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.SourceRoot
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.CartanExclusion

/-!
# Source assembly of the recognized rank-one branches

The original marking and earlier s-value supply the source Hall/Cartan
exclusion. Once the selected component is PSL₂ at generationParameter H,
that argument constructs the paired-collapse clause, and the completed
doubled-module contradiction proves k=n. The output is the actual ambient
O²(H), with relative normality, its own quotient, Sylow supplement and escape.

In the normal PSL₂ row, the existing elementary root construction supplies
recognition whenever V escapes O₂(H). This now gives f=n and the full
residual-component conclusion. A matching model exponent also completes
the core case directly from the numerical upper bound. Consequently the
remaining normal-row obstruction has n<f, V≤O₂(H), and the actual
nontrivial core commutator between source conjugates.

The model/FF sieve and that core obstruction remain with this owner.
The exact preceding generation alternative, global-s value and 11.0.4
clauses remain explicit and retain their existing local-geometry producers.
Doubled/Source proves the conditional exclusion used here; its producer
qt-d-1222-shadow-doubled-exclusion still retains unconditional earlier-source
discharge. Final source assembly remains with qt-d-1222-shadow-linear-geometry.
This module does not assert unconditional 11.3.5--6.
Source: Aschbacher--Smith, 11.3.4--7(1), printed pp.771--773.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
open LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H K : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The constructed elementary root lift and the doubled exclusion complete
the original residual-component conclusion whenever V escapes O₂(H). -/
theorem ComponentSeed.conclusion_of_normal_linear_escape
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : (K.subgroupOf H).Normal) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f))
    (hV : ¬ V ≤ H.pCoreIn 2)
    {c : LocalGeometry.Coordinates D S.field} (F : InvariantFlag c)
    (hpoint : c.binarySubspace (F.space 0) = U₁)
    (hgen : WeakClosure.Generation.Conclusion D S H) :
    f = S.field.degree ∧ K = residual H ∧ Conclusion S H := by
  have hr := (s.normal_linear_recognition_or_original_core h pr hc hs hn hf hm).resolve_right hV
  have ho := Doubled.source_parameter_component h pr hc F hpoint hr.2 hgen hs
  exact ⟨hr.1.symm.trans ho.parameter,s.normal_iff_eq_residual.mp hn,ho⟩

/-- A normal component with the original field exponent gives the full
conclusion even when V lies in the core, without Hall or doubled premises. -/
theorem ComponentSeed.conclusion_of_normal_matching_linear
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ S.field.degree)) :
    K = residual H ∧ Conclusion S H := by
  have he := s.normal_iff_eq_residual.mp hn
  have hk := Nat.le_antisymm (s.linear_parameter_le h pr hc hs (by have := S.nonbinary; omega) hm)
    (degree_le_parameter h pr hc hs)
  refine ⟨he,assemble h ⟨K,s.component,s.span,?_,fun _ => he⟩ hk⟩
  rwa [hk]


/-- Recognition at the actual minimum discharges the paired-collapse premise,
then the completed doubled argument gives the original residual component. -/
theorem ComponentSeed.conclusion_of_source_linear_model
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    {c : LocalGeometry.Coordinates D S.field} (F : InvariantFlag c)
    (hpoint : c.binarySubspace (F.space 0) = U₁)
    (hs : @ChapterE.globalS G _ V D.elementary = WeakClosure.Parameters.naturalParameter D S c)
    (hgen : WeakClosure.Generation.Conclusion D S H)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ ChapterE.generationParameter H))
    (hres : ∀ r : ℕ, r.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          r ∣ 2 ^ S.field.degree - 1 ∧ 3 < r) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          r ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual r (normalizer (L : Set G)) =
        L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    K = residual H ∧ Conclusion S H := by
  obtain ⟨hmark,hsn,_⟩ := source_marking_and_parameter h pr hc c hs hgen
  have hs' : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary := hsn.symm.le
  have hr := s.rankOneReduction_of_model h pr hc hs' hm hmark hres hcubic
  have ho := Doubled.source_parameter_component h pr hc F hpoint hr hgen hs'
  exact ⟨s.normal_iff_eq_residual.mp
    (s.normal_of_paired_cartan h pr hc hs' hm (.inl ho.parameter) hmark hres hcubic),ho⟩

/-- The normal PSL₂ row now leaves only a larger-field core obstruction.
The success branch includes the actual O²(H), not just RankOneReduction. -/
theorem ComponentSeed.normal_linear_source_alternative
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : (K.subgroupOf H).Normal) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f))
    {c : LocalGeometry.Coordinates D S.field} (F : InvariantFlag c)
    (hpoint : c.binarySubspace (F.space 0) = U₁)
    (hgen : WeakClosure.Generation.Conclusion D S H) :
    letI := D.elementary
    letI := omegaOrbit_elementary h
    (f = S.field.degree ∧ K = residual H ∧ Conclusion S H) ∨
      (S.field.degree < f ∧ V ≤ H.pCoreIn 2 ∧ ∃ g : G,
        let A := V.map (MulAut.conj g).toMonoidHom
        A ≤ T ∧ g ∉ normalizer (V : Set G) ∧
        actorImage T H A ∈
          ChapterE.fixedSpaceFamily (orbitRepresentation h) (ChapterE.globalS V).toNat ∧
        ∃ x ∈ H ⊓ normalizer (L : Set G), ∃ a ∈ A, ∃ b ∈ A,
          x*b*x⁻¹ ∈ (T : Subgroup G) ∧ ⁅a,x*b*x⁻¹⁆ ≠ 1 ∧
            ⁅a,x*b*x⁻¹⁆ ∈ H.pCoreIn 2) := by
  let := D.elementary
  let := omegaOrbit_elementary h
  by_cases he : f = S.field.degree
  · exact .inl ⟨he,s.conclusion_of_normal_matching_linear h pr hc hs hn (he ▸ hm)⟩
  have hnf : S.field.degree < f := by
    have hl := degree_le_parameter h pr hc hs
    have hu := s.linear_parameter_le h pr hc hs hf hm
    omega
  rcases s.normal_linear_recognition_or_source_commutator h pr hc hs hn hf hm with hr | ho
  · have hc' := Doubled.source_parameter_component h pr hc F hpoint hr.2 hgen hs
    exact (he (hr.1.symm.trans hc'.parameter)).elim
  · exact .inr ⟨hnf,ho⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
