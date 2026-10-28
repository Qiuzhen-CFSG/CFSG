module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.FFOrbit
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.OrbitRankOne

/-!
# Source assembly of the parameter and outside residual component

The normalized 7.0.1 exit is applied to the actual chosen module on the
faithful maximal overcomponent. Its FF branch passes through the complete
containing-model and full-orbit sieve; its orthogonal branch already supplies
a literal PSL₂ quotient. The original ambient exclusion removes the J₄ branch.
The checked Hall-parameter, paired and doubled arguments then yield k=n and
the required component, quotient model, supplement and outside-normalizer
conclusions on the actual embedded O²(H).

The final theorem constructs the component, maximal overcomponent, chosen
module and its source hypotheses. Its 7.0.1 premise is precisely the output
owned by qt-d-1222-normalized-nonff, including the actual multiple-overgroup
hypothesis. That producer is still required. The genuine preceding global-s,
odd-kernel, residual/cubic and Preceding1133 clauses retain their existing
producers and final discharge by qt-d-1222-shadow-linear-geometry. This is a
conditional assembly, not an unconditional proof of the source theorem.

Source: Aschbacher--Smith, 7.0.1 and 11.3.5--6, printed pp.695,771--773.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
open ChapterB.QuasisimpleSource LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H K J : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- Both the FF and orthogonal exits of original 7.0.1 identify the actual
seed quotient as PSL₂. The ambient J₄ exit is excluded by the source hypotheses. -/
theorem ComponentSeed.linear_of_overcomponent_source_exit
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : (K.subgroupOf H).Normal)
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    {W : Subgroup G} (E : Chapter12.Section02.ChosenModule T J W)
    (hsrc : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J)
    (hexit : Chapter7.NormalizedSource.Alternatives G E.orbitRepresentation E.orbitComponent) :
    ∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f) := by
  rcases hexit with hff | ⟨n,hn',⟨M⟩⟩ | hj
  · exact s.linear_of_overcomponent_orbit_ff h pr hc hs hn hJ hKJ E hsrc hff
  · let : NeZero n := ⟨by omega⟩
    have hm := E.orbit_orthogonal_actor hsrc.toHypothesis1221 hn' M
    exact ⟨2*n,by omega,s.linear_model_of_overcomponent h hJ.1 hKJ (by omega) hm⟩
  · exact (S.source.no_J4 hj).elim

/-- The original source exit feeds all paired, model and doubled exclusions,
yielding k=n and the literal outside residual component. Only the named earlier
source clauses and the 7.0.1 exit remain inputs. -/
theorem ComponentSeed.conclusion_of_overcomponent_source_exit
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    {c : LocalGeometry.Coordinates D S.field} (F : InvariantFlag c)
    (hpoint : c.binarySubspace (F.space 0) = U₁)
    (hs : @ChapterE.globalS G _ V D.elementary = WeakClosure.Parameters.naturalParameter D S c)
    (hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    {W : Subgroup G} (E : Chapter12.Section02.ChosenModule T J W)
    (hsrc : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J)
    (hexit : Chapter7.NormalizedSource.Alternatives G E.orbitRepresentation E.orbitComponent)
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
  have hn := s.normal_of_source_odd_kernel h pr hc F hpoint hs hcontrol hres hcubic
  have hgen := WeakClosure.Generation.Doubling.conclusion_of_automizer_bounds D S
    hcontrol (WeakClosure.Generation.Automizer.automizerBounds D S) h.outside
  have hs' := (source_marking_and_parameter h pr hc c hs hgen).2.1.symm.le
  obtain ⟨f,hf,hm⟩ := s.linear_of_overcomponent_source_exit h pr hc hs' hn hJ hKJ E hsrc hexit
  exact (s.conclusion_of_linear_odd_kernel h pr hc F hpoint hs hcontrol hf hm hres hcubic).2

/-- Choose the original component and its faithful maximal overcomponent,
construct the chosen module and apply the complete model/FF sieve. This is
conditional on genuine 7.0.1 for the same ambient group and source choices;
no component recognition or rank-two exclusion is an extra premise. -/
theorem conclusion_of_normalized_source
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    {c : LocalGeometry.Coordinates D S.field} (F : InvariantFlag c)
    (hpoint : c.binarySubspace (F.space 0) = U₁)
    (hs : @ChapterE.globalS G _ V D.elementary = WeakClosure.Parameters.naturalParameter D S c)
    (hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))
    (h701 : ∀ (J W : Subgroup G) (E : Chapter12.Section02.ChosenModule T J W),
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J →
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter7.NormalizedSource.Alternatives G E.orbitRepresentation E.orbitComponent)
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
  have hgen := WeakClosure.Generation.Doubling.conclusion_of_automizer_bounds D S
    hcontrol (WeakClosure.Generation.Automizer.automizerBounds D S) h.outside
  have hs' := (source_marking_and_parameter h pr hc c hs hgen).2.1.symm.le
  obtain ⟨K,J,s,hKJ,hJ,_,_,_,hcases⟩ :=
    exists_componentSeed_with_quasisimple_higher_rank_source h pr hc hs'
  have hn := s.normal_of_source_odd_kernel h pr hc F hpoint hs hcontrol hres hcubic
  have from_source (hsrc : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J) :
      Conclusion S H := by
    obtain ⟨W,⟨E⟩⟩ := s.exists_chosen_overcomponent_of_normal h hn hJ.1 hKJ
    exact (s.conclusion_of_overcomponent_source_exit h pr hc F hpoint hs hcontrol
      hJ hKJ E hsrc (h701 J W E hsrc S.many) hres hcubic).2
  rcases hcases with ⟨hlow,_⟩ | ⟨_,_,_,hsrc,_⟩
  · rcases hlow with ⟨f,hf,_,hm⟩ | ⟨hsrc,_⟩
    · exact (s.conclusion_of_linear_odd_kernel h pr hc F hpoint hs hcontrol hf hm hres hcubic).2.2
    · exact from_source hsrc
  · exact from_source hsrc

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
