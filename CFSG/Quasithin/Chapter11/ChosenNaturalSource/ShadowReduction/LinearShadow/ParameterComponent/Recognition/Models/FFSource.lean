module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.FFContaining
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.FFOrders
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.OvercomponentG2

/-!
# The complete containing-model comparison on the original source component

The corrected full-normalizer FF shortlist and the literal component embedding
exclude every Suzuki and unitary source row. Root orders exclude the finite
exceptional containers through the original star projection, preserving its
whole kernel. The remaining split containers force either a binary PSL₂ seed
or equality with the original seed and an actual natural SL₃/Sp₄ marking.

The original normal-source catalogue supplies every simplicity and quotient
premise. Under the genuine preceding odd-kernel and residual clauses, the last
theorem identifies the seed with the embedded O²(H) and completes the parameter
and outside-component conclusion in the PSL₂ branch. The rank-two orbit exclusion
and source existence of FF remain obligations: FF on one chosen constituent
does not assert FF on its full Sylow orbit.

Source: Aschbacher--Smith, A.3.12, B.5.1 and 11.3.5, printed pp.771--772.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H K J : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

private theorem split_model {W : Subgroup G} (E : Chapter12.Section02.ChosenModule T J W)
    {F : BinaryField} (hm :
      Nonempty (ActionEquiv E.centralQuotientAction (linearNatural F 3)) ∨
      Nonempty (ActionEquiv E.centralQuotientAction (binarySymplectic F))) :
    Source.IsSL (J ⧸ pCore 2 J) 3 (2 ^ F.degree) ∨
      ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 (2 ^ F.degree) ∨
      ClassicalGroup.IsPSp (J ⧸ pCore 2 J) 2 (2 ^ F.degree) ∨
      ClassificationModels.IsG2At (J ⧸ pCore 2 J) (2 ^ F.degree) := by
  rcases hm with e | e
  · exact .inl ⟨F.Carrier,inferInstance,inferInstance,F.card_eq,⟨e.some.groupEquiv⟩⟩
  · exact .inr (.inr (.inl ⟨F.Carrier,inferInstance,inferInstance,F.card_eq,
      ⟨e.some.groupEquiv.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F.Carrier))⟩⟩))

/-- The full containing-model sieve leaves a binary PSL₂ seed, or equality
with a rank-two container carrying the actual natural central-quotient action. -/
theorem ComponentSeed.linear_or_equal_natural_of_ff_sixtyFour
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    {W : Subgroup G} (E : Chapter12.Section02.ChosenModule T J W)
    (hsrc : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T J)
    (hff : IsFFModule (normalizerRepresentation E.chosenAction))
    (h64 : 64 ∣ Nat.card (K ⧸ pCore 2 K)) :
    (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) ∨
      (K = J ∧ ∃ F : BinaryField, 1 < F.degree ∧
        (Nonempty (ActionEquiv E.centralQuotientAction (linearNatural F 3)) ∨
          Nonempty (ActionEquiv E.centralQuotientAction (binarySymplectic F)))) := by
  rcases Models.chosen_ff_containing_models E hsrc hff with
    ⟨f,hf,hm⟩ | ⟨F,hF,hm⟩ | ⟨d,hd,hm⟩ | hsmall
  · exact .inl ⟨f,hf,s.linear_model_of_overcomponent h hJ.1 hKJ hf hm⟩
  · have hr (hm : Nonempty (ActionEquiv E.centralQuotientAction (linearNatural F 3)) ∨
        Nonempty (ActionEquiv E.centralQuotientAction (binarySymplectic F))) :
        (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) ∨
          (K = J ∧ ∃ F : BinaryField, 1 < F.degree ∧
            (Nonempty (ActionEquiv E.centralQuotientAction (linearNatural F 3)) ∨
              Nonempty (ActionEquiv E.centralQuotientAction (binarySymplectic F)))) := by
      by_cases he : K = J
      · exact Or.inr ⟨he,F,hF,hm⟩
      · exact Or.inl ⟨F.degree,by omega,
          s.linear_model_of_proper_split_overcomponent h hJ.1
            (lt_of_le_of_ne hKJ he) (by omega) (split_model E hm)⟩
    cases hm with
    | sl3 e => exact hr (.inl e)
    | sp4 e => exact hr (.inr e)
    | g2 e =>
      obtain ⟨a⟩ := e
      exact .inl ⟨F.degree,by omega,(s.linear_model_of_g2_overcomponent h pr hc hs hJ.1 hKJ
        (by omega) ⟨F.Carrier,inferInstance,inferInstance,F.card_eq,⟨a.groupEquiv⟩⟩).2⟩
  · exact (s.not_small_binary_linear_overcomponent h pr hc hs hJ.1 hKJ hd hm).elim
  · exact (hsmall (h64.trans (Models.quotient_order_dvd_of_le hKJ))).elim

/-- No Suzuki source seed admits an FF chosen module on any maximal local
overcomponent. The containing-model hypothesis has been discharged. -/
theorem ComponentSeed.suzuki_overcomponent_no_ff
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    {W : Subgroup G} (E : Chapter12.Section02.ChosenModule T J W)
    {m : ℕ} (hm : 1 ≤ m)
    (em : Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    ¬ IsFFModule (normalizerRepresentation E.chosenAction) := by
  intro hff
  have hsrc := (s.overcomponent_source_of_suzuki h hJ hKJ hm em).toHypothesis1221
  rcases s.linear_or_equal_natural_of_ff_sixtyFour h pr hc hs hJ hKJ E hsrc hff
      (Models.sixtyFour_dvd_suzuki hm em.some) with ⟨f,hf,hl⟩ | ⟨_,F,hF,ha⟩
  · exact s.not_linear_overcomponent_of_suzuki h (s.mem_local_family h) le_rfl hm em f hf hl
  · exact s.not_split_overcomponent_of_suzuki h hJ.1 hKJ hm em (by omega) (split_model E ha)

/-- The order calculation crosses the original star projection and both
literal two-core quotients; the full covering kernel remains intact. -/
theorem ComponentSeed.sixtyFour_dvd_of_higher_rank_image
    (s : ComponentSeed T H K) (R : Subgroup H) [R.Normal] (hR : pCore 2 H ≤ R)
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU ((K.subgroupOf H).map (QuotientGroup.mk' R)) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSL ((K.subgroupOf H).map (QuotientGroup.mk' R)) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSp ((K.subgroupOf H).map (QuotientGroup.mk' R)) 2 (2 ^ n)) :
    64 ∣ Nat.card (K ⧸ pCore 2 K) := by
  have hd := (Models.sixtyFour_dvd_higher_rank hn hm).trans
    (card_dvd_of_surjective (Models.starProjection (K.subgroupOf H) R s.component.2 hR)
      (Models.starProjection_surjective (K.subgroupOf H) R s.component.2 hR))
  rwa [Nat.card_congr s.intrinsicQuotientEquiv.symm.toEquiv] at hd

/-- The unitary source star image excludes FF on every containing chosen
module, with no Bender, split or small-model premise on the container. -/
theorem ComponentSeed.unitary_image_overcomponent_no_ff
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hnorm : (K.subgroupOf H).Normal)
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    {W : Subgroup G} (E : Chapter12.Section02.ChosenModule T J W)
    (R : Subgroup H) [R.Normal] (hR : pCore 2 H ≤ R)
    [IsSimpleGroup ((K.subgroupOf H).map (QuotientGroup.mk' R))]
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU ((K.subgroupOf H).map (QuotientGroup.mk' R)) 3 (2 ^ n)) :
    ¬ IsFFModule (normalizerRepresentation E.chosenAction) := by
  intro hff
  have hsrc := (s.chosen_overcomponent_of_unitary_image h hnorm hJ hKJ R hn hm).1.toHypothesis1221
  rcases s.linear_or_equal_natural_of_ff_sixtyFour h pr hc hs hJ hKJ E hsrc hff
      (s.sixtyFour_dvd_of_higher_rank_image R hR hn (.inl hm)) with ⟨f,hf,hl⟩ | ⟨_,F,hF,ha⟩
  · exact s.not_linear_overcomponent_of_higher_rank_image h (s.mem_local_family h) le_rfl
      R hR hn (.inl hm) f hf hl
  · exact s.not_split_overcomponent_of_unitary_image h hJ.1 hKJ R hR hn hm (by omega)
      (split_model E ha)

/-- In the rank-two source rows the entire embedding/FF comparison forces
non-enlargement and a natural marking of the unchanged chosen central quotient. -/
theorem ComponentSeed.higher_rank_image_ff_forces_natural_equal
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hnorm : (K.subgroupOf H).Normal)
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    {W : Subgroup G} (E : Chapter12.Section02.ChosenModule T J W)
    (hff : IsFFModule (normalizerRepresentation E.chosenAction))
    (R : Subgroup H) [R.Normal] (hR : pCore 2 H ≤ R)
    [Nontrivial ((K.subgroupOf H).map (QuotientGroup.mk' R))]
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL ((K.subgroupOf H).map (QuotientGroup.mk' R)) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSp ((K.subgroupOf H).map (QuotientGroup.mk' R)) 2 (2 ^ n)) :
    K = J ∧ ∃ F : BinaryField, 1 < F.degree ∧
      (Nonempty (ActionEquiv E.centralQuotientAction (linearNatural F 3)) ∨
        Nonempty (ActionEquiv E.centralQuotientAction (binarySymplectic F))) := by
  have hsrc : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T J := by
    rcases hm with hl | hsp
    · exact (s.chosen_overcomponent_of_linear_image h hnorm hJ hKJ R hn hl).1.toHypothesis1221
    · exact (s.chosen_overcomponent_of_symplectic_image h hnorm hJ hKJ R hsp).1.toHypothesis1221
  rcases s.linear_or_equal_natural_of_ff_sixtyFour h pr hc hs hJ hKJ E hsrc hff
      (s.sixtyFour_dvd_of_higher_rank_image R hR hn (.inr hm)) with ⟨f,hf,hl⟩ | hn
  · exact (s.not_linear_overcomponent_of_higher_rank_image h (s.mem_local_family h) le_rfl
      R hR hn (.inr hm) f hf hl).elim
  · exact hn

/-- Apply the full sieve to the actual normal-source catalogue. Only PSL₂
or the unchanged natural SL₃/Sp₄ choice on K=J survives. -/
theorem ComponentSeed.normal_source_models_of_overcomponent_ff
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hnorm : (K.subgroupOf H).Normal)
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    {W : Subgroup G} (E : Chapter12.Section02.ChosenModule T J W)
    (hff : IsFFModule (normalizerRepresentation E.chosenAction)) :
    (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) ∨
      (K = J ∧ ∃ F : BinaryField, 1 < F.degree ∧
        (Nonempty (ActionEquiv E.centralQuotientAction (linearNatural F 3)) ∨
          Nonempty (ActionEquiv E.centralQuotientAction (binarySymplectic F)))) := by
  rcases s.normal_binary_literal_models h pr hc hs hnorm with
    ⟨f,hf,_,hl,_⟩ | ⟨m,hm,_,em,_⟩ | ⟨n,hn,_,hm⟩
  · exact .inl ⟨f,hf,hl⟩
  · exact (s.suzuki_overcomponent_no_ff h pr hc hs hJ hKJ E hm em hff).elim
  · let P := T.subtype h.outside.1.1.2
    let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
    let R := ChapterB.minimalParabolicCore P hP
    let : IsSimpleGroup ((K.subgroupOf H).map (QuotientGroup.mk' R)) :=
      (ChapterE.Structure.source_component_simple_image P hP
        (counterexample_not_solvable h pr hc hs) (K.subgroupOf H) s.component.2
        (s.intrinsic_supplement h.outside.1.1.2)).1
    have hR : pCore 2 H ≤ R := ChapterB.minimalParabolicTwoCore_le_core P hP
    rcases hm with hu | hr
    · exact (s.unitary_image_overcomponent_no_ff h pr hc hs hnorm hJ hKJ E R hR hn hu hff).elim
    · exact .inr (s.higher_rank_image_ff_forces_natural_equal h pr hc hs hnorm hJ hKJ E hff R hR hn hr)

open LocalGeometry in
/-- Original parameter/component assembly after the complete FF containing
sieve. The only remaining FF branch is the literal natural rank-two seed,
which equals both its maximal container and the embedded O²(H). -/
theorem ComponentSeed.conclusion_or_natural_residual_of_overcomponent_ff
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    {c : LocalGeometry.Coordinates D S.field} (F : InvariantFlag c)
    (hpoint : c.binarySubspace (F.space 0) = U₁)
    (hs : @ChapterE.globalS G _ V D.elementary = WeakClosure.Parameters.naturalParameter D S c)
    (hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    {W : Subgroup G} (E : Chapter12.Section02.ChosenModule T J W)
    (hff : IsFFModule (normalizerRepresentation E.chosenAction))
    (hres : ∀ r : ℕ, r.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          r ∣ 2 ^ S.field.degree - 1 ∧ 3 < r) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          r ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual r (normalizer (L : Set G)) =
        L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    K = residual H ∧ (Conclusion S H ∨
      (J = residual H ∧ ∃ Efield : BinaryField, 1 < Efield.degree ∧
        (Nonempty (ActionEquiv E.centralQuotientAction (linearNatural Efield 3)) ∨
          Nonempty (ActionEquiv E.centralQuotientAction (binarySymplectic Efield))))) := by
  have hn := s.normal_of_source_odd_kernel h pr hc F hpoint hs hcontrol hres hcubic
  have hgen := WeakClosure.Generation.Doubling.conclusion_of_automizer_bounds D S
    hcontrol (WeakClosure.Generation.Automizer.automizerBounds D S) h.outside
  have hsn := (source_marking_and_parameter h pr hc c hs hgen).2.1
  have hs' : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary := hsn.symm.le
  refine ⟨s.normal_iff_eq_residual.mp hn,?_⟩
  rcases s.normal_source_models_of_overcomponent_ff h pr hc hs' hn hJ hKJ E hff with
    ⟨f,hf,hm⟩ | ⟨he,Ef,hEf,ha⟩
  · exact .inl (s.conclusion_of_linear_odd_kernel h pr hc F hpoint hs hcontrol hf hm hres hcubic).2.2
  · exact .inr ⟨he.symm.trans (s.normal_iff_eq_residual.mp hn),Ef,hEf,ha⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
