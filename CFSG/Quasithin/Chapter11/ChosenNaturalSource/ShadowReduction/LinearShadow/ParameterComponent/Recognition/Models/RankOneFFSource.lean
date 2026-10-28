module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.RankOneFF
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.Suzuki

/-!
# The original Bender overcomponent under the FF input

The actual embedding of a seed into a Bender overcomponent forces equality.
The full-normalizer FF witness on a chosen module then excludes Suzuki and
unitary-three, leaving a literal binary PSL₂ quotient of that same seed.
The source application feeds this marking into the checked Hall-parameter,
paired-exclusion and doubled-parameter arguments, producing the required
normal residual component and its outside-normalizer conclusion.

The FF witness and the Bender containing-model restriction remain explicit:
this handles their genuine source branch, not the whole embedding list or
Theorem 7.0.1. The other containing models and the rank-two exclusions remain
with this task. The original odd-kernel, global-s, residual and cubic clauses
retain their earlier-source producers and final linear-geometry discharge.
Source: Aschbacher--Smith, 11.3.5--6, printed pp.771--773, using A.3.12,
B.5.1 and 7.0.1.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
open LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H K J : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- FF on the original chosen space excludes the nonlinear Bender rows,
retaining the literal seed quotient and the containing field exponent. -/
theorem ComponentSeed.linear_model_of_bender_overcomponent_ff
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    {W : Subgroup G} (E : Chapter12.Section02.ChosenModule T J W)
    (hff : IsFFModule (normalizerRepresentation E.chosenAction))
    (hb : ClassificationModels.IsBenderModel (J ⧸ pCore 2 J)) :
    K = J ∧ ∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f) := by
  have he := s.eq_overcomponent_of_bender_twoCore h hJ.1 hKJ hb
  have hq : IsQuasisimple (J ⧸ pCore 2 J) := he ▸ s.quasisimple
  have hsrc := (s.overcomponent_source_of_quasisimple h hJ hKJ hq).toHypothesis1221
  refine ⟨he,?_⟩
  cases hb with
  | linear f hf hm => exact ⟨f,hf,he.symm ▸ hm⟩
  | unitary f hf hm => exact (Models.chosen_unitary_no_ff E hsrc hf hm hff).elim
  | suzuki m hm em => exact (Models.chosen_suzuki_no_ff E hsrc hm em hff).elim

/-- The original normal seed supplies the chosen module on a nonlinear
Bender overcomponent, and the literal quotient proves its full normalizer
has no FF witness. No module or coordinate marking is assumed. -/
theorem ComponentSeed.exists_nonFF_chosen_of_normal_bender_nonLinear
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hn : (K.subgroupOf H).Normal)
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    (hm : (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSU (J ⧸ pCore 2 J) 3 (2 ^ f)) ∨
      (∃ m : ℕ, 1 ≤ m ∧
        Nonempty ((J ⧸ pCore 2 J) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))) :
    ∃ W : Subgroup G, ∃ E : Chapter12.Section02.ChosenModule T J W,
      ¬ IsFFModule (normalizerRepresentation E.chosenAction) := by
  obtain ⟨W,⟨E⟩⟩ := s.exists_chosen_overcomponent_of_normal h hn hJ.1 hKJ
  refine ⟨W,E,?_⟩
  have hb : ClassificationModels.IsBenderModel (J ⧸ pCore 2 J) := by
    rcases hm with ⟨f,hf,hu⟩ | ⟨m,hm,em⟩
    · exact .unitary f hf hu
    · exact .suzuki m hm em
  have he := s.eq_overcomponent_of_bender_twoCore h hJ.1 hKJ hb
  have hq : IsQuasisimple (J ⧸ pCore 2 J) := he ▸ s.quasisimple
  have hsrc := (s.overcomponent_source_of_quasisimple h hJ hKJ hq).toHypothesis1221
  rcases hm with ⟨f,hf,hu⟩ | ⟨m,hm,em⟩
  · exact Models.chosen_unitary_no_ff E hsrc hf hu
  · exact Models.chosen_suzuki_no_ff E hsrc hm em

/-- The Suzuki source seed cannot lie in any Bender overcomponent carrying
an FF chosen module, even if its containing model has a different exponent. -/
theorem ComponentSeed.not_bender_overcomponent_of_suzuki_ff
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    {W : Subgroup G} (E : Chapter12.Section02.ChosenModule T J W)
    (hff : IsFFModule (normalizerRepresentation E.chosenAction))
    {m : ℕ} (hm : 1 ≤ m)
    (em : Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    ¬ ClassificationModels.IsBenderModel (J ⧸ pCore 2 J) := by
  intro hb
  obtain ⟨_,f,hf,hlin⟩ := s.linear_model_of_bender_overcomponent_ff h hJ hKJ E hff hb
  exact s.not_linear_overcomponent_of_suzuki h (s.mem_local_family h) le_rfl hm em f hf hlin

/-- The higher-rank source models retain their literal star image and its
full covering kernel in the same FF comparison. -/
theorem ComponentSeed.not_bender_overcomponent_of_higher_rank_image_ff
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    {W : Subgroup G} (E : Chapter12.Section02.ChosenModule T J W)
    (hff : IsFFModule (normalizerRepresentation E.chosenAction))
    (R : Subgroup H) [R.Normal] (hR : pCore 2 H ≤ R)
    [Nontrivial ((K.subgroupOf H).map (QuotientGroup.mk' R))]
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU ((K.subgroupOf H).map (QuotientGroup.mk' R)) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSL ((K.subgroupOf H).map (QuotientGroup.mk' R)) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSp ((K.subgroupOf H).map (QuotientGroup.mk' R)) 2 (2 ^ n)) :
    ¬ ClassificationModels.IsBenderModel (J ⧸ pCore 2 J) := by
  intro hb
  obtain ⟨_,f,hf,hlin⟩ := s.linear_model_of_bender_overcomponent_ff h hJ hKJ E hff hb
  exact s.not_linear_overcomponent_of_higher_rank_image h (s.mem_local_family h) le_rfl
    R hR hn hm f hf hlin

/-- Actual 11.3.5--6 assembly in the Bender/FF branch. The source field,
flag, moved point, relative normality and literal residual quotient are
unchanged; only the FF witness and containing-model branch remain inputs. -/
theorem ComponentSeed.conclusion_of_bender_overcomponent_ff
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
    (hb : ClassificationModels.IsBenderModel (J ⧸ pCore 2 J))
    (hres : ∀ r : ℕ, r.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          r ∣ 2 ^ S.field.degree - 1 ∧ 3 < r) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          r ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual r (normalizer (L : Set G)) =
        L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    K = residual H ∧ J = residual H ∧ Conclusion S H := by
  obtain ⟨he,f,hf,hm⟩ := s.linear_model_of_bender_overcomponent_ff h hJ hKJ E hff hb
  obtain ⟨_,hK,ho⟩ := s.conclusion_of_linear_odd_kernel h pr hc F hpoint hs hcontrol hf hm hres hcubic
  exact ⟨hK,he.symm.trans hK,ho⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
