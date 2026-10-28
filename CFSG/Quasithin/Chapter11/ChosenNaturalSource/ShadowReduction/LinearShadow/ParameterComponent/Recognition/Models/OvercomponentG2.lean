module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.OvercomponentBinary
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.OvercomponentSplit
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank

/-!
# Recognition inside a G₂ overcomponent

The original component cannot itself have a G₂ quotient. The explicit
cubic subgroup gives odd-prime rank two, excluding the paired row. In
the normal row the original two-core projection preserves the component,
its relative normality, the full Sylow supplement and minimal parabolicity.
The two invariant G₂ parabolics then give a contradiction.

Thus a seed inside a nonbinary G₂ overcomponent is proper. The checked
local quotient calculation identifies K/O₂(K) with PSL₂ over that same
containing field. This discharges the properness premise, without assuming
an equality between that field's degree and n(H). The higher-rank star
image application excludes all G₂ containers in those rows. The original
catalogue application retains the binary degree-three/four/five exclusions
and the independent component-model exponents.

The elementary full-root lift and recognition at n(H), remaining
containing-model/FF exclusions, and paired/doubled assembly are still
required. The preceding source inputs retain their producers and final
discharge by qt-d-1222-shadow-linear-geometry. No unconditional 11.3.5
or 11.3.6 is asserted here.
Source: Aschbacher--Smith, A.3.12 and E.2.2, printed pp.47--48,215--216,
in the model comparison of 11.3.5(1), pp.771--772 (refs/quasithin.pdf).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K J : Subgroup G}

/-- Neither relative-normality branch of the original component permits
a G₂ model of its literal two-core quotient. -/
theorem ComponentSeed.not_g2_model (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (f : ℕ) : ¬ ClassificationModels.IsG2At (K ⧸ pCore 2 K) (2 ^ f) := by
  intro hm
  have hn : (K.subgroupOf H).Normal := by
    by_contra hn
    have hu : primeRank 3 (K ⧸ pCore 2 K) ≤ 1 := by
      rcases s.paired_binary_models h pr hc hs hn with ⟨d,hd,_,hlin⟩ | ⟨m,hm,_,⟨e⟩⟩
      · exact Models.odd_rank_of_binary_linear (by omega) hlin 3 (by decide) (by decide)
      · exact Models.odd_rank_of_suzuki (by omega) e 3 (by decide) (by decide)
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    have hl := (Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2 (F := F)).trans
      (primeRank_subgroup_le 3 (commutator (Atlas.G2.Model F)))
    rw [primeRank_equiv 3 e] at hu
    omega
  let P := T.subtype h.outside.1.1.2
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := K.subgroupOf H
  let I := B.map q
  let := s.quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv s.intrinsicQuotientEquiv
  let : B.Normal := hn
  let : I.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let e := s.intrinsicQuotientEquiv.trans (cComponentTwoCoreQuotientEquiv s.component.2)
  have hgen : I ⊔ (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H)) :
      Subgroup (H ⧸ pCore 2 H)) = ⊤ := by
    change B.map q ⊔ (P : Subgroup H).map q = ⊤
    rw [← Subgroup.map_sup,s.intrinsic_supplement h.outside.1.1.2,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hmin := ChapterB.minimalParabolic_surjective P
    (outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc))
    q (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup.le_sylow_of_normal P)
  obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := hm
  exact ChapterE.BinaryExclusions.not_g2_binary
    (P.mapSurjective (QuotientGroup.mk'_surjective _)) I hgen hmin f
    ⟨F,hF,hfin,hcard,⟨e.symm.trans a⟩⟩

/-- A G₂ overcomponent forces proper containment and the actual PSL₂
quotient at the containing field degree. -/
theorem ComponentSeed.linear_model_of_g2_overcomponent (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J)
    {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassificationModels.IsG2At (J ⧸ pCore 2 J) (2 ^ f)) :
    K < J ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f) := by
  have hp : K < J := lt_of_le_of_ne hKJ (by
    intro he
    subst J
    exact s.not_g2_model h pr hc hs f hm)
  exact ⟨hp,s.linear_model_of_proper_split_overcomponent h hJ hp hf
    (.inr (.inr (.inr hm)))⟩

/-- The literal higher-rank star image excludes every nonbinary G₂
overcomponent, even at an independently marked field exponent. -/
theorem ComponentSeed.not_g2_overcomponent_of_higher_rank_image
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J)
    (R : Subgroup H) [R.Normal] (hR : pCore 2 H ≤ R)
    [Nontrivial ((K.subgroupOf H).map (QuotientGroup.mk' R))]
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU ((K.subgroupOf H).map (QuotientGroup.mk' R)) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSL ((K.subgroupOf H).map (QuotientGroup.mk' R)) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSp ((K.subgroupOf H).map (QuotientGroup.mk' R)) 2 (2 ^ n))
    {f : ℕ} (hf : 2 ≤ f) :
    ¬ ClassificationModels.IsG2At (J ⧸ pCore 2 J) (2 ^ f) := by
  intro hg2
  have he := s.eq_split_overcomponent_of_higher_rank_image h hJ hKJ R hR hn hm hf
    (.inr (.inr (.inr hg2)))
  subst J
  exact s.not_g2_model h pr hc hs f hg2

/-- The original catalogue now excludes the three small binary containers
and recognizes the seed whenever its maximal overcomponent has a G₂ quotient. -/
theorem exists_componentSeed_with_binary_and_g2_containing_sieve
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary) :
    let P := T.subtype h.outside.1.1.2
    let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
    ∃ K J : Subgroup G, ComponentSeed T H K ∧ K ≤ J ∧
      J ∈ Chapter1.LStar G (T : Subgroup G) ∧
      J ∈ MainForward.faithfulLocalComponents T ∧
      ¬ J ≤ normalizer (L : Set G) ∧ ⁅sourceZ T,J⁆ ≠ ⊥ ∧
      (∀ d : ℕ, (d = 3 ∨ d = 4 ∨ d = 5) →
        ¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) d 2) ∧
      (∀ f : ℕ, 2 ≤ f → ClassificationModels.IsG2At (J ⧸ pCore 2 J) (2 ^ f) →
        K < J ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) ∧
      (((∃ f : ℕ, 2 ≤ f ∧ ChapterE.generationParameter H ≤ f ∧
          ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) ∨
        (∃ m : ℕ, 1 ≤ m ∧ ChapterE.generationParameter H ≤ 2 * m + 1 ∧
          Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))) ∧
          solvableRadical H = pCore 2 H ∨
        (K.subgroupOf H).Normal ∧
          (let I := (K.subgroupOf H).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore P hP))
           ∃ f : ℕ, 2 ≤ f ∧ ChapterE.generationParameter H ≤ f ∧
             (ClassicalGroup.IsPSU I 3 (2 ^ f) ∨ ClassicalGroup.IsPSL I 3 (2 ^ f) ∨
               ClassicalGroup.IsPSp I 2 (2 ^ f)))) := by
  obtain ⟨K,J,s,hKJ,hJ,hfaith,ho,hm,hbin,hcases⟩ :=
    exists_componentSeed_with_small_binary_containing_exclusion h pr hc hs
  exact ⟨K,J,s,hKJ,hJ,hfaith,ho,hm,hbin,
    fun _ hf hg2 => s.linear_model_of_g2_overcomponent h pr hc hs hJ.1 hKJ hf hg2,hcases⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
