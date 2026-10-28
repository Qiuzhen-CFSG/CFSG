module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.StarSource
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryIntrinsicQuotients
public import CFSG.Quasithin.ChapterE.Section02.Structure.BinaryExclusions.Models
public import Theory.SpecificGroups.BinaryLinear.SmallCubicRank

/-!
# Excluding binary degree-three, four and five containing quotients

The original component cannot have PSL₃(2), PSL₄(2) or PSL₅(2) as its
own two-core quotient. The degree-three case uses the concrete PSL₂(7)
isomorphism: both the normal and paired rows give n(H) ≤ 1, contrary
to the original counterexample bound. In degrees four and five, cubic
rank two excludes a paired seed. Relative normality then descends to the
actual image in H/O₂(H), where the preserved Sylow supplement and minimal
parabolicity contradict the binary invariant-parabolic calculation.

For a containing quotient PSL_d(2), 3 ≤ d ≤ 5, the intrinsic local
quotient theorem identifies K/O₂(K) with PSL_m(2), 3 ≤ m ≤ d. Applying
the preceding exclusion removes all three containing rows, without an
FF hypothesis or a preselected seed model. The final application retains
the original catalogue, field exponents, full Sylow intersection and
literal quotient maps. The preceding odd-prime exclusion is also stated
on K/O₂(K), in both relative-normality branches.

Elementary full-root lifting, recognition at the actual generation
minimum, the remaining containing-model/FF exclusions and the paired and
doubled assembly remain with this owner. This module does not assert
unconditional 11.3.5 or 11.3.6. The preceding source inputs retain their
producers and final discharge by qt-d-1222-shadow-linear-geometry.
Source: Aschbacher--Smith, A.3.12 and E.2.2, printed pp.47--48,215--216,
used in 11.3.5(1), pp.771--772 (refs/quasithin.pdf). The existing imported
exceptional isomorphism facts retain LICENSES/ATLAS.txt attribution.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K J : Subgroup G}

/-- Neither relative-normality branch permits an odd-prime PSL₂ quotient
above the exceptional prime five on the original component. -/
theorem ComponentSeed.not_odd_prime_model (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    {r : ℕ} (hr : r.Prime) (ho : Odd r) (hlarge : 7 ≤ r) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 r := by
  intro hm
  let P := T.subtype h.outside.1.1.2
  let B := K.subgroupOf H
  let := s.quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv s.intrinsicQuotientEquiv
  have hu : ChapterE.generationParameter H ≤ 1 := by
    by_cases hn : B.Normal
    · let := hn
      apply ChapterE.generationParameter_le (by decide)
      exact Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.isEGenerated_of_normal_odd_component
        (outside_sqtk h) P B s.component.2 (s.intrinsic_supplement h.outside.1.1.2)
        ho hlarge (hm.of_mulEquiv s.intrinsicQuotientEquiv.symm)
    · let : Fact r.Prime := ⟨hr⟩
      let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
      have hsolv := counterexample_not_solvable h pr hc hs
      have hcore : ChapterB.minimalParabolicCore P hP = pCore 2 H :=
        (ChapterB.minimalParabolic_nonsolvable_core_eq_radical P hP hsolv).trans
          (s.paired_radical_eq_twoCore h pr hc hs hn)
      let e := s.quotientImageEquivOfCore (ChapterB.minimalParabolicCore P hP) hcore
      exact ChapterE.Structure.NumericalBounds.paired_prime_upper_one
        ChapterA.Section02.theoremA_knownSimple (outside_sqtk h) P hP hsolv B
        s.component.2 (s.intrinsic_supplement h.outside.1.1.2) hn hlarge
        (hm.of_mulEquiv e.symm)
  have hl := degree_le_parameter h pr hc hs
  have hnon := S.nonbinary
  omega

private def binary_equiv {X : Type*} [Group X] {d : ℕ}
    (hm : ClassicalGroup.IsPSL X d 2) : X ≃* PSL(d,ZMod 2) := by
  apply Classical.choice
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let a : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  exact ⟨e.trans (Atlas.fieldEquivPSL d a)⟩

private theorem normal_of_binary_higher_model (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) d 2) : (K.subgroupOf H).Normal := by
  by_contra hn
  have hu : primeRank 3 (K ⧸ pCore 2 K) ≤ 1 := by
    rcases s.paired_binary_models h pr hc hs hn with ⟨f,hf,_,hlin⟩ | ⟨m,hm,_,⟨e⟩⟩
    · exact Models.odd_rank_of_binary_linear (by omega) hlin 3 (by decide) (by decide)
    · exact Models.odd_rank_of_suzuki (by omega) e 3 (by decide) (by decide)
  let e := (binary_equiv hm).trans (BinaryLinear.OuterCyclic.projectiveEquivSL
    (by rcases hd with rfl | rfl <;> decide))
  have hl := BinaryLinear.SmallCubicRank.four_or_five hd
  rw [← primeRank_equiv 3 e] at hl
  omega

private theorem not_normal_binary_higher_model (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hn : (K.subgroupOf H).Normal) {d : ℕ} (hd : d = 4 ∨ d = 5) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) d 2 := by
  intro hm
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
  exact ChapterE.BinaryExclusions.not_linear_binary
    (P.mapSurjective (QuotientGroup.mk'_surjective _)) I hgen hmin hd
    (hm.of_mulEquiv e.symm)

/-- The original component excludes all three small binary linear quotients.
No field exponent is identified with the generation minimum. -/
theorem ComponentSeed.not_small_binary_linear_model (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    {d : ℕ} (hd : d = 3 ∨ d = 4 ∨ d = 5) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) d 2 := by
  intro hm
  rcases hd with rfl | hd
  · exact s.not_odd_prime_model h pr hc hs (by decide) (by decide) (by decide)
      (ChapterE.Structure.PairedModels.psl_three_two_as_seven hm)
  · exact not_normal_binary_higher_model s h pr hc
      (normal_of_binary_higher_model s h pr hc hs hd hm) hd hm

/-- Project through the actual containing two-core and use its full Sylow
intersection to exclude the three binary higher-linear containing rows. -/
theorem ComponentSeed.not_small_binary_linear_overcomponent (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J)
    {d : ℕ} (hd : d = 3 ∨ d = 4 ∨ d = 5) :
    ¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) d 2 := by
  intro hm
  let e := (binary_equiv hm).trans (BinaryLinear.OuterCyclic.projectiveEquivLinear
    (by omega : 0 < d))
  obtain ⟨m,hm3,hmd,⟨a⟩⟩ :=
    ChapterA.Section03.SourceEmbeddings.BinaryIntrinsic.local_twoCore_quotient_of_containing_quotient
      T (s.mem_local_family h).1 hJ.1 hKJ d (by omega) e
  apply s.not_small_binary_linear_model h pr hc hs (by omega : m = 3 ∨ m = 4 ∨ m = 5)
  exact ⟨ZMod 2,inferInstance,inferInstance,by simp,
    ⟨a.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < m)).symm⟩⟩

/-- Construct the original seed and faithful maximal overcomponent, retaining
the literal catalogue and excluding every small binary linear container. -/
theorem exists_componentSeed_with_small_binary_containing_exclusion
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
  obtain ⟨K,J,s,hKJ,hJ,hfaith,ho,hm,hcases⟩ :=
    exists_componentSeed_with_literal_binary_models h pr hc hs
  exact ⟨K,J,s,hKJ,hJ,hfaith,ho,hm,
    fun _ hd => s.not_small_binary_linear_overcomponent h pr hc hs hJ.1 hKJ hd,hcases⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
