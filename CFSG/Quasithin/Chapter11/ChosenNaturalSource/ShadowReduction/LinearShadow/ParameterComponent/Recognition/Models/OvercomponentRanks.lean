module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.Overcomponent
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ThreeRank
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.SpecificGroups.SymplecticFour.OddFieldActors.Cubic
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank

/-!
# Quasisimple overcomponents from the actual higher-rank star models

An odd-prime rank-two quotient cannot be an image of a group of odd-prime
rank at most one: its Sylow subgroup would be cyclic and so would every
Sylow image. Apply this at three to the literal star projection of K.
The rank lower bound passes through K ≤ J, and A.3.6 makes J/O₂(J)
quasisimple. Thus no central-cover or quotient-rank invariance is assumed.

The symplectic-four model always has an elementary nine. Linear-three
models in even field degree and unitary-three models in odd fixed-field
degree have the corresponding projective diagonal/cycle nine. These
three cases discharge the previously explicit quasisimple-quotient
premise of the normalized chosen-overcomponent construction. The final
consumer refines the original counterexample catalogue at its literal
model exponents and actual H/core_H(M) quotient.

The other signed-three parities, rank-one recognition at n(H), embedding
and FF exclusions, and doubled-SL₃ assembly remain with the parameter-
component owner. The existing preceding-source inputs retain their final
discharge with qt-d-1222-shadow-linear-geometry. No unconditional
11.3.5 or 11.3.6 conclusion is asserted here.
Source: Aschbacher--Smith, 11.3.5(1), pp.771--772; A.3.6, pp.43--45;
1.2.1(4), p.504 (combined manuscript, 1 March 2004).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent

private theorem three_rank_two_of_surjective
    {X Y : Type*} [Group X] [Finite X] [Group Y]
    (q : X →* Y) (hq : Function.Surjective q) (hr : 2 ≤ primeRank 3 Y) :
    2 ≤ primeRank 3 X := by
  by_contra hsmall
  let P : Sylow 3 X := Classical.choice inferInstance
  have hcyc := P.isCyclic_of_odd_of_primeRank_le_one (by decide) (by omega)
  have hh := P.primeRank_le_one_of_surjective hcyc q hq
  omega

private theorem symplectic_three_rank {X : Type*} [Group X] [Finite X]
    {f : ℕ} (hm : ClassicalGroup.IsPSp X 2 (2 ^ f)) : 2 ≤ primeRank 3 X := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  rw [primeRank_equiv 3 (e.trans
    (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm)]
  exact Theory.SpecificGroups.SymplecticFour.OddFieldActors.cubic_rank

private theorem linear_three_rank {X : Type*} [Group X] [Finite X]
    {f : ℕ} (he : Even f) (hm : ClassicalGroup.IsPSL X 3 (2 ^ f)) :
    2 ≤ primeRank 3 X := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  rw [primeRank_equiv 3 e]
  exact Theory.SpecificGroups.SignedThreeCubicRank.linear_projective hcard he

private theorem unitary_three_rank {X : Type*} [Group X] [Finite X]
    {f : ℕ} (hf : 0 < f) (ho : Odd f) (hm : ClassicalGroup.IsPSU X 3 (2 ^ f)) :
    2 ≤ primeRank 3 X := by
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
  rw [primeRank_equiv 3 e]
  exact Theory.SpecificGroups.SignedThreeCubicRank.unitary_projective J hf hcard hconj ho

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K J : Subgroup G}

/-- Cubic rank in any literal quotient image of the seed forces the containing
local component's own two-core quotient to be quasisimple. No quotient rank
monotonicity is assumed: rank at most one would give cyclic Sylow threes. -/
theorem ComponentSeed.overcomponent_quasisimple_of_quotient_three_rank
    (s : ComponentSeed T H K) (S : D.NonbinaryNaturalInput)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J)
    (R : Subgroup H) [R.Normal]
    (hr : 2 ≤ primeRank 3 ((K.subgroupOf H).map (QuotientGroup.mk' R))) :
    IsQuasisimple (J ⧸ pCore 2 J) := by
  have hK : 2 ≤ primeRank 3 K := by
    rw [←primeRank_equiv 3 (subgroupOfEquivOfLe s.component.1)]
    exact three_rank_two_of_surjective ((QuotientGroup.mk' R).subgroupMap (K.subgroupOf H))
      ((QuotientGroup.mk' R).subgroupMap_surjective (K.subgroupOf H)) hr
  have hlocal := (Chapter1.Section02.Adequate.mem_L_iff_mainForward T J).mp hJ
  obtain ⟨_,_,_,_,hsq⟩ := MainForward.localComponents_local_setup
    S.source.simpleQTKE T hlocal
  let B := J.subgroupOf (J ⊔ (T : Subgroup G))
  have hB : 2 ≤ primeRank 3 B := by
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe le_sup_left)]
    exact hK.trans (primeRank_mono 3 hKJ)
  let : IsQuasisimple (B ⧸ pCore 2 B) :=
    ChapterA.Section03.cComponent_twoCore_quasisimple_of_three_rank hsq hJ.1 hB
  let e : B ≃* J := subgroupOfEquivOfLe le_sup_left
  exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))

/-- The symplectic star row constructs the same normalized chosen overcomponent
with all 12.2.3 hypotheses, including its intrinsic quasisimple quotient. -/
theorem ComponentSeed.chosen_overcomponent_of_symplectic_image
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hn : (K.subgroupOf H).Normal)
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    (R : Subgroup H) [R.Normal] {f : ℕ}
    (hm : ClassicalGroup.IsPSp ((K.subgroupOf H).map (QuotientGroup.mk' R)) 2 (2 ^ f)) :
    Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
      (T : Subgroup G) ≤ normalizer (J : Set G) ∧
      ∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T J W) :=
  s.chosen_overcomponent_of_normal h hn hJ hKJ
    (s.overcomponent_quasisimple_of_quotient_three_rank S hJ.1 hKJ R
      (symplectic_three_rank hm))

/-- Even-degree linear-three star rows have the same actual source setup. -/
theorem ComponentSeed.chosen_overcomponent_of_even_linear_image
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hn : (K.subgroupOf H).Normal)
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    (R : Subgroup H) [R.Normal] {f : ℕ} (he : Even f)
    (hm : ClassicalGroup.IsPSL ((K.subgroupOf H).map (QuotientGroup.mk' R)) 3 (2 ^ f)) :
    Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
      (T : Subgroup G) ≤ normalizer (J : Set G) ∧
      ∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T J W) :=
  s.chosen_overcomponent_of_normal h hn hJ hKJ
    (s.overcomponent_quasisimple_of_quotient_three_rank S hJ.1 hKJ R
      (linear_three_rank he hm))

/-- Odd-degree unitary-three star rows retain the original Hermitian convention. -/
theorem ComponentSeed.chosen_overcomponent_of_odd_unitary_image
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hn : (K.subgroupOf H).Normal)
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    (R : Subgroup H) [R.Normal] {f : ℕ} (hf : 0 < f) (ho : Odd f)
    (hm : ClassicalGroup.IsPSU ((K.subgroupOf H).map (QuotientGroup.mk' R)) 3 (2 ^ f)) :
    Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
      (T : Subgroup G) ≤ normalizer (J : Set G) ∧
      ∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T J W) :=
  s.chosen_overcomponent_of_normal h hn hJ hKJ
    (s.overcomponent_quasisimple_of_quotient_three_rank S hJ.1 hKJ R
      (unitary_three_rank hf ho hm))

/-- The original source catalogue now constructs the complete chosen-module
setup in the symplectic and cubic-rank signed-three rows. The remaining signed
parities keep their actual star models, without an assumed quotient marking. -/
theorem exists_componentSeed_with_cubic_rank_overcomponent_source
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary) :
    let P := T.subtype h.outside.1.1.2
    let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
    ∃ K J : Subgroup G, ComponentSeed T H K ∧ K ≤ J ∧
      J ∈ Chapter1.LStar G (T : Subgroup G) ∧
      J ∈ MainForward.faithfulLocalComponents T ∧
      ¬ J ≤ normalizer (L : Set G) ∧ ⁅sourceZ T,J⁆ ≠ ⊥ ∧
      (((∃ f : ℕ, 2 ≤ f ∧ ChapterE.generationParameter H ≤ f ∧
          ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) ∨
        (∃ m : ℕ, 1 ≤ m ∧ ChapterE.generationParameter H ≤ 2 * m + 1 ∧
          Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))) ∧
          solvableRadical H = pCore 2 H ∨
        (K.subgroupOf H).Normal ∧ (T : Subgroup G) ≤ normalizer (J : Set G) ∧
          (∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T J W)) ∧
          (let I := (K.subgroupOf H).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore P hP))
           ∃ f : ℕ, 2 ≤ f ∧ ChapterE.generationParameter H ≤ f ∧
             ((Even f ∧ ClassicalGroup.IsPSU I 3 (2 ^ f)) ∨
              (Odd f ∧ ClassicalGroup.IsPSL I 3 (2 ^ f)) ∨
              (Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
                ((Odd f ∧ ClassicalGroup.IsPSU I 3 (2 ^ f)) ∨
                 (Even f ∧ ClassicalGroup.IsPSL I 3 (2 ^ f)) ∨
                 ClassicalGroup.IsPSp I 2 (2 ^ f)))))) := by
  obtain ⟨K,J,s,hKJ,hJ,hfaith,ho,hm,hcases⟩ :=
    exists_componentSeed_with_normalized_higher_rank_models h pr hc hs
  refine ⟨K,J,s,hKJ,hJ,hfaith,ho,hm,?_⟩
  rcases hcases with hlow | ⟨hn,hTJ,hchosen,f,hf,hbound,hmodels⟩
  · exact .inl hlow
  refine .inr ⟨hn,hTJ,hchosen,f,hf,hbound,?_⟩
  rcases hmodels with huni | hlin | hsp
  · rcases Nat.even_or_odd f with he | ho
    · exact .inl ⟨he,huni⟩
    · exact .inr (.inr ⟨(s.chosen_overcomponent_of_odd_unitary_image h hn hJ hKJ
        _ (by omega) ho huni).1,.inl ⟨ho,huni⟩⟩)
  · rcases Nat.even_or_odd f with he | ho
    · exact .inr (.inr ⟨(s.chosen_overcomponent_of_even_linear_image h hn hJ hKJ
        _ he hlin).1,.inr (.inl ⟨he,hlin⟩)⟩)
    · exact .inr (.inl ⟨ho,hlin⟩)
  · exact .inr (.inr ⟨(s.chosen_overcomponent_of_symplectic_image h hn hJ hKJ _ hsp).1,
      .inr (.inr hsp)⟩)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
