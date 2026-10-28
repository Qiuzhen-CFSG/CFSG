module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.Star
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.Small
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.Faithful

/-!
# Literal rank-one quotients in the original component catalogue

The component selected from the 11.3.2 counterexample is quasisimple
modulo its own two-core. Its simple image in H/core_H(M) has odd-prime
rank at most one in the binary PSL₂ and Suzuki rows. The original
projection is therefore an isomorphism by the central-cover argument in
Star. When the component is normal in H, its simple quotient and the
Sylow supplement also prove R(H) = O₂(H).

The two public maximal-core conventions are compared through their
normal-subgroup characterizations. Quotient transport retains the actual
inclusion and quotient maps, without exposing the core's implementation.
The final catalogue constructs both K and its faithful maximal
overcomponent, now with the literal K/O₂(K) model in the rank-one rows.
The field-four application feeds the existing parameter/component conclusion.

The remaining model exclusions, equality of the model exponent with
n(H), and the retained paired fixed-point construction belong to this
parameter-component owner. The preceding natural marking, residual and
cubic source clauses retain their producers and final discharge by
qt-d-1222-shadow-linear-geometry. No unconditional 11.3.5--6 conclusion
is asserted here.
Source: Aschbacher--Smith E.2.2, pp.215--216; 11.3.5--6, pp.771--772.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent

open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels

private theorem sourceKernel_eq_core {X : Type*} [Group X] [Finite X]
    (P : Sylow 2 X) (hP : ChapterB.IsMinimalParabolicOver P ⊤)
    (hs : ¬ Group.IsSolvable X) :
    sourceKernel (ChapterB.minimalParabolicMax P hP) =
      ChapterB.minimalParabolicCore P hP := by
  let M := ChapterB.minimalParabolicMax P hP
  have hM := ChapterB.minimalParabolicMax_spec P hP
  refine le_antisymm ?_ ?_
  · rcases ChapterB.minimalParabolic_normal_subgroup_dichotomy P hP M.normalCore with h | h
    · exact h
    · exact (hM.1.ne_top (top_unique (h ▸ sup_le hM.2 M.normalCore_le))).elim
  · rw [ChapterB.minimalParabolic_nonsolvable_core_eq_radical P hP hs]
    apply normal_le_normalCore.mpr
    let : Group.IsNilpotent (P : Subgroup X) := P.isPGroup'.isNilpotent
    rcases eq_top_or_exists_le_coatom (solvableRadical X ⊔ (P : Subgroup X)) with h | ⟨N,hN,hle⟩
    · exact (hs (Group.isSolvable_of_normal_sup_eq_top _ _ h)).elim
    · have he := ChapterB.minimalParabolicMax_unique P hP hN (le_sup_right.trans hle)
      exact (le_sup_left.trans hle).trans_eq he

private def quotientImageEquivOfEq {X : Type*} [Group X]
    (B N R : Subgroup X) [N.Normal] [R.Normal] (he : N = R) :
    B.map (QuotientGroup.mk' N) ≃* B.map (QuotientGroup.mk' R) := by
  subst R
  exact MulEquiv.refl _

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

/-- The original component projection identifies its own two-core quotient
with its simple star image whenever the latter has odd-prime rank at most one. -/
theorem ComponentSeed.star_odd_rank_equiv (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p
      ((K.subgroupOf H).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore
        (T.subtype h.outside.1.1.2)
        (outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc))))) ≤ 1) :
    Nonempty ((K ⧸ pCore 2 K) ≃*
      (K.subgroupOf H).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore
        (T.subtype h.outside.1.1.2)
        (outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc))))) := by
  let P := T.subtype h.outside.1.1.2
  let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
  let R := ChapterB.minimalParabolicCore P hP
  let B := K.subgroupOf H
  let := s.quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv s.intrinsicQuotientEquiv
  let : IsSimpleGroup (B.map (QuotientGroup.mk' R)) :=
    (ChapterE.Structure.source_component_simple_image P hP
      (counterexample_not_solvable h pr hc hs) B s.component.2
      (s.intrinsic_supplement h.outside.1.1.2)).1
  exact ⟨s.intrinsicQuotientEquiv.trans
    (Models.starEquiv B R s.component.2 (ChapterB.minimalParabolicTwoCore_le_core P hP) hr)⟩

/-- Transport a binary PSL₂ model from the star image to the literal
K/O₂(K), preserving its given field exponent. -/
theorem ComponentSeed.linear_model_of_star (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    {f : ℕ} (hf : 0 < f)
    (hm : ClassicalGroup.IsPSL
      ((K.subgroupOf H).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore
        (T.subtype h.outside.1.1.2)
        (outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)))))
      2 (2 ^ f)) : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f) := by
  obtain ⟨e⟩ := s.star_odd_rank_equiv h pr hc hs (Models.odd_rank_of_binary_linear hf hm)
  exact hm.of_mulEquiv e

/-- Transport the actual Suzuki matrix model to the literal component
two-core quotient; no abstract family label replaces the isomorphism. -/
theorem ComponentSeed.suzuki_model_of_star (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    {m : ℕ} (hm : 0 < m)
    (he : Nonempty (((K.subgroupOf H).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore
        (T.subtype h.outside.1.1.2)
        (outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc))))) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  obtain ⟨a⟩ := he
  obtain ⟨e⟩ := s.star_odd_rank_equiv h pr hc hs (Models.odd_rank_of_suzuki hm a)
  exact ⟨e.trans a⟩

/-- A normal component with simple own two-core quotient and the
original Sylow supplement makes the ambient solvable radical a two-group. -/
theorem ComponentSeed.radical_eq_twoCore_of_normal_simple
    (s : ComponentSeed T H K) (hTH : (T : Subgroup G) ≤ H)
    (hn : (K.subgroupOf H).Normal) [IsSimpleGroup (K ⧸ pCore 2 K)] :
    solvableRadical H = pCore 2 H := by
  let B := K.subgroupOf H
  let : B.Normal := hn
  let : Group.IsPerfect B := s.component.2.perfect
  let : IsSimpleGroup (B ⧸ pCore 2 B) := s.intrinsicQuotientEquiv.symm.isSimpleGroup
  exact PerfectCoreTwoExtension.extension_radical_eq_core B
    (isPGroup_quotient_of_sup_eq_top B (T.subtype hTH : Subgroup H)
      (T.subtype hTH).isPGroup' (s.intrinsic_supplement hTH))

/-- Odd-rank rigidity discharges the simple-quotient premise of the
normal-component radical identity. -/
theorem ComponentSeed.normal_radical_eq_twoCore_of_star_odd_rank
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : (K.subgroupOf H).Normal)
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p
      ((K.subgroupOf H).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore
        (T.subtype h.outside.1.1.2)
        (outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc))))) ≤ 1) :
    solvableRadical H = pCore 2 H := by
  let P := T.subtype h.outside.1.1.2
  let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
  let R := ChapterB.minimalParabolicCore P hP
  let B := K.subgroupOf H
  let : IsSimpleGroup (B.map (QuotientGroup.mk' R)) :=
    (ChapterE.Structure.source_component_simple_image P hP
      (counterexample_not_solvable h pr hc hs) B s.component.2
      (s.intrinsic_supplement h.outside.1.1.2)).1
  obtain ⟨e⟩ := s.star_odd_rank_equiv h pr hc hs hr
  let : IsSimpleGroup (K ⧸ pCore 2 K) := e.isSimpleGroup
  exact s.radical_eq_twoCore_of_normal_simple h.outside.1.1.2 hn

/-- The normal catalogue now has literal PSL₂ and Suzuki quotient
models and R(H) = O₂(H); its three higher-rank rows remain on the star image. -/
theorem ComponentSeed.normal_binary_literal_models (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : (K.subgroupOf H).Normal) :
    let P := T.subtype h.outside.1.1.2
    let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
    let I := (K.subgroupOf H).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore P hP))
    (∃ f : ℕ, 2 ≤ f ∧ ChapterE.generationParameter H ≤ f ∧
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f) ∧ solvableRadical H = pCore 2 H) ∨
    (∃ m : ℕ, 1 ≤ m ∧ ChapterE.generationParameter H ≤ 2 * m + 1 ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∧
      solvableRadical H = pCore 2 H) ∨
    (∃ f : ℕ, 2 ≤ f ∧ ChapterE.generationParameter H ≤ f ∧
      (ClassicalGroup.IsPSU I 3 (2 ^ f) ∨ ClassicalGroup.IsPSL I 3 (2 ^ f) ∨
        ClassicalGroup.IsPSp I 2 (2 ^ f))) := by
  obtain ⟨f,hf,hu,hm⟩ := s.normal_binary_models h pr hc hs hn
  let P := T.subtype h.outside.1.1.2
  let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
  let e := quotientImageEquivOfEq (K.subgroupOf H) _ _
    (sourceKernel_eq_core P hP (counterexample_not_solvable h pr hc hs))
  rcases hm with hlin | huni | hthree | hsp | ⟨m,hm,he,⟨a⟩⟩
  · have hlin' := hlin.of_mulEquiv e.symm
    exact .inl ⟨f,hf,hu,s.linear_model_of_star h pr hc hs (by omega) hlin',
      s.normal_radical_eq_twoCore_of_star_odd_rank h pr hc hs hn
        (Models.odd_rank_of_binary_linear (by omega) hlin')⟩
  · exact .inr (.inr ⟨f,hf,hu,.inl (huni.of_mulEquiv e.symm)⟩)
  · exact .inr (.inr ⟨f,hf,hu,.inr (.inl (hthree.of_mulEquiv e.symm))⟩)
  · exact .inr (.inr ⟨f,hf,hu,.inr (.inr (hsp.of_mulEquiv e.symm))⟩)
  · exact .inr (.inl ⟨m,hm,he ▸ hu,s.suzuki_model_of_star h pr hc hs (by omega)
      ⟨e.symm.trans a⟩,
      s.normal_radical_eq_twoCore_of_star_odd_rank h pr hc hs hn
        (Models.odd_rank_of_suzuki (by omega) (e.symm.trans a))⟩)

/-- Construct the original component and its maximal faithful overcomponent,
with each binary PSL₂ and Suzuki model on the literal two-core quotient. -/
theorem exists_componentSeed_with_literal_binary_models
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
        (K.subgroupOf H).Normal ∧
          (let I := (K.subgroupOf H).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore P hP))
           ∃ f : ℕ, 2 ≤ f ∧ ChapterE.generationParameter H ≤ f ∧
             (ClassicalGroup.IsPSU I 3 (2 ^ f) ∨ ClassicalGroup.IsPSL I 3 (2 ^ f) ∨
               ClassicalGroup.IsPSp I 2 (2 ^ f)))) := by
  obtain ⟨K,J,s,hKJ,hJ,hfaith,ho,hm⟩ := exists_componentSeed_with_faithful_maximal h pr hc hs
  refine ⟨K,J,s,hKJ,hJ,hfaith,ho,hm,?_⟩
  by_cases hn : (K.subgroupOf H).Normal
  · rcases s.normal_binary_literal_models h pr hc hs hn with
      ⟨f,hf,hu,hlin,hr⟩ | ⟨m,hm,hu,hsz,hr⟩ | hhigh
    · exact .inl ⟨.inl ⟨f,hf,hu,hlin⟩,hr⟩
    · exact .inl ⟨.inr ⟨m,hm,hu,hsz⟩,hr⟩
    · exact .inr ⟨hn,hhigh⟩
  · exact .inl ⟨s.paired_binary_models h pr hc hs hn,
      s.paired_radical_eq_twoCore h pr hc hs hn⟩

open Representation
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.ChapterB.QuasisimpleSource

/-- Apply the completed field-four case when the original catalogue
initially identifies only the star image. The natural marking and the
preceding 11.0.4 source clauses remain unchanged. -/
theorem ComponentSeed.conclusion_of_star_field_four (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hm : ClassicalGroup.IsPSL
      ((K.subgroupOf H).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore
        (T.subtype h.outside.1.1.2)
        (outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)))))
      2 (2 ^ 2))
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
  exact s.conclusion_of_field_four h pr hc hs
    (s.linear_model_of_star h pr hc hs (by decide) hm) hmark hres hcubic

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
