module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.StarSource
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Containment
public import Theory.Representation.BinaryOffender.Homogeneous.Existence

/-!
# Normalized overcomponents and their actual chosen modules

If the source component K is normal in H, the prescribed Sylow normalizes
K. Unique C-component containment then forces every local overcomponent J
of K to be normalized by that same Sylow. In characteristic two the orbit
of its omega-center lies in R₂(JT). The original movement by K therefore
makes the action of J on this literal reduced subgroup nontrivial.
Perfectness and homogeneous Irr⁺ selection construct a chosen module for J.
No model of J or FF-module conclusion is assumed in this construction.

The counterexample application refines the existing catalogue: its normal
higher-rank rows now carry a normalized faithful maximal overcomponent and
an actual chosen module. If J/O₂(J) is quasisimple, the original ambient
exclusions also supply the precise 12.2.3 hypotheses for this same J.
That quotient hypothesis remains explicit in the latter source adapter.

The embedding and FF-module exclusions, the minimum-parameter recognition,
and unconditional 11.3.5 remain with qt-d-1222-shadow-parameter-component.
The final preceding-source discharge stays with
qt-d-1222-shadow-linear-geometry. This module does not assert 11.3.5.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.3.5(1), pp.771--772; 1.2.4/9, pp.505/507; A.1.40/42 and B.2.14,
pp.31--32 and 78.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K J : Subgroup G}

/-- Relative normality of the seed forces Sylow normalization of each
containing local component, including the faithful maximal choice. -/
theorem ComponentSeed.normal_overcomponent_of_normal (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (hn : (K.subgroupOf H).Normal)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J) :
    (T : Subgroup G) ≤ normalizer (J : Set G) := by
  have hlocal := (Chapter1.Section02.Adequate.mem_L_iff_mainForward T J).mp hJ
  obtain ⟨_,_,_,_,hsq⟩ := MainForward.localComponents_local_setup
    S.source.simpleQTKE T hlocal
  have hsyl : Chapter1.IsSylowIn 2 (T : Subgroup G) (J ⊔ (T : Subgroup G)) :=
    ⟨T.subtype le_sup_right,by
      simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right]⟩
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    h.outside.1.1.2.trans ((normal_subgroupOf_iff_le_normalizer s.component.1).mp hn)
  obtain ⟨C,hC,_,hu⟩ := LocalGeometry.Components.exists_unique_normal_component
    hsq hsyl (hKJ.trans le_sup_left) (s.mem_local_family h) hTK
  have he : J = C := hu J ⟨le_sup_left,hJ.1⟩ hKJ
  have hnormal : (J.subgroupOf (J ⊔ (T : Subgroup G))).Normal := he.symm ▸ hC.2
  exact (show (T : Subgroup G) ≤ J ⊔ (T : Subgroup G) from le_sup_right).trans
    ((normal_subgroupOf_iff_le_normalizer
      (show J ≤ J ⊔ (T : Subgroup G) from le_sup_left)).mp hnormal)

open Chapter12.Section02 Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous

/-- Movement of the original omega-center remains nontrivial on the
literal reduced module of each local overcomponent. -/
theorem ComponentSeed.overcomponent_reduced_commutator_ne_bot
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J) :
    ⁅reducedTwoSubgroup (J ⊔ (T : Subgroup G) : Subgroup G),
      J.subgroupOf (J ⊔ (T : Subgroup G))⁆ ≠ ⊥ := by
  let X := J ⊔ (T : Subgroup G)
  let P := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  have hchar := Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (S.source.simpleQTKE.evenCharacteristic T)
      ⟨hJ.2.2,(show (T : Subgroup G) ≤ J ⊔ (T : Subgroup G) from le_sup_right)⟩)
  have hZ : Stellmacher.omegaOneCenterAmbient (P : Subgroup X) ≤
      reducedTwoSubgroup X := le_normalClosure.trans
        (omegaCenter_normalClosure_reduced P hchar).le_reducedPSubgroup
  have hZimage : (Stellmacher.omegaOneCenterAmbient (P : Subgroup X)).map X.subtype =
      sourceZ T := by
    rw [← Stellmacher.omegaOneCenterAmbient_map_injective X.subtype X.subtype_injective,
      Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right]
    rfl
  have hZR : sourceZ T ≤ (reducedTwoSubgroup X).map X.subtype := by
    rw [←hZimage]
    exact map_mono hZ
  intro he
  apply s.moves_omega_center h
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro z hz k hk
  obtain ⟨v,hv,rfl⟩ := hZR hz
  have hc := commutator_eq_bot_iff_le_centralizer.mp he hv
  exact congrArg X.subtype (hc ⟨k,(show J ≤ X from le_sup_left) (hKJ hk)⟩ (hKJ hk))

/-- In the normal branch homogeneous selection uses the actual reduced
module and the original Sylow, without assuming an overcomponent model. -/
theorem ComponentSeed.exists_chosen_overcomponent_of_normal
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hn : (K.subgroupOf H).Normal)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J) :
    ∃ W : Subgroup G, Nonempty (ChosenModule T J W) := by
  let X := J ⊔ (T : Subgroup G)
  let A := J.subgroupOf X
  have hnorm := s.normal_overcomponent_of_normal h hn hJ hKJ
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le J.le_normalizer hnorm)
  let e : A ≃* J := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect J := Chapter1.mem_L_isPerfect hJ
  let : Group.IsPerfect A :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hnot : ¬ (⊤ : Submodule (ZMod 2) (Additive (ReducedModule X))) ≤
      fixedSpace (reducedRepresentation X) A := by
    intro hf
    apply s.overcomponent_reduced_commutator_ne_bot h hJ hKJ
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro v hv x hx
    have hh := congrArg (fun w : Additive (ReducedModule X) => w.toMul.val)
      (hf (show Additive.ofMul (⟨v, hv⟩ : ReducedModule X) ∈ ⊤ from trivial) ⟨x, hx⟩)
    change x * v * x⁻¹ = v at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  obtain ⟨I,hI⟩ := exists_isIrrPlus_of_not_fixed (reducedRepresentation X) A hnot
  obtain ⟨W,_,hW⟩ := exists_isIrrPlusWith_le_orbitSpan (reducedRepresentation X)
    (show (T : Subgroup G).subgroupOf X ≤ normalizer (A : Set X) from
      le_normalizer_of_normal) T.isPGroup'.comap_subtype hI
  exact ⟨subspaceImage X W,⟨⟨W,hW,rfl⟩⟩⟩

/-- The original normal seed itself admits a chosen module. -/
theorem ComponentSeed.exists_chosen_of_normal (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (hn : (K.subgroupOf H).Normal) :
    ∃ W : Subgroup G, Nonempty (ChosenModule T K W) :=
  s.exists_chosen_overcomponent_of_normal h hn (s.mem_local_family h) le_rfl

/-- Inherit the original ambient exclusions and maximal faithfulness for
the same overcomponent; its own two-core quotient remains explicit. -/
theorem ComponentSeed.overcomponent_source_of_quasisimple (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H)
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    (hq : IsQuasisimple (J ⧸ pCore 2 J)) :
    Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J := by
  have hf := Chapter1.Section02.Adequate.faithful_local_overgroup T
    (S.source.simpleQTKE.evenCharacteristic T) (s.faithful h) hJ.1 hKJ
  exact {
    simpleQTKE := S.source.simpleQTKE
    maximal_faithful := ⟨hJ,hf.2⟩
    quasisimple := hq
    no_rankTwo := S.source.no_rankTwo
    no_M22 := S.source.no_M22
    no_M23 := S.source.no_M23
    no_J4 := S.source.no_J4 }

/-- The normalized maximal overcomponent supplies the literal chosen-module
setup once its own quotient has been proved quasisimple. -/
theorem ComponentSeed.chosen_overcomponent_of_normal (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (hn : (K.subgroupOf H).Normal)
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    (hq : IsQuasisimple (J ⧸ pCore 2 J)) :
    Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
      (T : Subgroup G) ≤ normalizer (J : Set G) ∧
      ∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T J W) := by
  have hs := s.overcomponent_source_of_quasisimple h hJ hKJ hq
  have hnorm := s.normal_overcomponent_of_normal h hn hJ.1 hKJ
  exact ⟨hs,hnorm,s.exists_chosen_overcomponent_of_normal h hn hJ.1 hKJ⟩

/-- In the non-rank-one rows the actual maximal overcomponent is normalized
by the original Sylow and has a constructed chosen module. The low-rank
rows retain their literal quotients. -/
theorem exists_componentSeed_with_normalized_higher_rank_models
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
          (∃ W : Subgroup G, Nonempty (ChosenModule T J W)) ∧
          (let I := (K.subgroupOf H).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore P hP))
           ∃ f : ℕ, 2 ≤ f ∧ ChapterE.generationParameter H ≤ f ∧
             (ClassicalGroup.IsPSU I 3 (2 ^ f) ∨ ClassicalGroup.IsPSL I 3 (2 ^ f) ∨
               ClassicalGroup.IsPSp I 2 (2 ^ f)))) := by
  obtain ⟨K,J,s,hKJ,hJ,hfaith,ho,hm,hcases⟩ :=
    exists_componentSeed_with_literal_binary_models h pr hc hs
  refine ⟨K,J,s,hKJ,hJ,hfaith,ho,hm,?_⟩
  rcases hcases with hlow | ⟨hn,hhigh⟩
  · exact .inl hlow
  · exact .inr ⟨hn,s.normal_overcomponent_of_normal h hn hJ.1 hKJ,
      s.exists_chosen_overcomponent_of_normal h hn hJ.1 hKJ,hhigh⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
