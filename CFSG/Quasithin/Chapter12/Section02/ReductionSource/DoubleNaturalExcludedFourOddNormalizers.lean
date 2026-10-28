module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourModuleExclusion
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourModule
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourStar
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourLinear
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourSymplectic
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourConstrained
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourOuter
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourOuterSporadic
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourOuterG2
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourOuterUnitary
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcludedOddNormalizers

/-!
# The remaining original degree-four odd-normalizer obstructions

Characteristic abelian reduction applies to every original nontrivial odd
subgroup. If its fixed residual has no unique maximal overgroup, reciprocal
escape and the complete ordinary-component exclusions produce a constrained
C.2.8 component with actual star group A₈ or SL₅(2). If the residual is unique, full-orbit placement and the local
model calculation leave an actual GL₄(2) outer section or a normal binary Sp₆
component containing both the residual and the whole doubled orbit.

The literal terminal consumer constructs this alternative from the original
branch and the exact earlier MarkedOmegaFixed premise. The separate strengthened reduction below excludes the constrained A₈ star
and the inner Sp₆(2) case. The constrained SL₅(2) and outer cases still require
exclusion in this owner;
The final parabolic reduction identifies the literal SL₅(2) star intersection
and the original residual's full Levi action. The outer-model reduction excludes
the alternating and shared C rows, odd PSL₃/PSU₃ and PSp₄, binary PSU₄,
and Fermat PSL₄, retaining
six actual central-quotient families in the preserved interface. The final
reduced interface also excludes Mersenne PSU₄. The final symplectic inspection
excludes Sp₆(2). The J₃, McL and odd-prime G₂ inspections leave only the
actual PSU₅(4) outer family and the constrained SL₅(2) star in their preserved
interfaces. The final fourth-power calculation excludes PSU₅(4), leaving only
the same original constrained SL₅(2) star.
The module refinement places the original residual in K and embeds the doubled
orbit in the actual classified moved central quotient. The final exclusion applies the original residual action and radical-fixed
embedding to every B.5.1 row. This proves degree-four odd-normalizer control
and the four/five-degree terminal exclusion with only the genuine degree-four
MarkedOmegaFixed premise. Its discharge remains with the existing pure-fusion/MS
producers; the unconditional degree-four 12.1.11 theorem is not asserted.
Source: Aschbacher--Smith 4.2.13, 4.4.3--12 and 12.1.9, pp.612,619--623,793.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Chapter1.RadicalExclusions.ModelReduction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)

/-- The surviving source alternatives retain literal ambient groups and quotient maps. -/
@[expose] def FourOddNormalizerCases (T : Sylow 2 G) (L V A : Subgroup G) : Prop :=
  (∃ J H U : Subgroup G, Witness L V A J H U ∧
      componentOrbit V (T : Subgroup G) ≤ U ∧
      componentOrbit V (T : Subgroup G) ≤ J.pCoreIn 2 ∧
      ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
        generalizedFitting K = pCore 2 K ∧
        FourConstrainedModels (K.map H.subtype) (J.pCoreIn 2)) ∨
  (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K,(componentOrbit V (T : Subgroup G)).subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧
      ((∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinear.OuterCyclic.LinearGroup 4,
        Function.Surjective f) ∨
       (K.Normal ∧ componentOrbit V (T : Subgroup G) ≤ K.map (normalizer (A : Set G)).subtype ∧
        oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
        ClassicalGroup.IsPSp (K ⧸ center K) 3 2)))

include D h in
/-- Every failed odd-normalizer containment yields these actual reduced alternatives. -/
theorem doubledFour_oddNormalizer_reduced_obstruction_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4)
    (hnot : ¬ OddNormalizerControl (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G))) :
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧ FourOddNormalizerCases T L V A := by
  classical
  obtain ⟨X,A,_,hcomm,hne,ho,hA,_,hout⟩ := exists_abelian_of_not_oddNormalizerControl hnot
  let := hcomm
  refine ⟨A.map X.subtype,hne,hcomm,ho,hA,hout,?_⟩
  by_cases hu : UniqueMaximalOvergroup (oddActorResidual L (A.map X.subtype)) (normalizer (L : Set G))
  · apply Or.inr
    have hcore := (oddNormalizer_reduction_of_cover_uniqueness D (A.map X.subtype) hu hout).2
    obtain ⟨K,hK,hm,houtK,hcoreK,hqt,_,_,_⟩ :=
      D.doubledOrbit_oddNormalizer_full_component h B _ hne hA ho hcore
    refine ⟨hu,K,hK,hm,houtK,hcoreK,?_⟩
    rcases D.doubledOrbit_oddNormalizer_inner_or_outer_section h B _ hA ho K hK with hi | he
    · let : IsQuasisimple K := hK.2
      have hkg : IsKGroup KnownSimple.IsKnownSimple K :=
        ((oddNormalizer_properQTK h.simpleQTKE _ hne).2.2).subgroup K
      have hmodel := ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
        ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple hqt hkg
      exact Or.inr (D.doubledFour_oddNormalizer_inner_symplectic_of_many h hmany B _ hA ho hu
        hout K hK houtK hi hmodel)
    · exact Or.inl he
  · exact Or.inl (D.doubledFour_pushingUp_two_linear_models_of_many h hmany B _ hA ho hu)

include D h in
/-- The original degree-four branch and the exact earlier omega premise
force one of the remaining concrete source obstructions, without an odd-control callback. -/
theorem doubledFour_refinedOddNormalizer_counterexample_of_many_of_omega_fixed
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    (∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component) →
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧ FourOddNormalizerCases T L V A := by
  let := D.doubledOrbit_elementary h
  intro hfixed
  apply D.doubledFour_oddNormalizer_reduced_obstruction_of_many h hmany B
  intro hodd
  exact D.doubleNatural_four_excluded_of_many_of_omega_fixed_of_odd_control h hmany B hodd hfixed


open scoped MatrixGroups
/-- The remaining degree-four obstructions: the literal SL₅(2) constrained star,
or the original GL₄(2) section in the full outer automorphism quotient. -/
@[expose] def FourOddNormalizerLinearOuterCases (T : Sylow 2 G) (L V A : Subgroup G) : Prop :=
  (∃ J H U : Subgroup G, Witness L V A J H U ∧
      componentOrbit V (T : Subgroup G) ≤ U ∧
      componentOrbit V (T : Subgroup G) ≤ J.pCoreIn 2 ∧
      ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
        generalizedFitting K = pCore 2 K ∧
        Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃* SL(5,ZMod 2))) ∨
  (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K,(componentOrbit V (T : Subgroup G)).subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧
      ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinear.OuterCyclic.LinearGroup 4,
        Function.Surjective f)

include D h in
/-- Exclude the A₈ constrained star and every inner ordinary component for
the actual arbitrary odd-normalizer counterexample. -/
theorem doubledFour_oddNormalizer_linear_outer_obstruction_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4)
    (hnot : ¬ OddNormalizerControl (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G))) :
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      FourOddNormalizerLinearOuterCases T L V A := by
  classical
  obtain ⟨X,A,_,hcomm,hne,ho,hA,_,hout⟩ := exists_abelian_of_not_oddNormalizerControl hnot
  let := hcomm
  refine ⟨A.map X.subtype,hne,hcomm,ho,hA,hout,?_⟩
  by_cases hu : UniqueMaximalOvergroup (oddActorResidual L (A.map X.subtype)) (normalizer (L : Set G))
  · apply Or.inr
    have hcore := (oddNormalizer_reduction_of_cover_uniqueness D (A.map X.subtype) hu hout).2
    obtain ⟨K,hK,hm,houtK,hcoreK,hqt,_,_,_⟩ :=
      D.doubledOrbit_oddNormalizer_full_component h B _ hne hA ho hcore
    let : IsQuasisimple K := hK.2
    have hkg : IsKGroup KnownSimple.IsKnownSimple K :=
      ((oddNormalizer_properQTK h.simpleQTKE _ hne).2.2).subgroup K
    have hmodel := ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
      ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple hqt hkg
    exact ⟨hu,K,hK,hm,houtK,hcoreK,
      D.doubledFour_oddNormalizer_outer_of_unique_of_many h hmany B _ hA ho hu hout K hK houtK hmodel⟩
  · exact Or.inl (D.doubledFour_pushingUp_linear_five_of_many h hmany B _ hA ho hu)

include D h in
/-- The actual degree-four terminal consumer retains only the two remaining
odd-normalizer branches and the genuine earlier marked-omega premise. -/
theorem doubledFour_linearOuter_counterexample_of_many_of_omega_fixed
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    (∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component) →
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      FourOddNormalizerLinearOuterCases T L V A := by
  let := D.doubledOrbit_elementary h
  intro hfixed
  apply D.doubledFour_oddNormalizer_linear_outer_obstruction_of_many h hmany B
  intro hodd
  exact D.doubleNatural_four_excluded_of_many_of_omega_fixed_of_odd_control h hmany B hodd hfixed

/-- The constrained alternative retains its actual endpoint parabolic and
compatible full Levi action; the other alternative is the literal outer section. -/
@[expose] def FourOddNormalizerParabolicOuterCases (T : Sylow 2 G) (L V A : Subgroup G) : Prop :=
  (∃ (J H U : Subgroup G) (hw : Witness L V A J H U),
      componentOrbit V (T : Subgroup G) ≤ U ∧
      componentOrbit V (T : Subgroup G) ≤ J.pCoreIn 2 ∧
      FourPushingUpParabolic L V A J H U hw) ∨
  (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K,(componentOrbit V (T : Subgroup G)).subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧
      ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinear.OuterCyclic.LinearGroup 4,
        Function.Surjective f)

include D h in
/-- Every original odd-normalizer counterexample yields a marked parabolic
with full residual Levi action or an actual outer section. -/
theorem doubledFour_oddNormalizer_parabolic_outer_obstruction_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4)
    (hnot : ¬ OddNormalizerControl (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G))) :
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      FourOddNormalizerParabolicOuterCases T L V A := by
  obtain ⟨A,hne,hcomm,ho,hA,hout,hcases⟩ :=
    D.doubledFour_oddNormalizer_linear_outer_obstruction_of_many h hmany B hnot
  refine ⟨A,hne,hcomm,ho,hA,hout,?_⟩
  rcases hcases with hc | ho
  · obtain ⟨J,H,U,hw,hWU,hWJ,K,hK,hq,houtK,hfK,⟨e⟩⟩ := hc
    exact Or.inl ⟨J,H,U,hw,hWU,hWJ,doubledFour_witness_parabolic B hw K hK hq houtK hfK e⟩
  · exact Or.inr ho

include D h in
/-- The terminal degree-four implication uses the same original branch and
exact earlier omega premise, retaining both remaining source exclusions. -/
theorem doubledFour_parabolicOuter_counterexample_of_many_of_omega_fixed
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    (∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component) →
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      FourOddNormalizerParabolicOuterCases T L V A := by
  let := D.doubledOrbit_elementary h
  intro hfixed
  apply D.doubledFour_oddNormalizer_parabolic_outer_obstruction_of_many h hmany B
  intro hodd
  exact D.doubleNatural_four_excluded_of_many_of_omega_fixed_of_odd_control h hmany B hodd hfixed

/-- A counterexample keeps the original marked parabolic or a full outer
section on one of the six remaining actual component models. -/
@[expose] def FourOddNormalizerParabolicModelCases (T : Sylow 2 G)
    (L V A : Subgroup G) : Prop :=
  (∃ (J H U : Subgroup G) (hw : Witness L V A J H U),
      componentOrbit V (T : Subgroup G) ≤ U ∧
      componentOrbit V (T : Subgroup G) ≤ J.pCoreIn 2 ∧
      FourPushingUpParabolic L V A J H U hw) ∨
  (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K,(componentOrbit V (T : Subgroup G)).subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ FourRemainingOuterModel (K ⧸ center K) ∧
      ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinear.OuterCyclic.LinearGroup 4,
        Function.Surjective f)

include D h in
/-- Apply the full B-model inspection to the original odd-normalizer witness.
Its nontrivial abelian odd actor supplies the proper QTK ambient group. -/
theorem doubledFour_oddNormalizer_parabolic_models_obstruction_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4)
    (hnot : ¬ OddNormalizerControl (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G))) :
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      FourOddNormalizerParabolicModelCases T L V A := by
  obtain ⟨A,hne,hcomm,ho,hA,hout,hcases⟩ :=
    D.doubledFour_oddNormalizer_parabolic_outer_obstruction_of_many h hmany B hnot
  refine ⟨A,hne,hcomm,ho,hA,hout,?_⟩
  rcases hcases with hp | ⟨hu,K,hK,hm,houtK,hcore,he⟩
  · exact Or.inl hp
  · let := hcomm
    let := hK.2
    obtain ⟨_,hqt,hkg⟩ := oddNormalizer_properQTK h.simpleQTKE A hne
    have hmodel := ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
      ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple
      (hqt.subgroup K) (hkg.subgroup K)
    exact Or.inr ⟨hu,K,hK,hm,houtK,hcore,four_remaining_outer_models hmodel he,he⟩

include D h in
/-- The same literal terminal implication now retains only the marked
constrained star and six genuine outer-model families. The earlier omega
premise is unchanged and still belongs to its independent source producers. -/
theorem doubledFour_parabolicModels_counterexample_of_many_of_omega_fixed
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    (∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component) →
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      FourOddNormalizerParabolicModelCases T L V A := by
  let := D.doubledOrbit_elementary h
  intro hfixed
  apply D.doubledFour_oddNormalizer_parabolic_models_obstruction_of_many h hmany B
  intro hodd
  exact D.doubleNatural_four_excluded_of_many_of_omega_fixed_of_odd_control h hmany B hodd hfixed

/-- After excluding Mersenne PSU₄, the same original witness retains only
its constrained star or five actual outer-section families. -/
@[expose] def FourOddNormalizerParabolicReducedModelCases (T : Sylow 2 G)
    (L V A : Subgroup G) : Prop :=
  (∃ (J H U : Subgroup G) (hw : Witness L V A J H U),
      componentOrbit V (T : Subgroup G) ≤ U ∧
      componentOrbit V (T : Subgroup G) ≤ J.pCoreIn 2 ∧
      FourPushingUpParabolic L V A J H U hw) ∨
  (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K,(componentOrbit V (T : Subgroup G)).subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ FourReducedOuterModel (K ⧸ center K) ∧
      ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinear.OuterCyclic.LinearGroup 4,
        Function.Surjective f)

include D h in
/-- The Mersenne exclusion applies to every failed original odd-normalizer
containment after the actual nontrivial abelian reduction. -/
theorem doubledFour_oddNormalizer_parabolic_reduced_models_obstruction_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4)
    (hnot : ¬ OddNormalizerControl (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G))) :
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      FourOddNormalizerParabolicReducedModelCases T L V A := by
  obtain ⟨A,hne,hcomm,ho,hA,hout,hcases⟩ :=
    D.doubledFour_oddNormalizer_parabolic_outer_obstruction_of_many h hmany B hnot
  refine ⟨A,hne,hcomm,ho,hA,hout,?_⟩
  rcases hcases with hp | ⟨hu,K,hK,hm,houtK,hcore,he⟩
  · exact Or.inl hp
  · let := hcomm
    let := hK.2
    obtain ⟨_,hqt,hkg⟩ := oddNormalizer_properQTK h.simpleQTKE A hne
    have hmodel := ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
      ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple
      (hqt.subgroup K) (hkg.subgroup K)
    exact Or.inr ⟨hu,K,hK,hm,houtK,hcore,four_reduced_outer_models hmodel he,he⟩

include D h in
/-- The original terminal implication keeps the exact ambient marked-omega
premise and now has only the five remaining outer families and constrained star. -/
theorem doubledFour_parabolicReducedModels_counterexample_of_many_of_omega_fixed
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    (∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component) →
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      FourOddNormalizerParabolicReducedModelCases T L V A := by
  let := D.doubledOrbit_elementary h
  intro hfixed
  apply D.doubledFour_oddNormalizer_parabolic_reduced_models_obstruction_of_many h hmany B
  intro hodd
  exact D.doubleNatural_four_excluded_of_many_of_omega_fixed_of_odd_control h hmany B hodd hfixed

/-- After excluding binary Sp₆, the same original witness retains only
its constrained star or four actual outer-section families. -/
@[expose] def FourOddNormalizerParabolicNonsymplecticModelCases (T : Sylow 2 G)
    (L V A : Subgroup G) : Prop :=
  (∃ (J H U : Subgroup G) (hw : Witness L V A J H U),
      componentOrbit V (T : Subgroup G) ≤ U ∧
      componentOrbit V (T : Subgroup G) ≤ J.pCoreIn 2 ∧
      FourPushingUpParabolic L V A J H U hw) ∨
  (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K,(componentOrbit V (T : Subgroup G)).subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ FourNonsymplecticOuterModel (K ⧸ center K) ∧
      ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinear.OuterCyclic.LinearGroup 4,
        Function.Surjective f)

include D h in
/-- The binary symplectic exclusion applies to every failed original odd-normalizer
containment after the actual nontrivial abelian reduction. -/
theorem doubledFour_oddNormalizer_parabolic_nonsymplectic_models_obstruction_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4)
    (hnot : ¬ OddNormalizerControl (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G))) :
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      FourOddNormalizerParabolicNonsymplecticModelCases T L V A := by
  obtain ⟨A,hne,hcomm,ho,hA,hout,hcases⟩ :=
    D.doubledFour_oddNormalizer_parabolic_reduced_models_obstruction_of_many h hmany B hnot
  refine ⟨A,hne,hcomm,ho,hA,hout,?_⟩
  rcases hcases with hp | ⟨hu,K,hK,hm,houtK,hcore,hmodel,he⟩
  · exact Or.inl hp
  · let := hK.2
    exact Or.inr ⟨hu,K,hK,hm,houtK,hcore,four_nonsymplectic_outer_models hmodel he,he⟩

include D h in
/-- The original terminal implication keeps the exact ambient marked-omega
premise and now has only the four remaining outer families and constrained star. -/
theorem doubledFour_parabolicNonsymplecticModels_counterexample_of_many_of_omega_fixed
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    (∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component) →
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      FourOddNormalizerParabolicNonsymplecticModelCases T L V A := by
  let := D.doubledOrbit_elementary h
  intro hfixed
  apply D.doubledFour_oddNormalizer_parabolic_nonsymplectic_models_obstruction_of_many h hmany B
  intro hodd
  exact D.doubleNatural_four_excluded_of_many_of_omega_fixed_of_odd_control h hmany B hodd hfixed

/-- After excluding J₃ and McL, the same original witness retains only
its constrained star or two actual outer-section families. -/
@[expose] def FourOddNormalizerParabolicLieModelCases (T : Sylow 2 G)
    (L V A : Subgroup G) : Prop :=
  (∃ (J H U : Subgroup G) (hw : Witness L V A J H U),
      componentOrbit V (T : Subgroup G) ≤ U ∧
      componentOrbit V (T : Subgroup G) ≤ J.pCoreIn 2 ∧
      FourPushingUpParabolic L V A J H U hw) ∨
  (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K,(componentOrbit V (T : Subgroup G)).subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ FourLieOuterModel (K ⧸ center K) ∧
      ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinear.OuterCyclic.LinearGroup 4,
        Function.Surjective f)

include D h in
/-- The J₃ and McL exclusions apply to every failed original odd-normalizer
containment after the actual nontrivial abelian reduction. -/
theorem doubledFour_oddNormalizer_parabolic_lie_models_obstruction_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4)
    (hnot : ¬ OddNormalizerControl (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G))) :
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      FourOddNormalizerParabolicLieModelCases T L V A := by
  obtain ⟨A,hne,hcomm,ho,hA,hout,hcases⟩ :=
    D.doubledFour_oddNormalizer_parabolic_nonsymplectic_models_obstruction_of_many h hmany B hnot
  refine ⟨A,hne,hcomm,ho,hA,hout,?_⟩
  rcases hcases with hp | ⟨hu,K,hK,hm,houtK,hcore,hmodel,he⟩
  · exact Or.inl hp
  · let := hK.2
    exact Or.inr ⟨hu,K,hK,hm,houtK,hcore,four_lie_outer_models hmodel he,he⟩

include D h in
/-- The original terminal implication keeps the exact ambient marked-omega
premise and now has only the two remaining outer families and constrained star. -/
theorem doubledFour_parabolicLieModels_counterexample_of_many_of_omega_fixed
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    (∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component) →
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      FourOddNormalizerParabolicLieModelCases T L V A := by
  let := D.doubledOrbit_elementary h
  intro hfixed
  apply D.doubledFour_oddNormalizer_parabolic_lie_models_obstruction_of_many h hmany B
  intro hodd
  exact D.doubleNatural_four_excluded_of_many_of_omega_fixed_of_odd_control h hmany B hodd hfixed

/-- After excluding odd-prime G₂, the same original witness retains only
its constrained SL₅(2) star or the actual PSU₅(4) outer section. -/
@[expose] def FourOddNormalizerParabolicUnitaryModelCases (T : Sylow 2 G)
    (L V A : Subgroup G) : Prop :=
  (∃ (J H U : Subgroup G) (hw : Witness L V A J H U),
      componentOrbit V (T : Subgroup G) ≤ U ∧
      componentOrbit V (T : Subgroup G) ≤ J.pCoreIn 2 ∧
      FourPushingUpParabolic L V A J H U hw) ∨
  (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K,(componentOrbit V (T : Subgroup G)).subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ ClassicalGroup.IsPSU (K ⧸ center K) 5 4 ∧
      ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinear.OuterCyclic.LinearGroup 4,
        Function.Surjective f)

include D h in
/-- The odd-prime G₂ exclusion applies to every failed original odd-normalizer
containment after the actual nontrivial abelian reduction. -/
theorem doubledFour_oddNormalizer_parabolic_unitary_model_obstruction_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4)
    (hnot : ¬ OddNormalizerControl (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G))) :
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      FourOddNormalizerParabolicUnitaryModelCases T L V A := by
  obtain ⟨A,hne,hcomm,ho,hA,hout,hcases⟩ :=
    D.doubledFour_oddNormalizer_parabolic_lie_models_obstruction_of_many h hmany B hnot
  refine ⟨A,hne,hcomm,ho,hA,hout,?_⟩
  rcases hcases with hp | ⟨hu,K,hK,hm,houtK,hcore,hmodel,he⟩
  · exact Or.inl hp
  · let := hK.2
    exact Or.inr ⟨hu,K,hK,hm,houtK,hcore,four_outer_model_unitary_five hmodel he,he⟩

include D h in
/-- The original terminal implication keeps the exact ambient marked-omega
premise and now has only the actual PSU₅(4) outer section and constrained SL₅(2) star. -/
theorem doubledFour_parabolicUnitaryModel_counterexample_of_many_of_omega_fixed
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    (∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component) →
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      FourOddNormalizerParabolicUnitaryModelCases T L V A := by
  let := D.doubledOrbit_elementary h
  intro hfixed
  apply D.doubledFour_oddNormalizer_parabolic_unitary_model_obstruction_of_many h hmany B
  intro hodd
  exact D.doubleNatural_four_excluded_of_many_of_omega_fixed_of_odd_control h hmany B hodd hfixed

include D h in
/-- Every failed original odd-normalizer containment now yields the actual
constrained SL₅(2) star; all original outer-section families are excluded. -/
theorem doubledFour_oddNormalizer_constrained_parabolic_obstruction_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4)
    (hnot : ¬ OddNormalizerControl (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G))) :
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      ∃ (J H U : Subgroup G) (hw : Witness L V A J H U),
        componentOrbit V (T : Subgroup G) ≤ U ∧
        componentOrbit V (T : Subgroup G) ≤ J.pCoreIn 2 ∧
        FourPushingUpParabolic L V A J H U hw := by
  obtain ⟨A,hne,hcomm,ho,hA,hout,hcases⟩ :=
    D.doubledFour_oddNormalizer_parabolic_lie_models_obstruction_of_many h hmany B hnot
  refine ⟨A,hne,hcomm,ho,hA,hout,?_⟩
  rcases hcases with hp | ⟨_,K,hK,_,_,_,hmodel,he⟩
  · exact hp
  · let := hK.2
    exact (four_lie_outer_model_exclusion hmodel he).elim

include D h in
/-- The terminal original degree-four implication retains the exact ambient
marked-omega premise and only the constrained SL₅(2) alternative. -/
theorem doubledFour_constrainedParabolic_counterexample_of_many_of_omega_fixed
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    (∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component) →
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      ∃ (J H U : Subgroup G) (hw : Witness L V A J H U),
        componentOrbit V (T : Subgroup G) ≤ U ∧
        componentOrbit V (T : Subgroup G) ≤ J.pCoreIn 2 ∧
        FourPushingUpParabolic L V A J H U hw := by
  let := D.doubledOrbit_elementary h
  intro hfixed
  apply D.doubledFour_oddNormalizer_constrained_parabolic_obstruction_of_many h hmany B
  intro hodd
  exact D.doubleNatural_four_excluded_of_many_of_omega_fixed_of_odd_control h hmany B hodd hfixed

open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open BinaryLinear.OuterCyclic

/-- The same original marked parabolic, with its doubled module embedded in
its classified moved section and central quotient. -/
@[expose] def FourPushingUpModule
    {T : Sylow 2 G} {L V A : Subgroup G} (B : DoubledBranch T L V 4)
    (J H U : Subgroup G) (hw : Witness L V A J H U) : Prop :=
  ∃ (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
      (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
      (hfK : generalizedFitting K = pCore 2 K)
      (e : starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃* SL(5,ZMod 2)),
    (let hc := hw.2.2.2.2.2.2.1
     let hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp hw.2.2.2.2.2.2.2.2.1
     let a := doubledFour_constrained_five_coordinates hc K hK hq hout hfK e
     let P := (coreCentralIntersectionImage K ((J.pCoreIn 2).subgroupOf H)).map a.toMonoidHom
     let N := normalizer (P : Set (LinearGroup 5))
     let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
     K.Normal ∧ IsPRadical 2 P ∧ Nat.card P = 16 ∧
       (∃ (b : BinaryLinear.FiveFlagGeometry.FiveBasis) (i : Fin 4),
         (i = 0 ∨ i = 3) ∧ N = BinaryLinear.FiveFlagGeometry.flagStabilizer b {i}) ∧
       ((starM (K.map H.subtype) (J.pCoreIn 2) (H ⊓ normalizer (L : Set G))).subgroupOf
         (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype))).map
         (e.trans (slEquivLinear 5)).toMonoidHom = N ∧
       ∃ r : F →* N, Group.IsSolvable r.ker ∧
         (∀ x : F, MulAut.conj (r x : LinearGroup 5) =
           MulAut.congr a (doubledFour_normalized_actor hc hn K hK hq x)) ∧
         Function.Surjective ((QuotientGroup.mk' (pCore 2 N)).comp r)) ∧
      ∃ d : FourStarModuleCoordinates B J H K, d.Classified

include D h in
/-- Apply the residual containment and marked module embedding to the
original odd-normalizer counterexample. All parabolic coordinates are retained. -/
theorem doubledFour_oddNormalizer_constrained_module_obstruction_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4)
    (hnot : ¬ OddNormalizerControl (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G))) :
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      ∃ (J H U : Subgroup G) (hw : Witness L V A J H U),
        componentOrbit V (T : Subgroup G) ≤ U ∧
        componentOrbit V (T : Subgroup G) ≤ J.pCoreIn 2 ∧
        FourPushingUpModule B J H U hw := by
  obtain ⟨A,hne,hcomm,ho,hA,hout,J,H,U,hw,hWU,hWJ,K,hK,hq,houtK,hfK,e,hpar⟩ :=
    D.doubledFour_oddNormalizer_constrained_parabolic_obstruction_of_many h hmany B hnot
  exact ⟨A,hne,hcomm,ho,hA,hout,J,H,U,hw,hWU,hWJ,K,hK,hq,houtK,hfK,e,hpar,
    D.doubledFour_witness_classified_star_module h B hw hWU K hK hq houtK hfK e⟩

include D h in
/-- The terminal degree-four counterexample retains the exact ambient omega
premise and now carries the original module in its classified star section. -/
theorem doubledFour_constrainedModule_counterexample_of_many_of_omega_fixed
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    (∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component) →
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsMulCommutative A ∧ Odd (Nat.card A) ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      ∃ (J H U : Subgroup G) (hw : Witness L V A J H U),
        componentOrbit V (T : Subgroup G) ≤ U ∧
        componentOrbit V (T : Subgroup G) ≤ J.pCoreIn 2 ∧
        FourPushingUpModule B J H U hw := by
  let := D.doubledOrbit_elementary h
  intro hfixed
  apply D.doubledFour_oddNormalizer_constrained_module_obstruction_of_many h hmany B
  intro hodd
  exact D.doubleNatural_four_excluded_of_many_of_omega_fixed_of_odd_control h hmany B hodd hfixed


/-- The last original constrained alternative is impossible. The literal
radical has order sixteen and fixes the original embedded doubled module. -/
theorem fourPushingUpModule_false
    (B : DoubledBranch T L V 4) {A J H U : Subgroup G}
    (hw : Witness L V A J H U) (hm : FourPushingUpModule B J H U hw) : False := by
  obtain ⟨K,hK,hq,hout,hfK,e,hpar,d,hd⟩ := hm
  have hc := hw.2.2.2.2.2.2.1
  have hcard := hpar.2.2.1
  rw [doubledFour_constrained_five_intersection hc K hK hq hout hfK e,
    card_map_of_injective (e.trans (slEquivLinear 5)).injective] at hcard
  exact d.not_classified_of_radical_card e hcard hd

include D h in
/-- Source 12.1.9(1) in degree four: every nontrivial odd subgroup in the
original normalizer centralizing the whole orbit has its normalizer there. -/
theorem doubledFour_oddNormalizerControl_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    OddNormalizerControl (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G)) := by
  by_contra hnot
  obtain ⟨A,_,_,_,_,_,J,H,U,hw,_,_,hm⟩ :=
    D.doubledFour_oddNormalizer_constrained_module_obstruction_of_many h hmany B hnot
  exact fourPushingUpModule_false B hw hm

include D h in
/-- Degree four in 12.1.11, with all odd-normalizer, escaping-actor and
weak-closure obligations discharged. Only the earlier ambient omega premise remains. -/
theorem doubleNatural_four_excluded_of_many_of_omega_fixed
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    (∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component) → False := by
  exact D.doubleNatural_four_excluded_of_many_of_omega_fixed_of_odd_control h hmany B
    (D.doubledFour_oddNormalizerControl_of_many h hmany B)

include D h in
/-- Both original degrees in 12.1.11. The exact ambient omega premise is
needed only in degree four and remains with the existing pure-point/MS producer. -/
theorem doubleNatural_excluded_of_many_of_omega_fixed
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    (n = 4 → ∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component) → False := by
  let := D.doubledOrbit_elementary h
  intro hfixed
  rcases hn with rfl | rfl
  · exact D.doubleNatural_four_excluded_of_many_of_omega_fixed h hmany B (hfixed rfl)
  · exact D.doubleNatural_five_excluded_of_many h hmany B

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
