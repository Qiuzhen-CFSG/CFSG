module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherComponentImages
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherTensor
public import Theory.GroupTheory.CComponent.LocalImageEquality
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryLinear
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SmallAlternating
public import Theory.SpecificGroups.PSL3Two.SolvableSylowOvergroups

/-!
# Non-enlargement for the ordinary containing images in 12.2.25

The actual Y-image in N_G(R)/R is quasisimple and is a local C-component
for the image of the original full Sylow. The proper-Sylow-overgroup
calculations in binary degrees four and five therefore force equality
with a binary-linear containing image. Solvability gives the degree-three
case and the small alternating cases. Equality lifts through the literal
quotient because R lies in T; it does not assume Y is subnormal in N_G(R).

The source chain now excludes these images whenever Y<Y_R. In the
binary-linear branch, equality immediately supplies residual normality
and feeds the existing dimension, rigidity and actual parabolic-complement
consumer. The catalogue placing the containing image in these rows or the
exceptional rows, the SL₂(7)/E₄₉ exclusion and marked A₇ recognition remain
with qt-d-12213-local-rigidity. No completion of 12.2.25–26 is asserted.

Source: Aschbacher–Smith, original 12.2.25, printed pp.805–806, using
A.3.11–12. Imported model calculations retain their ATLAS attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- Equality in the literal radical quotient lifts to the original subgroups. -/
theorem residual_eq_containing_of_image_eq
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (he : ThreeRigidity.image T U (rigidityHyperplaneResidual L U V) =
      ThreeRigidity.image T U K) : rigidityHyperplaneResidual L U V = K := by
  let R := sectionRadical T U
  let N := normalizer (R : Set G)
  let S := T.subtype (sylow_normalizes_sectionRadical C)
  have hlocal : (rigidityHyperplaneResidual L U V).subgroupOf N ∈ Chapter1.L N S :=
    (Chapter1.mem_LIn_iff_subgroupOf (sylow_normalizes_sectionRadical C)
      B.residual_normalizes).mp
      ⟨B.residual_normalizes,residual_mem_local_family D A C hd
        (((structural G T L h).2.2 V D).1)⟩
  have hh := local_cComponent_eq_of_map_eq hlocal.1 hK (comap_mono hYK)
    (quotient R) (show (quotient R).ker ≤ (S : Subgroup N) from by
      change (QuotientGroup.mk' (R.subgroupOf N)).ker ≤ _
      rw [QuotientGroup.ker_mk']
      exact comap_mono (show R ≤ (T : Subgroup G) from inf_le_left)) he
  have hm := congrArg (map N.subtype) hh
  change ((rigidityHyperplaneResidual L U V).subgroupOf N).map N.subtype =
    (K.subgroupOf N).map N.subtype at hm
  rw [map_subgroupOf_eq_of_le (show rigidityHyperplaneResidual L U V ≤ N from B.residual_normalizes),
    map_subgroupOf_eq_of_le (show K ≤ N from hKN)] at hm
  exact hm

/-- A containing image of binary linear degree three, four or five forces
equality. The larger binary parabolics cannot contain this quasisimple image. -/
theorem residual_eq_containing_of_binary_linear_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    {m : ℕ} (hm : m = 3 ∨ m = 4 ∨ m = 5)
    (hmodel : ClassicalGroup.IsPSL (ThreeRigidity.image T U K) m 2) :
    rigidityHyperplaneResidual L U V = K := by
  let R := sectionRadical T U
  let N := normalizer (R : Set G)
  let S : Sylow 2 (NormalizerQuotient R) :=
    (T.subtype (sylow_normalizes_sectionRadical C)).mapSurjective
      (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable (R.subgroupOf N) := by
    let : Group.IsNilpotent (R.subgroupOf N) :=
      ((T.isPGroup'.to_le (show R ≤ (T : Subgroup G) from inf_le_left)).comap_subtype).isNilpotent
    infer_instance
  have hKbar : (ThreeRigidity.image T U K).IsCComponent := hK.map_quotient (R.subgroupOf N)
  have hBbar := residual_image_local h D structural A C B hd
  let := residual_image_quasisimple h D structural A C B hd
  have hle : ThreeRigidity.image T U (rigidityHyperplaneResidual L U V) ≤
      ThreeRigidity.image T U K := map_mono (comap_mono hYK)
  apply residual_eq_containing_of_image_eq h D structural A C B hd hKN hK hYK
  rcases hm with rfl | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
    exact ChapterA.Section03.SourceEmbeddings.eq_of_solvable_sylow_overgroups
      S hBbar hKbar hle (SolvableSylowOvergroups.of_equiv e
        (Matrix.PSL3Two.solvableSylowOvergroups_projective_of_card_two hF))
  · exact ChapterA.Section03.SourceEmbeddings.eq_of_binary_linear_four_or_five
      S hBbar hKbar hle hm hmodel

/-- The A₅, A₆ and central-cover A₆ images have the same non-enlargement property. -/
theorem residual_eq_containing_of_small_alternating_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hmodel : Chapter1.Section02.LocalModels.IsAlternating (ThreeRigidity.image T U K) 5 ∨
      Chapter1.Section02.LocalModels.IsAlternating (ThreeRigidity.image T U K) 6 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover (ThreeRigidity.image T U K) 6) :
    rigidityHyperplaneResidual L U V = K := by
  let R := sectionRadical T U
  let N := normalizer (R : Set G)
  let S : Sylow 2 (NormalizerQuotient R) :=
    (T.subtype (sylow_normalizes_sectionRadical C)).mapSurjective
      (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable (R.subgroupOf N) := by
    let : Group.IsNilpotent (R.subgroupOf N) :=
      ((T.isPGroup'.to_le (show R ≤ (T : Subgroup G) from inf_le_left)).comap_subtype).isNilpotent
    infer_instance
  apply residual_eq_containing_of_image_eq h D structural A C B hd hKN hK hYK
  exact ChapterA.Section03.SourceEmbeddings.eq_of_small_alternating_containing_component S
    (residual_image_local h D structural A C B hd) (hK.map_quotient (R.subgroupOf N))
    (map_mono (comap_mono hYK)) hmodel

/-- The actual source chain, with the ordinary small images excluded whenever
its normal containing component properly contains the original residual. -/
theorem source_containing_component_sieve
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d) :
    ∃ K K₀ : Subgroup G,
      K ≤ normalizer (sectionRadical T U : Set G) ∧
      (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent ∧
      rigidityHyperplaneResidual L U V ≤ K ∧
      normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G) ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧ K ≤ K₀ ∧ FaithfulMaximalLocal T K₀ ∧
      (rigidityHyperplaneResidual L U V ≠ K →
        (∀ m, (m = 3 ∨ m = 4 ∨ m = 5) →
          ¬ ClassicalGroup.IsPSL (ThreeRigidity.image T U K) m 2) ∧
        ¬ (Chapter1.Section02.LocalModels.IsAlternating (ThreeRigidity.image T U K) 5 ∨
          Chapter1.Section02.LocalModels.IsAlternating (ThreeRigidity.image T U K) 6 ∨
          Chapter1.Section02.LocalModels.IsAlternatingCover (ThreeRigidity.image T U K) 6)) := by
  obtain ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀⟩ :=
    source_containing_component_chain h D structural A C hnone hd
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  refine ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀,?_⟩
  intro hne
  exact ⟨fun m hm hmodel => hne
    (residual_eq_containing_of_binary_linear_image h D structural A C B hd hKN hK hYK hm hmodel),
    fun hmodel => hne
      (residual_eq_containing_of_small_alternating_image h D structural A C B hd hKN hK hYK hmodel)⟩

/-- A binary-linear image of the actual normal containing component now
feeds the original rigidity and parabolic-complement conclusion directly.
Only the containing-image model is still an earlier step in this branch. -/
theorem source_rigidity_of_binary_linear_containing_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hn : normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G))
    {m : ℕ} (hm : m = 3 ∨ m = 4 ∨ m = 5)
    (hmodel : ClassicalGroup.IsPSL (ThreeRigidity.image T U K) m 2) :
    (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
      ParabolicSplitting T L V U := by
  have he := residual_eq_containing_of_binary_linear_image h D structural A C
    (RigidityKernel.source_centralizers h D structural A C hnone) hd hKN hK hYK hm hmodel
  apply source_rigidity_step_of_residual_normal h D structural A C hnone hd
  simpa only [he] using hn

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
