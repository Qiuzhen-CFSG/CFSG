module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherCatalogueRows
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryIntrinsicQuotients
public import Theory.SpecificGroups.AlternatingEight.ReducedCover
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Discharging the binary maximal-component rows of local rigidity

The actual inclusion Y_R≤Y₀ and the full Sylow intersection allow the binary
Levi classification to identify Y_R/O₂(Y_R) from Y₀/O₂(Y₀). Its literal
image in N_G(R)/R is the central cover supplied by HigherIntrinsicQuotients,
so non-enlargement gives Y=Y_R and hence residual normality. The existing
source theorem then supplies rigidity and the actual parabolic complement.

This discharges the linear natural and exterior rows of original 12.2.2.
The A₈ row is also binary: the canonical quotient of Y₀/O₂(Y₀) onto A₈ is
injective by the reduced-cover theorem, and the checked exceptional
isomorphism identifies A₈ with PSL₄(2). Both original A₇ module rows keep
their actual action markings in the remaining disjunction. The nonquasisimple
maximal quotient also remains explicit. Their catalogue transports and final
assembly stay with qt-d-12213-local-rigidity; this reduction does not assert
completion of original 12.2.25–26.

Source: Aschbacher–Smith, original 12.2.2(3), A.3.12 and 12.2.25, printed
pp.795,47–48,805. The imported exceptional comparison retains its original
ATLAS attribution and license.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- The actual larger binary quotient gives a binary intrinsic quotient
of the normal containing component, and hence equality with the residual. -/
theorem residual_eq_of_containing_binary_maximal_quotient
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K K₀ : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hlocal : K ∈ Chapter1.L G (T : Subgroup G)) (hKK₀ : K ≤ K₀)
    (hK₀ : K₀ ∈ Chapter1.L G (T : Subgroup G))
    {n : ℕ} (hn : n ≤ 5)
    (e : (K₀ ⧸ pCore 2 K₀) ≃* BinaryLinear.OuterCyclic.LinearGroup n) :
    rigidityHyperplaneResidual L U V = K := by
  obtain ⟨m,hm,hmn,⟨a⟩⟩ :=
    ChapterA.Section03.SourceEmbeddings.BinaryIntrinsic.local_twoCore_quotient_of_containing_quotient
      T hlocal.1 hK₀.1 hKK₀ n hn e
  exact residual_eq_containing_of_binary_twoCore_quotient h D structural A C B hd hKN hK hYK
    (by omega : m = 3 ∨ m = 4 ∨ m = 5)
    ⟨ZMod 2,inferInstance,inferInstance,Nat.card_zmod 2,
      ⟨a.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < m)).symm⟩⟩

/-- A binary maximal quotient now supplies the original rigidity and actual
parabolic complement, with its contained subgroup and quotient maps retained. -/
theorem source_rigidity_of_containing_binary_maximal_quotient
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d)
    {K K₀ : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hn : normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G))
    (hlocal : K ∈ Chapter1.L G (T : Subgroup G)) (hKK₀ : K ≤ K₀)
    (hK₀ : K₀ ∈ Chapter1.L G (T : Subgroup G))
    {n : ℕ} (hn5 : n ≤ 5)
    (e : (K₀ ⧸ pCore 2 K₀) ≃* BinaryLinear.OuterCyclic.LinearGroup n) :
    normalizer (sectionRadical T U : Set G) ≤ normalizer (rigidityHyperplaneResidual L U V : Set G) ∧
      (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
        ParabolicSplitting T L V U := by
  have he := residual_eq_of_containing_binary_maximal_quotient h D structural A C
    (RigidityKernel.source_centralizers h D structural A C hnone) hd hKN hK hYK hlocal hKK₀ hK₀ hn5 e
  have hnormal : normalizer (sectionRadical T U : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G) := by simpa only [he] using hn
  exact ⟨hnormal,source_rigidity_step_of_residual_normal h D structural A C hnone hd hnormal⟩

private def chosen_alternating_eight_linear_quotient {K₀ W : Subgroup G}
    (E : ChosenModule T K₀ W) (hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀))
    (e : letI := E.actionCentralizer_normal
      (K₀ ⧸ (centralizer (W : Set G)).subgroupOf K₀) ≃* alternatingGroup (Fin 8)) :
    (K₀ ⧸ pCore 2 K₀) ≃* BinaryLinear.OuterCyclic.LinearGroup 4 := by
  let := E.actionCentralizer_normal
  let := hq
  let f := e.toMonoidHom.comp E.coreToFaithful
  have hf : Function.Surjective f := e.surjective.comp E.coreToFaithful_surjective
  let a := MulEquiv.ofBijective f ⟨AlternatingEight.reduced_cover_injective f hf
    (pCore_quotient_pCore_eq_bot 2),hf⟩
  exact a.trans (Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4)))

/-- Only the two original marked A7 module rows remain in the quasisimple
maximal-overcomponent branch. -/
inductive ExceptionalContainingModuleRows {K₀ W : Subgroup G} (E : ChosenModule T K₀ W) : Prop
  | alternatingSeven
      (action : letI := E.actionCentralizer_normal
        ActionEquiv E.faithfulCentralAction (alternatingNatural 7))
  | alternatingSevenFour
      (groupEquiv : letI := E.actionCentralizer_normal
        (K₀ ⧸ (centralizer (W : Set G)).subgroupOf K₀) ≃* alternatingGroup (Fin 7))
      (dimension : Module.finrank (ZMod 2) E.space = 4)

/-- Eliminate the larger linear, exterior and A8 rows at the actual
containing component. The remaining A7 rows keep their module marking. -/
theorem exceptional_containing_module_rows
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K K₀ W : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V < K)
    (hlocal : K ∈ Chapter1.L G (T : Subgroup G)) (hKK₀ : K ≤ K₀)
    (hK₀ : K₀ ∈ Chapter1.L G (T : Subgroup G))
    (E : ChosenModule T K₀ W) (hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀))
    (rows : ProperContainingModuleRows E) : ExceptionalContainingModuleRows E := by
  let := E.actionCentralizer_normal
  have hnot {n : ℕ} (hn : n ≤ 5)
      (e : (K₀ ⧸ pCore 2 K₀) ≃* BinaryLinear.OuterCyclic.LinearGroup n) : False :=
    hYK.ne (residual_eq_of_containing_binary_maximal_quotient h D structural A C B hd
      hKN hK hYK.le hlocal hKK₀ hK₀ hn e)
  cases rows with
  | linear n hn e =>
    exact (hnot (by omega) (e.groupEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear n))).elim
  | linearFiveExterior e _ _ =>
    exact (hnot (by decide) (e.trans (BinaryLinear.OuterCyclic.slEquivLinear 5))).elim
  | alternating n hn e =>
    rcases hn with rfl | rfl
    · exact .alternatingSeven e
    · exact (hnot (by decide) (chosen_alternating_eight_linear_quotient E hq e.groupEquiv)).elim
  | alternatingSevenFour e hd => exact .alternatingSevenFour e hd

/-- The exhaustive source reduction after the binary Levi catalogue:
full rigidity, or the original proper chain with a nonquasisimple maximal
head or one of the two marked A7 rows. Final assembly retains those cases. -/
theorem source_rigidity_or_exceptional_containing_rows
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222Modules.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d) :
    (normalizer (sectionRadical T U : Set G) ≤ normalizer (rigidityHyperplaneResidual L U V : Set G) ∧
      (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
        ParabolicSplitting T L V U) ∨
    ∃ K K₀ : Subgroup G,
      K ≤ normalizer (sectionRadical T U : Set G) ∧
      (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent ∧
      rigidityHyperplaneResidual L U V < K ∧
      normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G) ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧ K ≤ K₀ ∧ FaithfulMaximalLocal T K₀ ∧
      pCore 2 (ThreeRigidity.image T U K) ≤ center (ThreeRigidity.image T U K) ∧
      ¬ Chapter1.Section02.LocalModels.IsAlternating (ThreeRigidity.image T U K) 7 ∧
      ((¬ IsQuasisimple (K₀ ⧸ pCore 2 K₀)) ∨
        ∃ W : Subgroup G, ∃ E : ChosenModule T K₀ W, ExceptionalContainingModuleRows E) := by
  rcases source_rigidity_or_remaining_containing_rows h D structural modules A C hnone hd with hc | hc
  · exact Or.inl hc
  · obtain ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀,hcore,hseven,hrows⟩ := hc
    refine Or.inr ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀,hcore,hseven,?_⟩
    rcases hrows with hnot | ⟨W,E,hrows⟩
    · exact Or.inl hnot
    · by_cases hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀)
      · exact Or.inr ⟨W,E,exceptional_containing_module_rows h D structural A C
          (RigidityKernel.source_centralizers h D structural A C hnone) hd
          hKN hK hYK hlocal hKK₀ hK₀.1.1 E hq hrows⟩
      · exact Or.inl hq

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
