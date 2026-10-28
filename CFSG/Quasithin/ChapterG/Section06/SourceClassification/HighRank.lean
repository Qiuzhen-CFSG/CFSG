module

public import CFSG.Quasithin.ChapterB.Section05.OuterSixThreeShape.Components
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.FFExtraction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison.BinaryG2Exclusion.TernaryKernel

/-!
# Excluding the noncentral high-rank branch for the original transvection

The distinguished involution generates its literal normal closure K by
ambient conjugation. If it centralizes O3(K), normality of the embedded
three-core makes all of K centralize that core. Otherwise its cyclic subgroup
is the original moving best offender. The proved B.5.7 offender-plane argument
would give that same subgroup rank three, contradicting its order two.

The genuine B.5.2/B.5.5 and A.3.6 cover construction therefore leaves the
quasisimple Fitting branch, retaining every B.5.1 action clause. The actual
outer A6–C3 configuration is excluded by its normal component and cubic factor.
The binary G2 and A8 kernel obstructions are supplied by their concrete proofs;
no multiplier-table or classified-normal-closure premise is introduced.

Source: Aschbacher–Smith, G.6.4, pp.345–346, and B.5.7, pp.105–106.
-/

public section

open Subgroup Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.SourceInduction
open HighThreeRank HighThreeRank.ModuleCalculation
universe u v
variable {G : Type u} [Group G]

private theorem normalClosure_threeCore_central
    (a : G) (ha : a ∈ normalClosure ({a} : Set G))
    (hc : (⟨a, ha⟩ : normalClosure ({a} : Set G)) ∈
      centralizer (pCore 3 (normalClosure ({a} : Set G)) : Set _)) :
    pCore 3 (normalClosure ({a} : Set G)) ≤ center (normalClosure ({a} : Set G)) := by
  let K := normalClosure ({a} : Set G)
  let N := (pCore 3 K).map K.subtype
  have hn : N.Normal := inferInstance
  have haN : a ∈ centralizer (N : Set G) := by
    apply mem_centralizer_iff.mpr
    rintro x ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_iff.mp hc y hy)
  have hKN : K ≤ centralizer (N : Set G) :=
    normalClosure_le_normal (by simpa only [Set.singleton_subset_iff, SetLike.mem_coe] using haN)
  intro x hx
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext (mem_centralizer_iff.mp (hKN y.property) x
    (mem_map_of_mem K.subtype hx)).symm

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {κ : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

theorem Hypotheses.normalClosure_not_noncentralContext
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} κ)
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    {L : Subgroup (normalClosure ({a} : Set G))}
    (hL : IsComponent (normalClosure ({a} : Set G)) L)
    (hr : 1 < primeRank 3 L)
    (d : NoncentralContext κ (normalClosure ({a} : Set G)) L) : False := by
  classical
  let := h.finite_group
  let := h.finite_module
  let K := normalClosure ({a} : Set G)
  let σ := ρ.comp K.subtype
  let t : K := ⟨a, subset_normalClosure (Set.mem_singleton a)⟩
  have htp : t ^ 2 = 1 := Subtype.ext h.involution
  have htne : t ≠ 1 := fun he => h.nonidentity (congrArg Subtype.val he)
  have hbest : IsBestOffender σ (zpowers t) :=
    bestOffender_of_involution_displacement_le_one σ t htp htne ht.le
  have hm : ¬zpowers t ≤ centralizer (pCore 3 K : Set K) := by
    intro hc
    exact d.noncentral (normalClosure_threeCore_central a t.property (hc (mem_zpowers t)))
  have hf := h.normalClosure_ffHypothesis ht
  obtain ⟨r⟩ := NaturalReduction.ModelComparison.reduced_of_threeFreePerfectKernels earlier
    NaturalReduction.ModelComparison.alternatingEight_threeFreePerfectKernels
    NaturalReduction.ModelComparison.binaryG2_threeFreePerfectKernels σ hf hL hr d hbest hm
  obtain ⟨m⟩ := NaturalReduction.model_of_reduced σ hf hL d hm r
  have hfix := NaturalCentralizers.threeCore_fixes_model σ
    NaturalCentralizers.ConcreteModels.modelCommutants hL d m
  have hp := NaturalCentralizers.source_offender_plane σ hf hL d hbest hm hfix m
  have hc : Nat.card (zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime htp htne
  have htr : rank (zpowers t) = 1 := by
    rw [rank, hc]
    decide
  have he := hp.rank_eq
  omega

theorem Hypotheses.normalClosure_high_rank_quasisimple
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} κ)
    (h52 : CoverCentralizer.SourceConstruction.CoverInput κ)
    (h5 : ComponentReduction.PreliminaryActions.Preparation.ComponentInput.{u,v} κ)
    (hA : CoverCentralizer.SourceConstruction.SemisimpleInput κ)
    (h36 : Chapter1.Section02.A36Input κ)
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    {L : Subgroup (normalClosure ({a} : Set G))}
    (hL : IsComponent (normalClosure ({a} : Set G)) L)
    (hr : 1 < primeRank 3 L) :
    IsQuasisimple (generalizedFitting (normalClosure ({a} : Set G))) ∧
      Nonempty (ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp (normalClosure ({a} : Set G)).subtype)
        (generalizedFitting (normalClosure ({a} : Set G)))) := by
  let := h.finite_group
  have hf := h.normalClosure_ffHypothesis ht
  obtain ⟨d⟩ := PreciseMultiplierInputs.liftedCover_of_preparation _ h52 h5 hA h36 hf hL hr
  rcases CoverCentralizer.reduction_of_liftedCover hf hL hr d with hc | hnc
  · obtain ⟨hsq, hfit⟩ := hc
    exact HighThreeRank.quasisimple_branch _ h1 hf hL hsq hfit
  · obtain ⟨nc⟩ := hnc
    exact (h.normalClosure_not_noncentralContext h1 ht hL hr nc).elim

/-- The outer group configuration is impossible on the literal normal closure. -/
theorem Hypotheses.normalClosure_not_outerShape
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} κ)
    (h52 : CoverCentralizer.SourceConstruction.CoverInput κ)
    (h5 : ComponentReduction.PreliminaryActions.Preparation.ComponentInput.{u,v} κ)
    (hA : CoverCentralizer.SourceConstruction.SemisimpleInput κ)
    (h36 : Chapter1.Section02.A36Input κ)
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (c : ChapterB.OuterSixThreeShape (normalClosure ({a} : Set G))) : False := by
  let := h.finite_group
  exact c.not_quasisimple_fitting
    (h.normalClosure_high_rank_quasisimple h1 h52 h5 hA h36 ht
      c.first_isComponent c.first_three_rank).1
end CFSG.Quasithin.ChapterG.Section06
