module
public import CFSG.Quasithin.Chapter10.SourceNormalizationAssembly
public import CFSG.Quasithin.Chapter10.SourceSetup
public import CFSG.Quasithin.Chapter10.SourceThompsonNormalization
public import CFSG.Quasithin.Chapter10.SourceWeakClosure
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Selection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental

/-!
# The actual Chapter 12 input before component normalization

The original Hypothesis 12.2.1 constructs the Fundamental Setup for
L₀=⟨Lᵀ⟩ without presupposing normalization or a chosen module. The source
10.1.2(2) theorem consequently normalizes L by the actual J(T).
The nonnormal alternative retains the original two-factor orbit, maximal
normalizer and full elementary module for the remaining Chapter 10 argument.
The full-module kernel also satisfies the literal unique-overgroup
hypothesis of E.3.35, giving its solvable-overgroup weak-closure bound.

A chosen Section 12.2 Irr⁺(L,R₂(LT),T) module exists precisely when T
normalizes L: this identifies the distinction between the two source choices
and prevents using that later choice to assume the normalization being proved.
The A5 branch now has full normalization after its independent tensor
exclusion, using a reselected minimal setup and the proved Hall/natural
contradiction. The multiple-overgroup application retains only tensor exclusion,
the non-A5 survivor and its actual A5 replacement, all on the same G and T.
The universal conditional API additionally retains the singleton-overgroup
premise; that optional branch is not required by the guarded applications.
The unconditional T-normalization statement10.0.1 is not asserted here.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
§10.1, p.741, and Hypothesis12.2.1/Theorem12.2.2, pp.794–795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {L : Subgroup G}

/-- The original source hypotheses construct a seed for the T-orbit actor,
including before normalization of L has been established. -/
theorem Hypothesis1221.exists_original_fundamentalSetup
    (h : Hypothesis1221 K T L) : Nonempty (FundamentalSetup K T L) :=
  source_exists_fundamentalSetup h.simpleQTKE T L
    h.maximal_faithful.1 h.maximal_faithful.2 h.quasisimple

/-- Source 10.1.2(2) applies to the literal component in Hypothesis 12.2.1,
without a chosen Section 12.2 module or a normalization premise. -/
theorem Hypothesis1221.thompson_normalizes_component
    (h : Hypothesis1221 K T L) :
    Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ normalizer (L : Set G) := by
  obtain ⟨D⟩ := h.exists_original_fundamentalSetup
  exact D.thompson_normalizes_component

/-- The literal 12.2.2 input constructs the original module for the E.3.35
solvable-overgroup branch. Its full-kernel uniqueness premise is supplied
by source 10.1.2(3), without a chosen Section 12.2 module or normalization. -/
theorem Hypothesis1221.exists_original_weakClosure_setup
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      maximalTwoLocalOvergroups (normalizer
        (((T : Subgroup G) ⊓ centralizer (D.fullModule : Set G) : Subgroup G) : Set G)) =
        {D.maximalLocal} ∧
      maximalTwoLocalOvergroups (normalizer (Stellmacher.elementaryAbelianMaxJ
        ((T : Subgroup G) ⊓ centralizer (D.fullModule : Set G)) : Set G)) =
        {D.maximalLocal} ∧
      ∀ H : Subgroup G, Group.IsSolvable H → (T : Subgroup G) ≤ H →
        ¬ H ≤ D.maximalLocal →
        min (ChapterE.globalW D.fullModule (T : Subgroup G))
          (ChapterE.globalR D.fullModule) ≤ 1 := by
  obtain ⟨D⟩ := h.exists_original_fundamentalSetup
  have h127 := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  refine ⟨D, Chapter10.source_fullModule_kernel_unique D,
    Chapter10.source_kernel_thompson_unique D h127, ?_⟩
  intro H hs hTH hHM
  let := hs
  exact Chapter10.source_solvable_overgroup_weakClosure_bound D hTH hHM

/-- Choosing the Section 12.2 Irr⁺(L,R₂(LT),T) module is equivalent to the
normalization which precedes that choice in the source. The earlier FSU
uses L₀ instead, and its existence above does not presuppose normalization. -/
theorem Hypothesis1221.exists_chosen_iff_normalizes
    (h : Hypothesis1221 K T L) :
    (∃ V : Subgroup G, Nonempty (ChosenModule T L V)) ↔
      (T : Subgroup G) ≤ normalizer (L : Set G) := by
  constructor
  · rintro ⟨V, ⟨D⟩⟩
    exact D.sylow_normalizes_component
  · exact h.exists_chosen_of_normalizes

/-- The literal 12.2.2 input is reduced to its normalized chosen-module
branch or the genuine two-factor nonnormal configuration from Chapter 10.
The latter retains its original maximal normalizer and full orbit module. -/
theorem Hypothesis1221.normalizes_or_original_pair
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    ((T : Subgroup G) ≤ normalizer (L : Set G) ∧
      ∃ V : Subgroup G, Nonempty (ChosenModule T L V)) ∨
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      IsMaximalTwoLocal D.maximalLocal ∧
      normalizer (D.fullModule : Set G) = D.maximalLocal ∧
      IsElementaryAbelian 2 D.fullModule ∧
      L < localOrbit T L ∧
      Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      (normalizer (L : Set G)).relIndex (T : Subgroup G) = 2 ∧
      ∃ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) ∧
        localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom ∧
        ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ ≤
          (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  by_cases hn : (T : Subgroup G) ≤ normalizer (L : Set G)
  · exact Or.inl ⟨hn, h.exists_chosen_of_normalizes hn⟩
  · obtain ⟨D, hm, hvn, he, hlt, hi, hp⟩ := Chapter10.source_nonnormal_preparation
      h.simpleQTKE h.maximal_faithful.1 h.maximal_faithful.2 h.quasisimple hn
    exact Or.inr ⟨D, hm, hvn, he, hlt, D.thompson_normalizes_component, hi, hp⟩

/-- The original A5 component is normalized, and its Section 12.2 module
can then be chosen, after the independent tensor source is supplied.
The Hall, natural-generation and point-control inputs are discharged. -/
theorem Hypothesis1221.a5_normalizes_and_chosen_after_tensor_exclusion_of_many
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnot : ∀ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      D.IsMinimalFullModule → ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
      ¬ Nonempty (Chapter10.SourceA5TensorModel D e)) :
    (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      ∃ V : Subgroup G, Nonempty (ChosenModule T L V) := by
  have hn := Chapter10.source_a5_normalizes_after_tensor_exclusion_of_many e
    h.simpleQTKE h.maximal_faithful.1 h.maximal_faithful.2 h.quasisimple hmany hnot
  exact ⟨hn, h.exists_chosen_of_normalizes hn⟩

/-- The source normalization prefix on the same G and T, using the actual
multiple-overgroup standing hypothesis. No global model exclusion or
single-overgroup theorem is required before choosing the module. -/
theorem Hypothesis1221.normalizes_and_chosen_after_source_branches_of_many
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (htensor : Chapter10.SourceA5TensorExclusionAt T)
    (hreduction : Chapter10.SourceNonnormalReductionAt T)
    (hreplacement : Chapter10.SourceLinearThreeReplacementAt T) :
    (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      ∃ V : Subgroup G, Nonempty (ChosenModule T L V) := by
  have hn := Chapter10.source_normalizes_of_source_branches_of_many h.simpleQTKE hmany
    htensor hreduction hreplacement h.maximal_faithful.1 h.maximal_faithful.2 h.quasisimple
  exact ⟨hn, h.exists_chosen_of_normalizes hn⟩

/-- The literal Chapter 12 normalization and module-existence prefix,
conditional on the outstanding source branches. This does not assert the
remaining invariance, reducedness or TI conclusions of Structural1222. -/
theorem Hypothesis1223.normalizes_and_chosen_after_source_branches
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hsingle : Chapter10.SourceSingleOvergroupExclusionAt T)
    (htensor : Chapter10.SourceA5TensorExclusionAt T)
    (hreduction : Chapter10.SourceNonnormalReductionAt T)
    (hreplacement : Chapter10.SourceLinearThreeReplacementAt T) :
    (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      Nonempty {V : Subgroup G // Nonempty (ChosenModule T L V)} := by
  have hn := Chapter10.source_normalizes_of_source_branches h.simpleQTKE hsingle htensor
    hreduction hreplacement h.maximal_faithful.1 h.maximal_faithful.2 h.quasisimple
  obtain ⟨V,hV⟩ := h.toHypothesis1221.exists_chosen_of_normalizes hn
  exact ⟨hn, ⟨⟨V,hV⟩⟩⟩

/-- In the actual multiple-overgroup campaign branch, the same source
application needs no singleton-branch premise. -/
theorem Hypothesis1223.normalizes_and_chosen_after_source_branches_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (htensor : Chapter10.SourceA5TensorExclusionAt T)
    (hreduction : Chapter10.SourceNonnormalReductionAt T)
    (hreplacement : Chapter10.SourceLinearThreeReplacementAt T) :
    (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      Nonempty {V : Subgroup G // Nonempty (ChosenModule T L V)} := by
  obtain ⟨hn,V,hV⟩ := h.toHypothesis1221.normalizes_and_chosen_after_source_branches_of_many
    hmany htensor hreduction hreplacement
  exact ⟨hn, ⟨⟨V,hV⟩⟩⟩

end CFSG.Quasithin.Chapter12.Section02
