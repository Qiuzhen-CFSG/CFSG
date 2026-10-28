module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceInputs.Covers
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.Geometry
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.LocalClauses
public import Theory.GroupTheory.CComponent.QuotientLifting
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSix

/-!
# The literal covering step after the binary rank-two sieve

C.2.7 describes L* using Ω₁(Z(O₂(LR))), whereas the earlier plus action
uses the span of V. We use the existing map from L/O₂(L) to the literal
C.2.7 star image. Its perfect central kernel is a two-group for PSL₃(2),
PSL₄(2), or PSL₅(2), by the proved model multiplier results. It is trivial
because L/O₂(L) has trivial two-core. This gives the source quotient model
without an identification of the star and plus actions or a natural block
module premise.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.22,
printed p.1128; I.1.3, printed p.407.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The actual C.2.7 core-to-star map is injective in each surviving binary model. -/
theorem coreToStar_injective_of_binary_model
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hR : d.R ≤ normalizer (c.L : Set G))
    (n : ℕ) (hn : n = 3 ∨ n = 4 ∨ n = 5)
    (e : starImage c.L d.R c.L ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) :
    Function.Injective (coreToStar hR) := by
  let _ : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) :=
    Atlas.psl_simple_high_rank n (by omega)
  let _ : Nontrivial (starImage c.L d.R c.L) := e.symm.injective.nontrivial
  have hne : starImage c.L d.R c.L ≠ ⊥ := (nontrivial_iff_ne_bot _).mp inferInstance
  let f := coreStarCover hR c.core_quotient_quasisimple hne
  let g : PerfectCentralCovering.Cover (c.L ⧸ pCore 2 c.L)
      (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) :=
    { toMonoidHom := e.toMonoidHom.comp f.toMonoidHom
      surjective := e.surjective.comp f.surjective
      isPerfect := f.isPerfect
      ker_le_center := by
        rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
        exact f.ker_le_center }
  have hk : IsPGroup 2 (coreToStar hR).ker := by
    have h := SourceInputs.binaryPSL_cover_kernel_isTwoGroup n hn g
    change IsPGroup 2 (e.toMonoidHom.comp f.toMonoidHom).ker at h
    rwa [MonoidHom.ker_comp_of_injective _ _ e.injective] at h
  apply (MonoidHom.ker_eq_bot_iff _).mp
  have hle : (coreToStar hR).ker ≤ pCore 2 (c.L ⧸ pCore 2 c.L) :=
    le_sSup ⟨inferInstance, hk⟩
  exact eq_bot_iff.mpr (hle.trans
    (pCore_quotient_pCore_eq_bot (G := c.L) 2).le)

/-- Source 15.3.22's covering step for the literal C.2.7 star quotient. -/
theorem core_quotient_binary_of_star_model
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hR : d.R ≤ normalizer (c.L : Set G))
    (n : ℕ) (hn : n = 3 ∨ n = 4 ∨ n = 5)
    (e : starImage c.L d.R c.L ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) :
    Nonempty ((c.L ⧸ pCore 2 c.L) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) :=
  ⟨(MulEquiv.ofBijective (coreToStar hR)
      ⟨coreToStar_injective_of_binary_model d c hR n hn e,
        coreToStar_surjective hR⟩).trans e⟩

/-- The binary-linear C.2.7 alternative already gives the exact marked
model needed for the source quotient conclusion, without a block premise. -/
theorem core_quotient_binary_of_source_parabolic
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hR : d.R ≤ normalizer (c.L : Set G))
    (M : Subgroup G) (n : ℕ) (hn : n = 4 ∨ n = 5)
    (hp : IsBinaryPositiveRankParabolic
      ((starM c.L d.R M).subgroupOf (starImage c.L d.R c.L)) n) :
    Nonempty ((c.L ⧸ pCore 2 c.L) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) := by
  obtain ⟨e, _⟩ := hp
  exact core_quotient_binary_of_star_model d c hR n (Or.inr hn) e

omit [Finite G] in
/-- An A₈ block already supplies the binary degree-four quotient required by
15.3.22. Its alternating natural module need not be a degree-four linear block. -/
theorem core_quotient_binary_of_alternatingEight_block
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hblock : ChapterC.IsAlternatingBlock c.L 8) :
    Nonempty ((c.L ⧸ pCore 2 c.L) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) := by
  obtain ⟨e⟩ := hblock.2.2.quotient_iso
  exact ⟨e.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm⟩

/-- A complete surviving star-model list gives the exact conclusion of
15.3.22; the nonbinary exclusions still have to produce this list. -/
theorem source_15_3_22_of_binary_star_models
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hR : d.R ≤ normalizer (c.L : Set G))
    (hmodels : ∃ n, (n = 3 ∨ n = 4 ∨ n = 5) ∧
      Nonempty (starImage c.L d.R c.L ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) :
    ∃ n, (n = 3 ∨ n = 4 ∨ n = 5) ∧
      Nonempty ((c.L ⧸ pCore 2 c.L) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hmodels
  exact ⟨n, hn, core_quotient_binary_of_star_model d c hR n hn e⟩

/-- Original-input application of the literal 15.3.22 covering step.
Source 15.3.12 supplies R-normalization. Only the surviving star-model list
remains, to be proved by the distinct nonbinary source exclusions. -/
theorem source_15_3_22_from_selection_of_binary_star_models
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (hrank : primeRank 3 d.Yplus = 2)
    (c : ComponentWitness d I)
    (hmodels : ∃ n, (n = 3 ∨ n = 4 ∨ n = 5) ∧
      Nonempty (starImage c.L d.R c.L ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) :
    ∃ n, (n = 3 ∨ n = 4 ∨ n = 5) ∧
      Nonempty ((c.L ⧸ pCore 2 c.L) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) := by
  have h12 := ComponentIntersection.source_lemma_15_3_12_1_from_selection
    hG d hempty hM hu hmany hI (component_le c)
      (LinearThree.Extension.SourceCases.component_in_overgroup d c) hrank c.rank_pos
  exact source_15_3_22_of_binary_star_models d c h12.2.1 hmodels

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
