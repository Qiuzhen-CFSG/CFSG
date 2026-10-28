module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceSylow

/-!
# The displayed offender calculation on an actual source maximum

Choose a maximum elementary subgroup of the unchanged T_E with nontrivial
image modulo the full temporary core. The preceding local hypotheses justify
that choice and place it in C_H(E). The proved core transvection identity
and the actual paired quotient now supply the complete displayed calculation
for B = A ∩ Q and D = C_A(V_E), with the correction term the rank of
C_U(B)/C_U(A). The result is ordinary offending on the literal first summand.

This theorem needs no classification witness or best-generation premise.
Best generation of the identical Thompson image is the separate full-core
argument consumed by SourceAssembly.Local.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 15.3.67, printed pp.1153–1154.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceRanks
open Replacement Replacement.Transvections BestReduction.FullCoreTransfer
universe u
variable {G L : Type u} [Group G] [Finite G] [Group L]
  {Y T V M E Pc : Subgroup G} [IsMulCommutative V]
  (o : Geometry.OriginalData Y T V M E Pc)
  (hJ : elementaryAbelianMaxJ (lineT T E) ≤ centralizer (E : Set G))
  (hNM : normalizer (V : Set G) ≤ M) (hI : ¬ lineI E ≤ lineM M E)
  (f : temporaryLineNormalizer T V E →* L) (hf : Function.Surjective f)
  (hker : f.ker = centralizer
    (Replacement.Transvections.localSpan T V E : Set (temporaryLineNormalizer T V E)))

include hJ hNM hI in
/-- An actual maximum with nontrivial temporary-core image, the exact B/D
rank identities, both displayed bounds and the ordinary offender inequality.
Every temporary and transvection premise is supplied by OriginalData. -/
theorem exists_source_offender :
    let := o.module_normal
    let := o.module_elementary
    let H := temporaryLineNormalizer T V E
    let U := Replacement.Transvections.localSpan T V E
    let Q := localCore T V E
    let q := QuotientGroup.mk' Q
    let σ := o.pairedRepresentation f hf hker
    ∃ A ∈ elementaryAbelianMaxSubgroups ((lineT T E).subgroupOf H),
      A ≤ localCentralizer T V E ∧
      let B := A ⊓ Q
      let D := A ⊓ centralizer (U : Set H)
      let F := U ⊓ centralizer (A : Set H)
      let N := quotientRank (U ⊓ centralizer (B : Set H)) F
      A.map q ≠ ⊥ ∧ F = A ⊓ U ∧
      rank (A.map q) + rank (B.map f) + rank D = rank A ∧
      rank (D ⊔ U) = rank D + quotientRank U F ∧
      quotientRank U F ≤ rank (A.map q) + rank (B.map f) ∧
      quotientRank U (U ⊓ centralizer (B : Set H)) = 2 * rank (B.map f) ∧
      rank (B.map f) + N ≤ rank (A.map q) ∧
      quotientRank U F + N ≤ 2 * rank (A.map q) ∧
      IsOffender σ (A.map q) ∧
      2 * fixedCodim σ (A.map q) + N ≤ 2 * rank (A.map q) := by
  let := o.module_normal
  let := o.module_elementary
  dsimp only
  let H := temporaryLineNormalizer T V E
  let U := Replacement.Transvections.localSpan T V E
  let Q := localCore T V E
  let S₀ := (lineT T E).subgroupOf H
  let dt := temporaryData_of_original o
  let geom := fixedGeometry_of_original o f hf hker
  obtain ⟨S, hS, A, hA, hAC, hne⟩ := exists_temporary_max_of_local_structure
    M Y T V E o.line_le o.module_le_sylow o.sylow o.sylow_image o.residual_normal
    o.core_le_kernel o.residual_section_kernel_le_core o.local_core o.seed_commutator hNM hI hJ
  have hS' : (S : Subgroup H) = S₀ := by
    dsimp only [S₀]
    rw [← hS, subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
  rw [hS'] at hA
  let := hA.2.1
  have hU : U ≤ S₀ := comap_mono o.span_le_sylow
  have hkerQ := temporary_action_kernel_le_core Y T V E f hker dt A hA.1
  have hcore := temporary_core_quotientRank Y T V E f hf hker dt geom (A ⊓ Q) inf_le_right
  have hb := temporary_displayed_rank_inequalities Y T V E f hf hker dt geom A hA
  have ho := first_summand_offender S₀ U A Q hU hA f hker hkerQ hcore
    (o.pairedRepresentation f hf hker)
    (o.paired_fixedCodim_bound f hf hker A hAC) hne
  exact ⟨A, hA, hAC, hne, max_fixed_eq_inf S₀ U A hU hA,
    rank_two_images A Q U f hker hkerQ, replacement_rank S₀ U A hU hA,
    displayed_first_bound S₀ U A Q hU hA f hker hkerQ, hcore, hb.1, hb.2, ho.1, ho.2⟩
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceRanks
