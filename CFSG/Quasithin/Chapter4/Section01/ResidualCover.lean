module

public import CFSG.Quasithin.Chapter4.Defs
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Residual covering in general pushing up

Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), Lemma 4.1.4(3) and its preliminary `I⁺` construction,
printed pp. 606–607 (PDF pp. 623–624).

The eta covering condition makes `X ∩ I` surject onto `X/O₂(X)`. Since
`X` is two-perfect, its intersection residual still surjects, proving
`X = I⁺ O₂(X)`. Monotonicity gives `I⁺ ≤ H⁺`; normality of `X` in `M`
gives normality of `H⁺` in `H ∩ M`. The preliminary `I⁺` is two-perfect
and normal in `I`, as needed for the subsequent A.4.3 application.

Only the final adapters use Chapter 4 hypotheses. The covering products
are ambient set products, and all normality statements are relative.
-/

public section

namespace CFSG.Quasithin.Chapter4
open Subgroup
open scoped Pointwise
universe u
variable {G : Type u} [Group G]

/-- The preliminary cover used in the proof of 4.1.4(1). -/
theorem intersection_residual_cover [Finite G] {X I : Subgroup G}
    (hX : IsPPerfect 2 X)
    (hcover : (X : Set G) ⊆ (I : Set G) * (X.pCoreIn 2 : Set G)) :
    (X : Set G) =
      ((pResidual 2 (X ⊓ I : Subgroup G)).map (X ⊓ I).subtype : Set G) *
        (X.pCoreIn 2 : Set G) :=
  eq_mul_embedded_pResidual_of_cover 2 X I (pCore 2 X) hX hcover

/-- Intersections with a subgroup normal in `M` have residual normal in
`H ∩ M`; no normality in the ambient group is asserted. -/
theorem intersection_residual_normal {X M H : Subgroup G}
    (hXM : X ≤ M) (hN : (X.subgroupOf M).Normal) :
    (((pResidual 2 (X ⊓ H : Subgroup G)).map (X ⊓ H).subtype).subgroupOf
      (H ⊓ M)).Normal := by
  have hn : ((X ⊓ H).subgroupOf (H ⊓ M)).Normal := by
    let := hN
    have h := inf_subgroupOf_inf_normal_of_left (A' := X) (A := M) H
    rw [inf_comm M H] at h
    exact h
  exact normal_embedded_pResidual_subgroupOf 2
    (le_inf inf_le_right (inf_le_left.trans hXM)) hn

/-- The complete preliminary `I⁺` construction, including the properties
needed to apply A.4.3 with `X,I⁺` in the roles of `X,Y`. -/
theorem preliminary_Iplus [Finite G] {X M I H : Subgroup G}
    (hXM : X ≤ M) (hN : (X.subgroupOf M).Normal) (hX : IsPPerfect 2 X)
    (hIM : I ≤ M)
    (hcover : (X : Set G) ⊆ (I : Set G) * (X.pCoreIn 2 : Set G))
    (hIH : I ≤ H) :
    (X : Set G) =
        ((pResidual 2 (X ⊓ I : Subgroup G)).map (X ⊓ I).subtype : Set G) *
          (X.pCoreIn 2 : Set G) ∧
    IsPPerfect 2 ((pResidual 2 (X ⊓ I : Subgroup G)).map (X ⊓ I).subtype) ∧
    (pResidual 2 (X ⊓ I : Subgroup G)).map (X ⊓ I).subtype ≤ I ∧
    (((pResidual 2 (X ⊓ I : Subgroup G)).map (X ⊓ I).subtype).subgroupOf I).Normal ∧
    (pResidual 2 (X ⊓ I : Subgroup G)).map (X ⊓ I).subtype ≤
      (pResidual 2 (X ⊓ H : Subgroup G)).map (X ⊓ H).subtype := by
  refine ⟨intersection_residual_cover hX hcover,
    isPPerfect_embedded_pResidual 2 (X ⊓ I), (map_subtype_le _).trans inf_le_right,
    ?_, embedded_pResidual_mono 2 (inf_le_inf_left X hIH)⟩
  have hn := intersection_residual_normal (H := I) hXM hN
  have he : I ⊓ M = I := inf_eq_left.mpr hIM
  rw [he] at hn
  exact hn

/-- Finite-group form of 4.1.4(3), independent of the QTKE hypotheses. -/
theorem residual_cover_of_containment [Finite G] {X M I H : Subgroup G}
    (hXM : X ≤ M) (hN : (X.subgroupOf M).Normal) (hX : IsPPerfect 2 X)
    (hcover : (X : Set G) ⊆ (I : Set G) * (X.pCoreIn 2 : Set G))
    (hIH : I ≤ H) :
    (X : Set G) =
        ((pResidual 2 (X ⊓ H : Subgroup G)).map (X ⊓ H).subtype : Set G) *
          (X.pCoreIn 2 : Set G) ∧
    (pResidual 2 (X ⊓ H : Subgroup G)).map (X ⊓ H).subtype ≤ H ⊓ M ∧
    (((pResidual 2 (X ⊓ H : Subgroup G)).map (X ⊓ H).subtype).subgroupOf
      (H ⊓ M)).Normal := by
  refine ⟨intersection_residual_cover hX ?_,
    (map_subtype_le _).trans (le_inf inf_le_right (inf_le_left.trans hXM)),
    intersection_residual_normal hXM hN⟩
  exact hcover.trans (Set.mul_subset_mul hIH Set.Subset.rfl)

/-- Source adapter: eta membership already suffices for 4.1.4(3), so neither
maximality in mu nor the outside-overgroup condition is needed here. -/
theorem lemma_4_1_4_3 [Finite G] {K : GroupClass.{u}} {T : Sylow 2 G}
    {M Mplus Mminus I H : Subgroup G} (hyp : Hypothesis411 K T M Mplus)
    (hI : I ∈ eta M Mplus Mminus) (hIH : I ≤ H) :
    (Mplus : Set G) =
        ((pResidual 2 (Mplus ⊓ H : Subgroup G)).map (Mplus ⊓ H).subtype : Set G) *
          (Mplus.pCoreIn 2 : Set G) ∧
    (pResidual 2 (Mplus ⊓ H : Subgroup G)).map (Mplus ⊓ H).subtype ≤ H ⊓ M ∧
    (((pResidual 2 (Mplus ⊓ H : Subgroup G)).map (Mplus ⊓ H).subtype).subgroupOf
      (H ⊓ M)).Normal :=
  residual_cover_of_containment hyp.plus_le hyp.plus_normal hyp.plus_perfect hI.2.2.1 hIH

/-- The source `I⁺` construction under 4.1.1 and eta membership. -/
theorem preliminary_Iplus_of_eta [Finite G] {K : GroupClass.{u}} {T : Sylow 2 G}
    {M Mplus Mminus I H : Subgroup G} (hyp : Hypothesis411 K T M Mplus)
    (hminus : Mminus ∈ sigma M Mplus) (hI : I ∈ eta M Mplus Mminus)
    (hIH : I ≤ H) :
    (Mplus : Set G) =
        ((pResidual 2 (Mplus ⊓ I : Subgroup G)).map (Mplus ⊓ I).subtype : Set G) *
          (Mplus.pCoreIn 2 : Set G) ∧
    IsPPerfect 2 ((pResidual 2 (Mplus ⊓ I : Subgroup G)).map (Mplus ⊓ I).subtype) ∧
    (pResidual 2 (Mplus ⊓ I : Subgroup G)).map (Mplus ⊓ I).subtype ≤ I ∧
    (((pResidual 2 (Mplus ⊓ I : Subgroup G)).map (Mplus ⊓ I).subtype).subgroupOf I).Normal ∧
    (pResidual 2 (Mplus ⊓ I : Subgroup G)).map (Mplus ⊓ I).subtype ≤
      (pResidual 2 (Mplus ⊓ H : Subgroup G)).map (Mplus ⊓ H).subtype :=
  preliminary_Iplus hyp.plus_le hyp.plus_normal hyp.plus_perfect
    (hI.1.trans hminus.1) hI.2.2.1 hIH

end CFSG.Quasithin.Chapter4
