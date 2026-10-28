module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallParabolicSetup
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.ChosenResidualKernel
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.PreparedSmallChiefActions
public import Theory.Representation.BinaryOffender.IrreducibleResidual

/-!
# Both faithful chief factors of the original elementary orbit span

Residual uniqueness controls the normalizer of every T-invariant two-perfect
subgroup of C_M(V). Thus the kernel of each noncentral chief action is O₂(H).
The prepared chosen module supplies exactly two noncentral factors, and its
small-action classification applies to both literal chief representations.
The final theorem transfers one factor's faithful quotient to H/O₂(H); the
subsequent exclusions require the two factors retained by the preceding theorem.

Source: Aschbacher--Smith 15.1.12 and the opening of 15.2.8,
printed pp.1089--1090 and 1109--1110.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
open NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G]

/-- Kernel equality on every noncentral interval, not just a selected interval. -/
theorem ChosenSmallSource.chief_kernel_of_residual_unique
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    letI := h.prepared.elementary
    let U := (conjugateSpan H V).subgroupOf H
    letI := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
    ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
      (Representation.BinaryOffender.actionHom (s.factorRepresentation i)).ker = pCore 2 H := by
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  dsimp only
  intro s i hi
  let := s.factorRepresentation_irreducible i
  let ρ := s.factorRepresentation i
  let q := Representation.BinaryOffender.actionHom ρ
  have hn : q.ker ≠ ⊤ := by
    intro he
    apply hi
    apply (s.central_iff_action i).mpr
    intro x v
    have hx : q x = 1 := show x ∈ q.ker from he ▸ mem_top x
    exact congrArg Additive.toMul ((actionHom_eq_one_iff ρ x).mp hx (Additive.ofMul v))
  exact source_HStar_reduced_kernel_of_residual_unique h.ambient T h.maximal h.centralizing
    h.partner h.prepared hunique hH q ρ.asGroupHom.rangeRestrict_surjective
    (irreducible_image_twoCore_eq_bot ρ) hn

/-- Both noncentral chief factors of the literal elementary orbit span, with their
actual natural actions and the faithful quotient H/O₂(H). -/
theorem ChosenSmallSource.two_faithful_chief_factors_of_residual_unique
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    letI := h.prepared.elementary
    let U := (conjugateSpan H V).subgroupOf H
    letI := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
    ∀ s : SeriesOn U, ∃ i j : Fin s.series.length, i ≠ j ∧
      (¬ s.Central i ∧
        (Representation.BinaryOffender.actionHom (s.factorRepresentation i)).ker = pCore 2 H ∧
        ChapterB.ChiefSmallWholeAction
          (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))) ∧
      (¬ s.Central j ∧
        (Representation.BinaryOffender.actionHom (s.factorRepresentation j)).ker = pCore 2 H ∧
        ChapterB.ChiefSmallWholeAction
          (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation j))) := by
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  dsimp only
  intro s
  have hcount := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).2 s
  obtain ⟨i,j,hij,hi,hj⟩ := s.one_lt_noncentralCount_iff.mp (by omega)
  have hk := h.chief_kernel_of_residual_unique hunique hH
  have ha := h.prepared.chief_small_whole_action h.ambient T h.empty h.maximal h.centralizing hH
  exact ⟨i,j,hij,⟨hi,hk s i hi,ha s i hi⟩,⟨hj,hk s j hj,ha s j hj⟩⟩

/-- The opening quotient reduction in 15.2.8 for every original small choice. -/
theorem ChosenSmallSource.HStar_small_quotient_of_residual_unique
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ChapterB.ChiefSmallActor (H ⧸ pCore 2 H) := by
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  obtain ⟨s⟩ := SeriesOn.exists_series U
  obtain ⟨i,_,_,⟨_,hk,ha⟩,_⟩ := h.two_faithful_chief_factors_of_residual_unique hunique hH s
  exact ha.quotient_actor.of_equiv (QuotientGroup.quotientMulEquivOfEq hk.symm)

end CFSG.Quasithin.Chapter15.Section02
