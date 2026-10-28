module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallChiefKernel
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.DihedralFiveSetup
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallOffenderCentralizer
public import Theory.GroupTheory.NoncentralChiefRefinement.OrderBound

/-!
# The two paired chief actions in the marked-five wreath branch

The marked-five seed proves residual uniqueness, so every noncentral chief
factor of the original H-span has kernel O₂(H). The order of the proposed
S₅-wreath quotient excludes both the solvable and single-five action rows.
Thus both actual noncentral factors carry the paired eight-dimensional action.
Their orders multiply inside the original span, giving order at least 2^16.

These are retained ambient module data for the mixed-pair argument, not an
exclusion of an arbitrary D₁₀/Sz(2)--A₅ pair. Original 15.2.4 still requires
the rank-two recognition step.

Source: Aschbacher--Smith, original 15.1.12 and 15.2.4, printed pp.1090,
1105--1107.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
open NoncentralChiefRefinement ChapterB.QuasisimpleSource

private theorem wreath_card :
    Nat.card (RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))) = 28800 := by
  rw [RegularWreathProduct.card, Nat.card_perm, Nat.card_fin]
  norm_num [Nat.card_eq_fintype_card]

private theorem paired_of_card {D W : Type*} [Group D] [AddCommGroup W]
    [Module (ZMod 2) W] {ρ : Representation (ZMod 2) D W}
    (ha : ChapterB.ChiefSmallWholeAction ρ) (hc : Nat.card D = 28800) :
    Nonempty (ActionEquiv ρ BinaryPermutation.FivePair.wreathRepresentation) := by
  unfold ChapterB.ChiefSmallWholeAction at ha
  rcases ha with ⟨hs,_⟩ | ha
  · have hb := hs.card_le_seventy_two
    omega
  rcases ha with he | he
  · obtain ⟨e⟩ := he
    have hh := Nat.card_congr e.groupEquiv.toEquiv
    rw [Nat.card_perm, Nat.card_fin] at hh
    norm_num at hh
    omega
  · exact he

private theorem pair_card {D W : Type*} [Group D] [AddCommGroup W]
    [Module (ZMod 2) W] {ρ : Representation (ZMod 2) D W}
    (ha : Nonempty (ActionEquiv ρ BinaryPermutation.FivePair.wreathRepresentation)) :
    Nat.card W = 256 := by
  obtain ⟨e⟩ := ha
  rw [Nat.card_congr e.linearEquiv.toEquiv, Nat.card_prod]
  have hc : Nat.card (BinaryPermutation.core (Fin 5)) = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), BinaryPermutation.finrank_core]
    norm_num
  change Nat.card (BinaryPermutation.core (Fin 5)) * Nat.card (BinaryPermutation.core (Fin 5)) = _
  rw [hc]

variable {G : Type*} [Group G] [Finite G]

/-- Under the marked-five hypothesis, both original noncentral chief factors
have the actual paired action and kernel O₂(H), without a residual-uniqueness premise. -/
theorem ChosenSmallSource.marked_five_wreath_chief_actions
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))) :
    letI := h.prepared.elementary
    ∀ (l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
      (Jhat (imageRepresentation M V h.prepared.normalized)).subtype)),
    DihedralMarking l 5 2 →
    let U := (conjugateSpan H V).subgroupOf H
    letI := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
    ∀ s : SeriesOn U, ∃ i j : Fin s.series.length, i ≠ j ∧
      ∀ k ∈ ({i,j} : Finset (Fin s.series.length)), ¬ s.Central k ∧
        (Representation.BinaryOffender.actionHom (s.factorRepresentation k)).ker = pCore 2 H ∧
        Nonempty (ActionEquiv
          (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation k))
          BinaryPermutation.FivePair.wreathRepresentation) ∧
        Nat.card (s.Factor k) = 256 := by
  let := h.prepared.elementary
  intro l hd
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  dsimp only
  intro s
  have hp : PrimeDimensionOptions 5 2 := (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  have hu : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M} :=
    source_dihedral_five_residual_sylow_unique h.ambient T h.empty h.maximal h.centralizing
      h.partner h.many h.prepared l hp hd
  obtain ⟨i,j,hij,hi,hj⟩ := h.two_faithful_chief_factors_of_residual_unique hu hH s
  refine ⟨i,j,hij,?_⟩
  intro k hk
  have hk' : ¬ s.Central k ∧
      (Representation.BinaryOffender.actionHom (s.factorRepresentation k)).ker = pCore 2 H ∧
      ChapterB.ChiefSmallWholeAction
        (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation k)) := by
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hi
    · obtain rfl := Finset.mem_singleton.mp hk
      exact hj
  let ρ := s.factorRepresentation k
  let q := Representation.BinaryOffender.actionHom ρ
  let e := (QuotientGroup.quotientKerEquivOfSurjective q ρ.asGroupHom.rangeRestrict_surjective).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk'.2.1).trans he.some)
  have ha := paired_of_card hk'.2.2 ((Nat.card_congr e.toEquiv).trans wreath_card)
  exact ⟨hk'.1,hk'.2.1,ha,by
    have hc := pair_card ha
    exact hc⟩

/-- The original elementary H-span in the wreath branch has order at least 2^16.
The bound concerns the original ambient span, before quotienting the mixed pair. -/
theorem ChosenSmallSource.marked_five_wreath_span_card
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))) :
    letI := h.prepared.elementary
    ∀ (l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
      (Jhat (imageRepresentation M V h.prepared.normalized)).subtype)),
      DihedralMarking l 5 2 → 65536 ≤ Nat.card (conjugateSpan H V) := by
  classical
  let := h.prepared.elementary
  intro l hd
  let U := (conjugateSpan H V).subgroupOf H
  have hUH : conjugateSpan H V ≤ H := by
    rw [UniqueFactor.conjugateSpan_eq]
    exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H))
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUH
  obtain ⟨s⟩ := SeriesOn.exists_series U
  obtain ⟨i,j,hij,hijact⟩ := h.marked_five_wreath_chief_actions hH he l hd s
  have hi : Nat.card (s.Factor i) = 256 := (hijact i (by simp)).2.2.2
  have hj : Nat.card (s.Factor j) = 256 := (hijact j (by simp)).2.2.2
  have hb : (∏ k ∈ ({i,j} : Finset (Fin s.series.length)), Nat.card (s.Factor k)) ≤
      ∏ k : Fin s.series.length, Nat.card (s.Factor k) :=
    Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _) (fun _ _ => Nat.zero_le _)
      (fun _ _ _ => Nat.card_pos)
  have hc := s.series.prod_card_section_mul_head
  rw [s.head_eq,s.last_eq] at hc
  change (∏ k : Fin s.series.length, Nat.card (s.Factor k)) * Nat.card (⊥ : Subgroup H) = Nat.card U at hc
  rw [card_bot,mul_one] at hc
  rw [←Nat.card_congr (subgroupOfEquivOfLe hUH).toEquiv,←hc]
  simpa [Finset.prod_pair hij,hi,hj] using hb

end CFSG.Quasithin.Chapter15.Section02
