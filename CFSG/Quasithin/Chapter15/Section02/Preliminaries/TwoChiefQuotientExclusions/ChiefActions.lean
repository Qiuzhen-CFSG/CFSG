module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaOvergroupComparison
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallOffenderCentralizer
public import Theory.GroupTheory.NoncentralChiefRefinement.OrderBound

/-!
# Both natural chief actions in the single symmetric quotient branches

Residual uniqueness identifies the kernel of each noncentral chief action
with the original O₂(H). The order of the proposed quotient selects the
single natural action in the whole-action classification. For S₃ the actual
SL₂(2) matrices act on the full chief plane; for S₅ an action equivalence
identifies the full chief module with the natural four-dimensional module.

Both distinct noncentral intervals are retained, with their literal quotient
actions. Multiplying their section orders bounds the original elementary
orbit span below by 16 or 256. These data are inputs to the remaining
rank-two exclusions owned by qt-e-152-small-parabolic; the bounds alone do
not exclude either quotient.

Source: Aschbacher--Smith 15.1.12(1),(3) and 15.2.8, pp.1090,1109--1110.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor
open NoncentralChiefRefinement ChapterB.QuasisimpleSource

private theorem single_three_coordinates {D W : Type*} [Group D] [AddCommGroup W]
    [Module (ZMod 2) W] {ρ : Representation (ZMod 2) D W}
    (ha : ChapterB.ChiefSmallWholeAction ρ) (hc : Nat.card D = 6) :
    (∃ (e : D ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
      (c : W ≃ₗ[ZMod 2] (Fin 2 → ZMod 2)),
      ∀ g v, c (ρ g v) = (e g).val.mulVec (c v)) ∧ Nat.card W = 4 := by
  unfold ChapterB.ChiefSmallWholeAction at ha
  rcases ha with ⟨hs,hw⟩ | ⟨e⟩ | ⟨e⟩
  · rcases hs with ⟨c,e,he⟩ | ⟨e,c,he⟩
    · let a : W ≃ₗ[ZMod 2] subspaceCommutator ρ ⊤ (offenderSubgroup ρ) :=
        { toFun := fun v => ⟨v, by rw [hw]; trivial⟩
          invFun := Subtype.val
          left_inv := fun _ => rfl
          right_inv := fun _ => Subtype.ext rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      refine ⟨⟨e,a.trans c,fun g v => he g (a v)⟩,?_⟩
      rw [Nat.card_congr (a.trans c).toEquiv]
      norm_num [Nat.card_eq_fintype_card]
    · obtain ⟨b⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
      have hb : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
        rw [Nat.card_congr b.toEquiv]
        simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
      have hh := Nat.card_congr e.toEquiv
      rw [hc,RegularWreathProduct.card,hb] at hh
      norm_num [Nat.card_eq_fintype_card] at hh
  · have hh := Nat.card_congr e.some.groupEquiv.toEquiv
    rw [hc,Nat.card_perm,Nat.card_fin] at hh
    norm_num at hh
  · have hh := Nat.card_congr e.some.groupEquiv.toEquiv
    rw [hc,RegularWreathProduct.card,Nat.card_perm,Nat.card_fin] at hh
    norm_num [Nat.card_eq_fintype_card] at hh

private theorem single_five_coordinates {D W : Type*} [Group D] [AddCommGroup W]
    [Module (ZMod 2) W] {ρ : Representation (ZMod 2) D W}
    (ha : ChapterB.ChiefSmallWholeAction ρ) (hc : Nat.card D = 120) :
    Nonempty (ActionEquiv ρ (BinaryPermutation.naturalRepresentation (Fin 5))) ∧
      Nat.card W = 16 := by
  unfold ChapterB.ChiefSmallWholeAction at ha
  rcases ha with ⟨hs,_⟩ | ha | ⟨e⟩
  · have hb := hs.card_le_seventy_two
    omega
  · refine ⟨ha,?_⟩
    obtain ⟨e⟩ := ha
    rw [Nat.card_congr e.linearEquiv.toEquiv,
      Module.natCard_eq_pow_finrank (K := ZMod 2), BinaryPermutation.finrank_natural_odd (Fin 5) (by decide)]
    norm_num
  · have hh := Nat.card_congr e.some.groupEquiv.toEquiv
    rw [hc,RegularWreathProduct.card,Nat.card_perm,Nat.card_fin] at hh
    norm_num [Nat.card_eq_fintype_card] at hh

variable {G : Type*} [Group G] [Finite G]

/-- In the single S₃ row both original noncentral factors have their natural
two-dimensional actions and kernel O₂(H). -/
theorem ChosenSmallSource.symmetricThree_chief_actions
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    letI := h.prepared.elementary
    let U := (conjugateSpan H V).subgroupOf H
    letI := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
    ∀ s : SeriesOn U, ∃ i j : Fin s.series.length, i ≠ j ∧
      ∀ k ∈ ({i,j} : Finset (Fin s.series.length)), ¬ s.Central k ∧
        (Representation.BinaryOffender.actionHom (s.factorRepresentation k)).ker = pCore 2 H ∧
        (∃ (e : actionImage (s.factorRepresentation k) ≃*
          Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
          (c : Additive (s.Factor k) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2)),
          ∀ g v, c (Representation.BinaryOffender.imageRepresentation
            (s.factorRepresentation k) g v) = (e g).val.mulVec (c v)) ∧
        Nat.card (s.Factor k) = 4 := by
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  dsimp only
  intro s
  obtain ⟨i,j,hij,hi,hj⟩ := h.two_faithful_chief_factors hprior hH s
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
  have hc : Nat.card (actionImage ρ) = 6 :=
    (Nat.card_congr e.toEquiv).trans (by
      simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial])
  obtain ⟨ha,hcard⟩ := single_three_coordinates hk'.2.2 hc
  exact ⟨hk'.1,hk'.2.1,ha,hcard⟩

/-- In the single S₅ row both original noncentral factors have their natural
four-dimensional actions and kernel O₂(H). -/
theorem ChosenSmallSource.symmetricFive_chief_actions
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    letI := h.prepared.elementary
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
          (BinaryPermutation.naturalRepresentation (Fin 5))) ∧
        Nat.card (s.Factor k) = 16 := by
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  dsimp only
  intro s
  obtain ⟨i,j,hij,hi,hj⟩ := h.two_faithful_chief_factors hprior hH s
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
  have hc : Nat.card (actionImage ρ) = 120 :=
    (Nat.card_congr e.toEquiv).trans (by
      simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial])
  obtain ⟨ha,hcard⟩ := single_five_coordinates hk'.2.2 hc
  exact ⟨hk'.1,hk'.2.1,ha,hcard⟩

/-- Both natural S₃ chief factors contribute to the order of the literal span. -/
theorem ChosenSmallSource.symmetricThree_span_card
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    16 ≤ Nat.card (conjugateSpan H V) := by
  classical
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  have hUH : conjugateSpan H V ≤ H := by
    rw [UniqueFactor.conjugateSpan_eq]
    exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H))
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUH
  obtain ⟨s⟩ := SeriesOn.exists_series U
  obtain ⟨i,j,hij,hijact⟩ := h.symmetricThree_chief_actions hprior hH he s
  have hi : Nat.card (s.Factor i) = 4 := (hijact i (by simp)).2.2.2
  have hj : Nat.card (s.Factor j) = 4 := (hijact j (by simp)).2.2.2
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

/-- Both natural S₅ chief factors contribute to the order of the literal span. -/
theorem ChosenSmallSource.symmetricFive_span_card
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    256 ≤ Nat.card (conjugateSpan H V) := by
  classical
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  have hUH : conjugateSpan H V ≤ H := by
    rw [UniqueFactor.conjugateSpan_eq]
    exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H))
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUH
  obtain ⟨s⟩ := SeriesOn.exists_series U
  obtain ⟨i,j,hij,hijact⟩ := h.symmetricFive_chief_actions hprior hH he s
  have hi : Nat.card (s.Factor i) = 16 := (hijact i (by simp)).2.2.2
  have hj : Nat.card (s.Factor j) = 16 := (hijact j (by simp)).2.2.2
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
