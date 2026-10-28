module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallResidualControl
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallWholeAction
public import Theory.GroupTheory.CubicResidualJoin

/-!
# Rank-one selection in the cyclic small residual rows

The marked cubic residual and the cyclic Omega residual have order-three
images. Their kernels lie in O₂(M), hence in the literal intersection core
Rc. Nontrivial action by Rc gives Y=[Y,Rc] and the quotient YRc/O₂(YRc)=S₃.
The marked cubic whole-action alternatives also supply M(T)={M,Mc}; this
makes Y itself the complete original rank-one witness in that row.

For the cyclic Omega row the witness retains the preceding Omega overgroup
comparison as an explicit premise. The elementary-nine and extraspecial
Omega selections and the overgroup comparison remain obligations of the
source-family assembly in qt-e-152-small-parabolic.

Source: Aschbacher--Smith 15.2.5--7 and the opening of 15.2.8,
printed pp.1107--1110.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

private theorem core_le_sylow
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V) :
    (M ⊓ Mc).pCoreIn 2 ≤ (T : Subgroup G) := by
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := h.partner ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hh := pCoreIn_le_sylow (M ⊓ Mc) (T.subtype (le_inf h.maximal.1.2 hTMc))
  simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (le_inf h.maximal.1.2 hTMc)] using hh

/-- The literal cyclic residual supplies full movement, nontriviality, its S₃
join quotient and the exact centralizer, using only its image and movement. -/
theorem ChosenSmallSource.cubic_residual_selection_of_image
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hc : letI := h.prepared.elementary
      Nat.card ((h.residual.subgroupOf M).map
        (actionHom M V h.prepared.normalized).rangeRestrict) = 3)
    (hm : letI := h.prepared.elementary
      let f := (actionHom M V h.prepared.normalized).rangeRestrict
      ¬ (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map f ≤
        centralizer (↑((h.residual.subgroupOf M).map f) : Set _)) :
    ⁅h.residual,(M ⊓ Mc).pCoreIn 2⁆ = h.residual ∧ h.residual ≠ ⊥ ∧
      Nonempty (((h.residual ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G) ⧸
        pCore 2 (h.residual ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      h.residual ⊓ centralizer (V : Set G) = h.residual.pCoreIn 2 := by
  let := h.prepared.elementary
  let Y := h.residual
  let R := (M ⊓ Mc).pCoreIn 2
  let A := Y.subgroupOf M
  let B := R.subgroupOf M
  let f := (actionHom M V h.prepared.normalized).rangeRestrict
  have hYM : Y ≤ M := source_caseIIResidual_le T h.maximal.1.2 (map_subtype_le _)
  have hRM : R ≤ M := (pCoreIn_le 2 (M ⊓ Mc)).trans inf_le_left
  have hp : IsPPerfect 2 A := h.residual_perfect.of_surjective
    (subgroupOfEquivOfLe hYM).symm.toMonoidHom (subgroupOfEquivOfLe hYM).symm.surjective
  have hn : B ≤ normalizer (A : Set M) :=
    (comap_mono ((core_le_sylow h).trans h.residual_invariant)).trans
      (Y.le_normalizer_comap M.subtype)
  have hk : A ⊓ f.ker ≤ pCore 2 M := by
    simpa only [f,MonoidHom.ker_rangeRestrict] using
      source_chosen_cyclic_kernel_le_core T h.maximal.1.2 h.partner h.prepared
        (isCyclic_of_prime_card hc)
  have hcoreR : M.pCoreIn 2 ≤ R :=
    (h.prepared.intersection_core_centralizer T h.maximal.1.2 h.partner).symm.le.trans inf_le_left
  have hkr : A ⊓ f.ker ≤ B := by
    intro x hx
    exact hcoreR (mem_map_of_mem M.subtype (hk hx))
  obtain ⟨hmove,_,⟨e⟩⟩ := cubic_join_of_moving_prime_image A B f hp
    (isPGroup_pCoreIn 2 (M ⊓ Mc)).comap_subtype hn hc
    (pCore_isPGroup.to_le hk) hkr hm
  have hjoin : (A ⊔ B).map M.subtype = Y ⊔ R := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hYM,map_subgroupOf_eq_of_le hRM]
  let j : (A ⊔ B : Subgroup M) ≃* (Y ⊔ R : Subgroup G) :=
    ((A ⊔ B).equivMapOfInjective M.subtype M.subtype_injective).trans
      (MulEquiv.subgroupCongr hjoin)
  let q := QuotientGroup.congr (pCore 2 (A ⊔ B : Subgroup M))
    (pCore 2 (Y ⊔ R : Subgroup G)) j (pCore_map_iso 2 j)
  refine ⟨?_,?_,⟨q.symm.trans e⟩,h.residual_centralizer_of_prime_image (by decide : 3 ≠ 2) hc⟩
  · have hh := congrArg (map M.subtype) hmove
    simpa only [A,B,map_commutator,map_subgroupOf_eq_of_le hYM,
      map_subgroupOf_eq_of_le hRM] using hh
  · intro he
    change Y = ⊥ at he
    change Nat.card ((Y.subgroupOf M).map f) = 3 at hc
    rw [he,bot_subgroupOf,Subgroup.map_bot,card_bot] at hc
    omega

/-- Original 15.2.5 in every marked cubic row, with no residual uniqueness input. -/
theorem ChosenSmallSource.maximal_overgroups_of_marked_cubic
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 3 2) :
    maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc} := by
  let := h.prepared.elementary
  obtain ⟨l,hd⟩ := hd
  have hc := Nat.card_congr hd.dihedral.some.toEquiv
  rw [DihedralGroup.nat_card] at hc
  rcases h.action_alternatives with ⟨_,⟨e⟩⟩ | ⟨_,⟨e⟩⟩ | ho | ⟨⟨e⟩,_,_⟩
  · exact h.prepared.maximal_overgroups_of_symmetric_three_action h.ambient T
      h.empty h.maximal h.centralizing h.partner e
  · exact h.prepared.maximal_overgroups_of_symmetric_three_cubic_action h.ambient T
      h.empty h.maximal h.centralizing h.partner h.different e
  · rw [ho.1,card_top] at hc
    have ho' : Nat.card (internalActionImage M V h.prepared.normalized) = 36 :=
      (Nat.card_congr ho.2.2.2.1.some.toEquiv).trans (by
        rw [Nat.card_prod]
        norm_num [Nat.card_eq_fintype_card,Fintype.card_perm])
    omega
  · have hc' := Nat.card_congr e.toEquiv
    rw [DihedralGroup.nat_card] at hc'
    omega

/-- The source choice Y₁=Y has all the cubic selection properties in 15.2.6. -/
theorem ChosenSmallSource.marked_cubic_residual_selection
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 3 2) :
    ⁅h.residual,(M ⊓ Mc).pCoreIn 2⁆ = h.residual ∧ h.residual ≠ ⊥ ∧
      Nonempty (((h.residual ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G) ⧸
        pCore 2 (h.residual ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      h.residual ⊓ centralizer (V : Set G) = h.residual.pCoreIn 2 := by
  let := h.prepared.elementary
  obtain ⟨l,hd⟩ := hd
  have hp : PrimeDimensionOptions 3 2 :=
    (primeDimensionOptions_iff 3 2).mpr (Or.inl ⟨rfl,Or.inr rfl⟩)
  have him := source_dihedral_caseIIResidual_image h.ambient T h.empty h.maximal
    h.centralizing h.partner h.many h.prepared l hp hd
  have hc : Nat.card ((h.residual.subgroupOf M).map
      (actionHom M V h.prepared.normalized).rangeRestrict) = 3 := by
    exact (congrArg (fun K : Subgroup (internalActionImage M V h.prepared.normalized) => Nat.card K) him).trans
      ((card_map_of_injective (Jhat (imageRepresentation M V h.prepared.normalized)).subtype_injective).trans
        hd.card_kernel)
  apply h.cubic_residual_selection_of_image hc
  let f := (actionHom M V h.prepared.normalized).rangeRestrict
  let B := (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map f
  have hBne : B ≠ ⊥ := by
    intro he
    have hk := (Subgroup.map_eq_bot_iff _).mp he
    apply source_chosen_core_noncentral h.ambient T h.empty h.maximal h.centralizing
      h.partner h.many h.prepared
    intro r hr
    let x : M := ⟨r,((pCoreIn_le 2 (M ⊓ Mc)).trans inf_le_left) hr⟩
    have hx : x ∈ (actionHom M V h.prepared.normalized).ker := congrArg Subtype.val (hk hr)
    rwa [actionHom_ker] at hx
  have hm := dihedral_prime_moves_twoGroup (imageRepresentation M V h.prepared.normalized)
    (imageRepresentation_injective _ _ _) h.prepared.quadratic_ratio l hp hd B
    ((isPGroup_pCoreIn 2 (M ⊓ Mc)).comap_subtype.map f) hBne
  dsimp only
  rwa [him]

/-- Complete original 15.2.6 and the cubic normalizer clause of 15.2.7 in the
marked cubic row, applying the moved-selection consumer with uniqueness proved. -/
theorem ChosenSmallSource.smallResidualWitness_of_marked_cubic
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 3 2) :
    SmallResidualWitness h h.residual ∧ SmallCubicNormalizer h h.residual := by
  obtain ⟨hm,hne,hq,hc⟩ := h.marked_cubic_residual_selection hd
  exact h.smallResidualWitness_of_moved_selection (h.maximal_overgroups_of_marked_cubic hd)
    le_rfl h.residual_perfect hne h.residual_invariant hm (Or.inl hq) hc

/-- In case 15.2.3(1)(iii), Y itself supplies the cubic selection, including
proper chosen supports and the original Rc quotient. -/
theorem ChosenSmallSource.omega_cubic_residual_selection
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hc : letI := h.prepared.elementary
      Nat.card ((h.residual.subgroupOf M).map
        (actionHom M V h.prepared.normalized).rangeRestrict) = 3) :
    ⁅h.residual,(M ⊓ Mc).pCoreIn 2⁆ = h.residual ∧ h.residual ≠ ⊥ ∧
      Nonempty (((h.residual ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G) ⧸
        pCore 2 (h.residual ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      h.residual ⊓ centralizer (V : Set G) = h.residual.pCoreIn 2 := by
  let := h.prepared.elementary
  apply h.cubic_residual_selection_of_image hc
  have hs := source_omega_chosen_residual_complete h.ambient T h.empty h.maximal
    h.centralizing h.partner h.many h.prepared ho
  dsimp only
  intro he
  have hb := commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp he)
  rw [hs.image_movement] at hb
  exact hs.image_nontrivial hb

/-- Apply the cyclic Omega selection to 15.2.6--7. The same source-family owner
must discharge the remaining original 15.2.5 overgroup comparison. -/
theorem ChosenSmallSource.smallResidualWitness_of_omega_cubic
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hc : letI := h.prepared.elementary
      Nat.card ((h.residual.subgroupOf M).map
        (actionHom M V h.prepared.normalized).rangeRestrict) = 3)
    (hover : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc}) :
    SmallResidualWitness h h.residual ∧ SmallCubicNormalizer h h.residual := by
  obtain ⟨hm,hne,hq,hcentral⟩ := h.omega_cubic_residual_selection ho hc
  exact h.smallResidualWitness_of_moved_selection hover le_rfl h.residual_perfect hne
    h.residual_invariant hm (Or.inl hq) hcentral

/-- All dihedral markings now supply the original rank-one witness Y₁=Y. -/
theorem ChosenSmallSource.smallResidualWitness_of_dihedral
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      SourceCases.Dihedral (imageRepresentation M V h.prepared.normalized)) :
    SmallResidualWitness h h.residual ∧ SmallCubicNormalizer h h.residual := by
  let := h.prepared.elementary
  obtain ⟨l,p,m,hpm,hd⟩ := hd
  have hm := h.marking_dimension l p m hd
  subst m
  rcases (primeDimensionOptions_iff p 2).mp hpm with ⟨rfl,_⟩ | ⟨rfl,_⟩
  · exact h.smallResidualWitness_of_marked_cubic ⟨l,hd⟩
  · exact h.smallResidualWitness_of_marked_five ⟨l,hd⟩

/-- The marked cubic witness feeds the actual H-star quotient reduction.
The S₅ wreath row is excluded by the existing cubic argument; the two
single symmetric-group exclusions remain part of the source-family assembly. -/
theorem ChosenSmallSource.HStar_quotient_of_marked_cubic
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 3 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5)) := by
  have hw := (h.smallResidualWitness_of_marked_cubic hd).1
  rcases h.HStar_small_quotient_of_residual_unique hw.residual_unique hH with
    h3 | hwr | h5 | h5wr
  · exact Or.inl h3
  · exact Or.inr (Or.inl hwr)
  · exact Or.inr (Or.inr h5)
  · let := h.prepared.elementary
    obtain ⟨l,hd⟩ := hd
    have hp : PrimeDimensionOptions 3 2 :=
      (primeDimensionOptions_iff 3 2).mpr (Or.inl ⟨rfl,Or.inr rfl⟩)
    exact (source_dihedral_cubic_HStar_not_symmetricFive_wreath h.ambient T h.empty
      h.maximal h.centralizing h.partner h.many h.prepared l hp hd hH h5wr).elim

end CFSG.Quasithin.Chapter15.Section02
