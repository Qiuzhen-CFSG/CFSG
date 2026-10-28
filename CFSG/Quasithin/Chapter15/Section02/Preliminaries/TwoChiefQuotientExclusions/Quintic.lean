module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.Pair
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallRankOneSelection
public import CFSG.Quasithin.ChapterF.Section01.SourceLocalSylow
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.Tits
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.CubicCenter

/-!
# The centered cubic endpoint of the original quintic pair

Every original H-star centralizes the nontrivial Sylow omega-center.
Consequently it has a central involution, excluding both the Tits and
full binary Ree cubic parabolics. For the S₃ quotient, the actual first
factor is Y₁Rc, its full parabolic is Y₁T, and the entire overlap is T.
The final marked-five application retains that first factor, its D₁₀ or
Sz(2) quotient, the whole overlap and both inclusion maps.

The remaining enumeration must apply to this literal Chapter 15 pair.
The current Chapter 14 wrapper has its centralizing subgroup at the
quintic endpoint and assumes a plane chosen module, so it cannot be used
here without a further source argument. The shared enumeration belongs
to qt-e-quintic-recognition; its Chapter 15 adaptation and final source
discharge remain with qt-e-152-small-parabolic. This module does not claim
the unconditional marked-five S₃ exclusion.

Source: Aschbacher--Smith 15.2.6--8, printed pp.1109--1110, and the
quintic models of F.1.12, pp.262--264, with the corrected Sz(2) quotient.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
open ChapterF.Source ChapterF.GreenBook
variable {G : Type*} [Group G] [Finite G]

/-- The original Sylow seed supplies a central involution of every H-star. -/
theorem ChosenSmallSource.HStar_central_involution
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ∃ z : H, z ∈ center H ∧ orderOf z = 2 := by
  let : IsElementaryAbelian 2 (centralInvolutions T) := omegaOneCenterAmbient_elementaryAbelian _
  let : Nontrivial (centralInvolutions T) := (nontrivial_iff_ne_bot _).mpr
    (InitialSource.centralInvolutions_ne_bot_of_maximal_local T h.maximal.1)
  obtain ⟨z,hz⟩ := exists_ne (1 : centralInvolutions T)
  let j : centralInvolutions T →* H := inclusion ((centralInvolutions_le_sylow T).trans hH.1.1.2)
  have hc := source_centralizing_HStar_le_seed_centralizer h.ambient T h.maximal hH h.centralizing
  refine ⟨j z,mem_center_iff.mpr (fun a => ?_),?_⟩
  · exact Subtype.ext ((hc a.property) z z.property).symm
  · rw [orderOf_injective j (inclusion_injective _) z]
    apply orderOf_eq_prime _ hz
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) z.property)

private theorem central_involution_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : ∃ z : A, z ∈ center A ∧ orderOf z = 2) :
    ∃ z : B, z ∈ center B ∧ orderOf z = 2 := by
  obtain ⟨z,hz,ho⟩ := h
  exact ⟨e z,(MulEquivClass.apply_mem_center_iff e).mpr hz,(e.orderOf_eq z).trans ho⟩

/-- H-star cannot be the cubic Tits endpoint, regardless of the choice of
endpoint isomorphism. -/
theorem ChosenSmallSource.HStar_not_tits_cubic
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ¬ Nonempty (H ≃* Tits.ExceptionalParabolics.second) := by
  rintro ⟨e⟩
  exact Tits.ExceptionalParabolics.second_no_central_involution
    (central_involution_equiv e (h.HStar_central_involution hH))

/-- The full binary Ree cubic endpoint is excluded by the same actual seed. -/
theorem ChosenSmallSource.HStar_not_fullRee_cubic
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ¬ Nonempty (H ≃* Tits.ExceptionalParabolics.FullRee.second) := by
  rintro ⟨e⟩
  exact Tits.ExceptionalParabolics.FullRee.second_no_central_involution
    (central_involution_equiv e (h.HStar_central_involution hH))

/-- For the single S₃ quotient, the literal first factor Y₁Rc has full
parabolic Y₁T and the entire overlap is T. No containment T ≤ Y₁Rc is used. -/
theorem SmallResidualWitness.symmetricThree_geometry
    {T : Sylow 2 G} {M Mc V Y₁ H : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    let L := ![Y₁ ⊔ (M ⊓ Mc).pCoreIn 2,H]
    H ⊓ M = (T : Subgroup G) ∧
      commonBorel L (T : Subgroup G) = T ∧
      parabolic L (T : Subgroup G) 0 = Y₁ ⊔ (T : Subgroup G) ∧
      parabolic L (T : Subgroup G) 1 = H ∧
      (Y₁ ⊔ (T : Subgroup G)) ⊓ H = T ∧
      pCore 2 ((Y₁ ⊔ (T : Subgroup G)) ⊔ H : Subgroup G) = ⊥ := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  let A := Y₁ ⊔ (M ⊓ Mc).pCoreIn 2
  let L := ![A,H]
  obtain ⟨hF,hB₀,hP₁,hN,_⟩ := hw.symmetricThree_pair hH he
  have hB₁ : borel H (T : Subgroup G) = T := borel_eq_of_cubic_local_sylow H T
    ⟨T.subtype hH.1.1.2,map_subgroupOf_eq_of_le hH.1.1.2⟩ he.some
  have hB : commonBorel L (T : Subgroup G) = T := by
    change borel A (T : Subgroup G) ⊔ borel H (T : Subgroup G) ⊔ (T : Subgroup G) = T
    rw [hB₀,hB₁]
    exact le_antisymm (sup_le (sup_le inf_le_left le_rfl) le_rfl) le_sup_right
  have hHM : H ⊓ M = T := by
    have hn := hF.commonBorel_eq_normalizer 1
    rw [hP₁] at hn
    exact hN.trans (hn.symm.trans hB)
  obtain ⟨_,hP₀,_,hinter⟩ := hw.rankOne_pair_geometry hH le_rfl H.le_normalizer
    (sup_eq_left.mpr hH.1.1.2)
    (show Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ H) H by
      rw [inf_eq_left.mpr hTH]
      exact ⟨T.subtype hTH,map_subgroupOf_eq_of_le hTH⟩)
    (hF.quotient 1)
  rw [hHM] at hP₀ hinter
  refine ⟨hHM,hB,hP₀,hP₁,hinter,?_⟩
  have hg := parabolics_generate L (T : Subgroup G)
  change parabolic L (T : Subgroup G) 0 ⊔ parabolic L (T : Subgroup G) 1 = _ at hg
  rw [hP₀,hP₁] at hg
  exact hg.symm ▸ hF.twoCore_free

/-- The actual source inclusion amalgam cannot have either marked quintic
model. Its second endpoint is H, rather than the Chapter 14 residual vertex. -/
theorem ChosenSmallSource.HStar_not_quintic_amalgam
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) (P : Subgroup G) :
    let α := RankTwoAmalgam.ofSubgroups P (P ⊓ H) H inf_le_left inf_le_right
    ¬ (IsBinaryReeAmalgam α ∨ IsAtlasTitsAmalgam α) := by
  dsimp only
  intro hm
  rcases hm with hr | ht
  · exact h.HStar_not_fullRee_cubic hH ⟨hr.some.right⟩
  · exact h.HStar_not_tits_cubic hH ⟨ht.some.right⟩

/-- The marked-five S₃ branch supplies the literal pair and full Sylow
overlap required for enumeration, and excludes both concrete output models.
Obtaining one of those models remains with the quintic recognition owner;
the final 15.2.8 discharge stays with qt-e-152-small-parabolic. -/
theorem ChosenSmallSource.marked_five_symmetricThree_recognition_data
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    let L₀ := h.residual ⊔ (M ⊓ Mc).pCoreIn 2
    let P := h.residual ⊔ (T : Subgroup G)
    HypothesisF11 ![L₀,H] (T : Subgroup G) ∧
      (Nonempty ((L₀ ⧸ pCore 2 L₀) ≃* DihedralGroup 5) ∨
        Nonempty ((L₀ ⧸ pCore 2 L₀) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) ∧
      commonBorel ![L₀,H] (T : Subgroup G) = T ∧
      parabolic ![L₀,H] (T : Subgroup G) 0 = P ∧
      P ⊓ H = T ∧
      let α := RankTwoAmalgam.ofSubgroups P (P ⊓ H) H inf_le_left inf_le_right
      ¬ (IsBinaryReeAmalgam α ∨ IsAtlasTitsAmalgam α) := by
  let := h.prepared.elementary
  obtain ⟨l,hd⟩ := hd
  have hp : PrimeDimensionOptions 5 2 := (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  have hw := h.smallResidualWitness_of_marked_five ⟨l,hd⟩
  have hg := hw.1.symmetricThree_geometry hH he
  exact ⟨(hw.1.symmetricThree_pair hH he).1,
    source_dihedral_five_join_quotient h.ambient T h.empty h.maximal h.centralizing
      h.partner h.many h.prepared l hp hd,
    hg.2.1,hg.2.2.1,hg.2.2.2.2.1,h.HStar_not_quintic_amalgam hH _⟩

end CFSG.Quasithin.Chapter15.Section02
