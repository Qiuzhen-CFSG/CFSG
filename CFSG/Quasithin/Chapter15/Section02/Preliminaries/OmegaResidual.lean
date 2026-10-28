module

public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaUniqueness
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan

/-!
# The original residual in the Omega row of Case II

Here M₀=M, so the Sylow supplement O²(M₀)T is M itself. Consequently
M=(M∩M_c)O²(M₀), and the source residual is the two-residual of the
M-normal closure of the literal intersection core. This proves its
normality and transports its image through the actual conjugation map.

The uniqueness conclusion of 15.2.3(3) is conditional on the residual
image being the full O²(M-bar). The Omega row also allows the proper
order-three image in 15.2.3(1)(iii); that branch is kept distinct.

Source: Aschbacher--Smith, 15.2.3(2)--(4), printed pp.1104--1105.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem residual_notation (H : Subgroup G) :
    twoResidualAmbient H = (pResidual 2 H).map H.subtype := by
  unfold twoResidualAmbient twoResidualSubgroup pResidual
  congr 1
  apply congrArg sInf
  ext N
  constructor
  · rintro ⟨hN, n, hn⟩
    exact ⟨hN, IsPGroup.of_card hn⟩
  · rintro ⟨hN, hp⟩
    exact ⟨hN, IsPGroup.iff_card.mp hp⟩

private theorem residual_sylow (T : Sylow 2 G) {M : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) :
    twoResidualAmbient M ⊔ (T : Subgroup G) = M := by
  rw [residual_notation]
  have h := congrArg (Subgroup.map M.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTM))
  simpa only [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM,
    ← MonoidHom.range_eq_map, range_subtype] using h

/-- The original conjugating group O²(M₀)T is M in the Omega case. -/
theorem source_omega_residual_orbit (T : Sylow 2 G)
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn)) :
    twoResidualAmbient (chosenStarredPreimage M V hn) ⊔ (T : Subgroup G) = M := by
  rw [chosenStarredPreimage_eq_of_omega M V hn ho]
  exact residual_sylow T hTM

/-- Original 15.2.3(4) in the Omega row, as the actual set product. -/
theorem source_omega_lemma_15_2_3_4 (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn)) :
    (M : Set G) = ((M ⊓ Mc : Subgroup G) : Set G) *
      (twoResidualAmbient (chosenStarredPreimage M V hn) : Set G) := by
  rw [chosenStarredPreimage_eq_of_omega M V hn ho]
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    apply hMc.2
    intro z hz
    exact (centralInvolutions_le_centralizer_sylow T hz t ht).symm
  have hnorm : M ≤ normalizer (twoResidualAmbient M : Set G) := by
    rw [residual_notation]
    exact M.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image M (pResidual 2 M))
  rw [← coe_mul_of_left_le_normalizer_right _ _ (inf_le_left.trans hnorm)]
  apply congrArg (fun H : Subgroup G => (H : Set G))
  apply le_antisymm ?_ (sup_le inf_le_left (map_subtype_le _))
  exact (residual_sylow T hTM).ge.trans
    (sup_le le_sup_right (le_sup_of_le_left (le_inf hTM hTMc)))

/-- In the Omega row the literal source residual is generated using all of M. -/
theorem source_omega_caseIIResidual_eq (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn)) :
    caseIIResidual T M (chosenStarredPreimage M V hn) Mc =
      twoResidualAmbient (conjugateSpanBy ((M ⊓ Mc).pCoreIn 2) M) := by
  unfold caseIIResidual
  rw [source_omega_residual_orbit T hTM hn ho]

/-- Original 15.2.3(2) for the literal Omega residual, with no image premise. -/
theorem source_omega_lemma_15_2_3_2 (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn)) :
    ((caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M).Normal := by
  rw [source_omega_caseIIResidual_eq T hTM hn ho, residual_notation]
  apply normal_subgroupOf_of_le_normalizer
  exact (le_normalizer_conjugateSpanBy _ _).trans
    (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _))

/-- Transport the literal Omega residual to a quotient action. Its image is
exactly the residual of the normal closure of the actual intersection-core image. -/
theorem source_omega_caseIIResidual_image
    {D : Type*} [Group D] [Finite D] (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn))
    (f : M →* D) (hf : Function.Surjective f) :
    ((caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M).map f =
      twoResidualAmbient (normalClosure
        ((((M ⊓ Mc).pCoreIn 2).subgroupOf M).map f : Set D)) := by
  rw [source_omega_caseIIResidual_eq T hTM hn ho]
  let R := (M ⊓ Mc).pCoreIn 2
  have hRM : R ≤ M := (pCoreIn_le 2 _).trans inf_le_left
  have hspan : conjugateSpanBy R M ≤ M := conjugateSpanBy_le_self hRM
  have he : (normalClosure (R.subgroupOf M : Set M)).map M.subtype =
      conjugateSpanBy R M := by
    rw [normalClosure_subgroupOf_eq_conjugateSpanBy R M hRM,
      map_subgroupOf_eq_of_le hspan]
  rw [← map_twoResidualAmbient_of_subgroup_image
    (normalClosure (R.subgroupOf M : Set M)) M.subtype _ he,
    ← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective]
  apply map_twoResidualAmbient_of_subgroup_image
  rw [map_normalClosure _ _ hf]
  rfl

private theorem full_image_of_residual_image
    {D : Type*} [Group D] [Finite D] (T : Sylow 2 G)
    {M Y : Subgroup G} (hTM : (T : Subgroup G) ≤ M) (hYM : Y ≤ M)
    (f : M →* D) (hf : Function.Surjective f)
    (hY : (Y.subgroupOf M).map f = pResidual 2 D) :
    ((Y ⊔ (T : Subgroup G)).subgroupOf M).map f = ⊤ := by
  rw [subgroupOf_sup hYM hTM, Subgroup.map_sup, hY]
  exact pResidual_sup_sylow_eq_top ((T.subtype hTM).mapSurjective hf)

/-- Original 15.2.3(3), with the exact preceding full-residual-image condition.
The Sylow supplement now proves the action-image premise of the uniqueness theorem. -/
theorem source_omega_lemma_15_2_3_3_of_residual_image
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (himage : ((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (actionHom M V hV.normalized).rangeRestrict =
        pResidual 2 (internalActionImage M V hV.normalized)) :
    maximalTwoLocalOvergroups
      (caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc ⊔
        (T : Subgroup G)) = {M} := by
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  let f := actionHom M V hV.normalized
  have hYM : Y ≤ M := by
    dsimp only [Y]
    rw [source_omega_caseIIResidual_eq T hM.1.2 hV.normalized ho]
    exact (map_subtype_le _).trans
      (conjugateSpanBy_le_self ((pCoreIn_le 2 _).trans inf_le_left))
  have hfull : ((Y ⊔ (T : Subgroup G)).subgroupOf M).map f.rangeRestrict = ⊤ :=
    full_image_of_residual_image T hM.1.2 hYM f.rangeRestrict f.rangeRestrict_surjective himage
  have hfull' : ((Y ⊔ (T : Subgroup G)).subgroupOf M).map f = f.range := by
    have he := congrArg (Subgroup.map f.range.subtype) hfull
    simpa only [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict,
      ← MonoidHom.range_eq_map, range_subtype] using he
  apply source_omega_lemma_15_2_3_3 hG T hempty hM hJ hV ho
  change ((chosenStarredPreimage M V hV.normalized).subgroupOf M).map f ≤
    ((Y ⊔ (T : Subgroup G)).subgroupOf M).map f
  rw [hfull']
  exact map_le_range _ _

end CFSG.Quasithin.Chapter15.Section02
