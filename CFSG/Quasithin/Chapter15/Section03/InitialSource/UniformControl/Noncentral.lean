module
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.PlaneSeed
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.OrthogonalSeed
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.NaturalModels.Action
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl
open ChapterB ChapterC.GlaubermanNiles
universe u
variable {G : Type u} [Group G] [Finite G]

theorem source_noncentral_seed_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hcase : M ≠ Mc ∨ Nat.card (centralInvolutions T) = 2)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (D : CharacteristicPair (baumann (T : Subgroup G))) :
    M ⊓ centralizer (ChapterC.RankOne.ChiProduct.FixedPair.firstSeed T D : Set G) =
      (M ⊓ centralizer (localModule T M : Set G)) ⊔ (T : Subgroup G) := by
  have hH : M ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1,hM.2⟩
  let := (localModule_reduced_from_source hG T hH).normal
  let := (localModule_reduced_from_source hG T hH).elementary
  rcases local_natural_action_from_source
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    hG T hempty hM hu hcase hJ with hp | ho
  · obtain ⟨c,e,hc⟩ := hp
    exact plane_fixed_pair_centralizer_factorization T hM.2 D c e hc
  · obtain ⟨d⟩ := ho
    exact orthogonal_fixed_pair_centralizer_factorization T hM.2 d hJ D

omit [Finite G] in
theorem fixed_pair_control_proper_of_factorization_failure
    (T : Sylow 2 G) {M : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (D : CharacteristicPair (baumann (T : Subgroup G)))
    (hcent : M ⊓ centralizer (ChapterC.RankOne.ChiProduct.FixedPair.firstSeed T D : Set G) =
      (M ⊓ centralizer (localModule T M : Set G)) ⊔ (T : Subgroup G))
    (hfail : M ≠ (M ⊓ centralizer (localModule T M : Set G)) ⊔
      (M ⊓ normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G))) :
    (M ⊓ centralizer (ChapterC.RankOne.ChiProduct.FixedPair.firstSeed T D : Set G)) ⊔
      (M ⊓ normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G)) < M := by
  let : D.second.Characteristic := D.second_characteristic
  have hTN : (T : Subgroup G) ≤ M ⊓
      normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G) :=
    le_inf hTM (((T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)).trans
      (normalizer_le_normalizer_characteristic_image _ D.second))
  rw [hcent,sup_assoc,sup_eq_right.mpr hTN]
  exact lt_of_le_of_ne (sup_le inf_le_left inf_le_left) (Ne.symm hfail)

theorem source_fixed_pair_control_proper
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hcase : M ≠ Mc ∨ Nat.card (centralInvolutions T) = 2)
    (D : CharacteristicPair (baumann (T : Subgroup G)))
    (hfail : M ≠ (M ⊓ centralizer (localModule T M : Set G)) ⊔
      (M ⊓ normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G))) :
    (M ⊓ centralizer (ChapterC.RankOne.ChiProduct.FixedPair.firstSeed T D : Set G)) ⊔
      (M ⊓ normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G)) < M := by
  have hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G) := by
    intro hJ
    let : D.second.Characteristic := D.second_characteristic
    exact hfail (source_centralizing_factorization hG T hM hJ D.second)
  exact fixed_pair_control_proper_of_factorization_failure T hM.2 D
    (source_noncentral_seed_centralizer hG T hempty hM hu hcase hJ D) hfail
end CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl
