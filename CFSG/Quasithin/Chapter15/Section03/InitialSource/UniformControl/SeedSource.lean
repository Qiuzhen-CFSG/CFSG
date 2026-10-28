module
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.PlaneSeed
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.OrthogonalSeed
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.NaturalModels.Action
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# The fixed characteristic seed in the original noncentral source action

The original 14.1.7 alternatives identify the same local module with a natural
binary plane or the natural orthogonal four-space. In both cases the centralizer
of the first member's central restriction is exactly the module centralizer
times the given Sylow subgroup. The characteristic second member is normalized
by that Sylow subgroup, giving precisely the inclusion used in 14.1.11.

All action coordinates and the earlier A/C classifications are constructed.
The pair is kept fixed, so this applies to the single pair chosen before all
maximal local overgroups. Source: Aschbacher--Smith 14.1.11, printed p.978.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl
open ChapterB ChapterC.GlaubermanNiles
universe u
variable {G : Type u} [Group G] [Finite G]

theorem source_noncentral_seed_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hcase : M ≠ Mc ∨ Nat.card (centralInvolutions T) = 2)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (D : CharacteristicPair (baumann (T : Subgroup G))) :
    M ⊓ centralizer (ChapterC.RankOne.ChiProduct.FixedPair.firstSeed T D : Set G) =
      (M ⊓ centralizer (localModule T M : Set G)) ⊔ (T : Subgroup G) := by
  let hH : M ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1,hM.2⟩
  let := (localModule_reduced_from_source hG T hH).normal
  let := (localModule_reduced_from_source hG T hH).elementary
  rcases local_natural_action_from_source
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
      hG T hempty hM hu hcase hJ with h | h
  · obtain ⟨c,e,hc⟩ := h
    exact plane_fixed_pair_centralizer_factorization T hM.2 D c e hc
  · obtain ⟨d⟩ := h
    exact orthogonal_fixed_pair_centralizer_factorization T hM.2 d hJ D

/-- The literal containment before the fixed-pair C.1.28 application. -/
theorem source_noncentral_seed_le_characteristic_supplement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hcase : M ≠ Mc ∨ Nat.card (centralInvolutions T) = 2)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (D : CharacteristicPair (baumann (T : Subgroup G))) :
    M ⊓ centralizer (ChapterC.RankOne.ChiProduct.FixedPair.firstSeed T D : Set G) ≤
      (M ⊓ centralizer (localModule T M : Set G)) ⊔
        (M ⊓ normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G)) := by
  rw [source_noncentral_seed_centralizer hG T hempty hM hu hcase hJ D]
  apply sup_le_sup_left
  let : D.second.Characteristic := D.second_characteristic
  exact le_inf hM.2 (((T : Subgroup G).le_normalizer.trans
    (normalizer_le_normalizer_baumann _)).trans
      (normalizer_le_normalizer_characteristic_image _ D.second))

end CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl
