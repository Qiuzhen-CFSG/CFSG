module

public import CFSG.Quasithin.Chapter6.Section01.SourceHStarE23
public import CFSG.Quasithin.Chapter6.SourceDefs.ReducedImage
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure

/-!
# The source enlargement to `R₂(LT)`

The printed 6.1.5 argument enlarges the selected reduced module to `R₂(LT)`.
This file records exactly the reusable part of that move: the intrinsic
reduced subgroup is a member of the ambient reduced family, contains the
Sylow omega-center, and still has nontrivial commutator with `L`.  The
rank-one input does not require an A₅ model exclusion. The existing theorem
signature retains that premise for compatibility with its source caller;
`SourceHStarFullEnlargement` proves preservation of all of `Hypothesis611`.

Source: Aschbacher--Smith 6.1.4--6.1.5, printed pp.665--666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source

variable {G : Type*} [Group G]

/-- `R₂(H)` itself is a reduced member of the source family. -/
theorem reducedSubgroup_mem (H : Subgroup G) :
    reducedSubgroup H ∈ reducedFamily H := by
  have he : (reducedSubgroup H).subgroupOf H = reducedTwoSubgroup H := by
    rw [reducedSubgroup_eq_map]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  have hr : IsPReduced 2 ((reducedSubgroup H).subgroupOf H) :=
    he.symm ▸ isPReduced_reducedPSubgroup
  refine ⟨?_, ?_, hr.normal, hr.quotient_pCore_eq_bot⟩
  · rw [reducedSubgroup_eq_map]
    exact map_subtype_le _
  · rw [reducedSubgroup_eq_map]
    let := (isPReduced_reducedPSubgroup (p := 2) (G := H)).elementary
    exact IsElementaryAbelian.map _

namespace Hypothesis611

variable [Finite G] {T : Sylow 2 G}
  {L M V : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

theorem reduced_enlargement_nontrivial :
    layer L (reducedSubgroup (L ⊔ (T : Subgroup G))) ≠ ⊥ := by
  intro he
  apply h.nontrivial_action
  exact le_bot_iff.mp (he ▸ layer_le_reduced_layer h.V_mem)

theorem omega_le_reduced_enlargement :
    omegaOneCenterAmbient (T : Subgroup G) ≤
      reducedSubgroup (L ⊔ (T : Subgroup G)) := by
  let J := L ⊔ (T : Subgroup G)
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hc : centralizer (pCore 2 J : Set J) ≤ pCore 2 J :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
      (h.simpleQTKE.evenCharacteristic T)
      ⟨h.local_mem.1.prop.2.2, show (T : Subgroup G) ≤ J from le_sup_right⟩)
  have hr := omegaCenter_normalClosure_reduced S hc
  have he : (omegaOneCenterAmbient (S : Subgroup J)).map J.subtype =
      omegaOneCenterAmbient (T : Subgroup G) := by
    rw [← omegaOneCenterAmbient_map_injective J.subtype J.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le le_sup_right
  rw [← he, reducedSubgroup_eq_map]
  exact map_mono ((show omegaOneCenterAmbient (S : Subgroup J) ≤
    normalClosure (omegaOneCenterAmbient (S : Subgroup J) : Set J) from
      le_normalClosure).trans hr.le_reducedPSubgroup)

/-- The enlarged subgroup supplies the same rank-one input contract. The A₅
premise is redundant for this contract and is retained for compatibility. -/
theorem rankOneInput_of_reduced_enlargement
    (hout : Chapter3.HasMaximalOutside T M)
    (hnotA5 : ¬ IsOneOrTwoA5Modules L
      (layer L (reducedSubgroup (L ⊔ (T : Subgroup G))))) :
    RankOneGeneric.Input KnownSimple.IsKnownSimple T L
      (reducedSubgroup (L ⊔ (T : Subgroup G))) n := by
  have _hnotA5 := hnotA5
  refine ⟨h.simpleQTKE, h.local_mem, h.n_gt_one, h.quotient_model,
    h.maximal_eq_normalizer_L ▸ h.maximal, h.sylow_normalizes_L,
    reducedSubgroup_mem (L ⊔ (T : Subgroup G)), h.reduced_enlargement_nontrivial, ?_⟩
  exact h.maximal_eq_normalizer_L ▸ hout

end Hypothesis611
end CFSG.Quasithin.Chapter6.Source
