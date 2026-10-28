module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalitySporadicModelsHigmanSimsLocals
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.Overgroups

/-!
# Higman--Sims in the moved-component obstruction

The certified 270-double-coset cover puts each proper full-Sylow overgroup
in the central-involution local or the elementary-eight normalizer.
Their component restrictions lift through the established solvable kernels.
The whole-group case uses the inherited simplicity and perfection.

The quotient application uses the original normalized overcomponent modulo
its solvable radical, discharging A.3.12(18) in the embedding restriction
1.2.8(1), printed pp.47--48 and 506.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.MovedMaximality
open Sporadic.LeechRelated.HS

private theorem higman_sims_unique [IsSimpleGroup Carrier] [Group.IsPerfect Carrier] :
    SylowOvergroupComponentUnique Carrier := by
  apply SylowOvergroupComponentUnique.of_proper_overgroups
  intro S P hSP hP B C hB hC
  have hidx : ¬ 2 ∣ P.index := fun h => S.not_dvd_index (h.trans (index_dvd_of_le hSP))
  obtain ⟨g,hg⟩ := exists_conj_overgroup_of_index_primeTo EvenLocalCandidates.subgroup P
    (IsPGroup.of_card (n := 9) EvenLocalCandidates.subgroup_card) hidx
  let e := MulAut.conj g
  let R := P.comap e.toMonoidHom
  have hR : R ≠ ⊤ := by
    intro ht
    apply hP
    have hm := congrArg (Subgroup.map e.toMonoidHom) ht
    change (P.comap e.toMonoidHom).map e.toMonoidHom =
      (⊤ : Subgroup Carrier).map e.toMonoidHom at hm
    simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
      map_top_of_surjective e.toMonoidHom e.surjective] using hm
  let f : R ≃* P := (e.subgroupMap R).trans
    (MulEquiv.subgroupCongr (map_comap_eq_self_of_surjective e.surjective P))
  apply (map_injective (f := f.symm.toMonoidHom) f.symm.injective)
  have hSR : ((S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective) : Subgroup Carrier) ≤ R := by
    change (S : Subgroup Carrier).map e.symm.toMonoidHom ≤ P.comap e.toMonoidHom
    rw [comap_equiv_eq_map_symm']
    exact map_mono hSP
  rcases SylowOvergroups.proper_overgroup_le R hg hR with h | h
  · exact SylowOvergroupComponentUnique.eq_of_le_overgroup _ hSR h
      higman_sims_central_local_unique
      (hB.map_equiv f.symm) (hC.map_equiv f.symm)
  · exact SylowOvergroupComponentUnique.eq_of_le_overgroup _ hSR h
      (higman_sims_large_local_unique 2 (by decide))
      (hB.map_equiv f.symm) (hC.map_equiv f.symm)

variable {G : Type*} [Group G] [Finite G]

/-- Full-Sylow component uniqueness for the actual degree-100 Higman--Sims model. -/
theorem higman_sims_sylow_overgroup_component_unique [IsSimpleGroup G] [Group.IsPerfect G]
    (hm : Nonempty (G ≃* Carrier)) : SylowOvergroupComponentUnique G := by
  obtain ⟨e⟩ := hm
  let := e.symm.isSimpleGroup
  let := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact SylowOvergroupComponentUnique.of_equiv e higman_sims_unique

/-- Exclude HS for the literal radical quotient of the original normalized overcomponent. -/
theorem moved_normalized_not_higman_sims_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G)) :
    let C := K.subgroupOf (K ⊔ (T : Subgroup G))
    let Q := C ⧸ solvableRadical C
    ¬ Nonempty (Q ≃* Carrier) := by
  dsimp only
  intro hmodel
  obtain ⟨hs, _, _, hu⟩ := moved_normalized_remaining_simple_quotient hG T hB hK hBK hTK hm
  let := hs
  let := hK.1.perfect
  exact hu (higman_sims_sylow_overgroup_component_unique hmodel)

/-- The full sporadic predicate now has only J₄, He and Ru left. -/
theorem sporadic_model_remaining_after_higman_sims [IsSimpleGroup G] [Group.IsPerfect G]
    (hspor : ChapterA.Section02.IsTheoremCSporadicModel G)
    (hu : ¬ SylowOvergroupComponentUnique G) :
    ∃ name : ClassificationModels.SporadicName,
      (name = .j4 ∨ name = .he ∨ name = .ru) ∧
      Nonempty (G ≃* name.Carrier) := by
  obtain ⟨name,hn,iso⟩ := sporadic_model_remaining_after_janko_two hspor hu
  rcases hn with h4 | rfl | hrest
  · exact ⟨name,Or.inl h4,iso⟩
  · exact (hu (higman_sims_sylow_overgroup_component_unique iso)).elim
  · exact ⟨name,Or.inr hrest,iso⟩

/-- Apply the three-row reduction to the original normalized overcomponent. -/
theorem moved_normalized_remaining_sporadic_quotient_after_higman_sims
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G)) :
    let C := K.subgroupOf (K ⊔ (T : Subgroup G))
    let Q := C ⧸ solvableRadical C
    ChapterA.Section02.IsTheoremCSporadicModel Q →
      ∃ name : ClassificationModels.SporadicName,
        (name = .j4 ∨ name = .he ∨ name = .ru) ∧
        Nonempty (Q ≃* name.Carrier) := by
  dsimp only
  intro hmodel
  obtain ⟨hs, _, _, hu⟩ := moved_normalized_remaining_simple_quotient hG T hB hK hBK hTK hm
  let := hs
  let := hK.1.perfect
  exact sporadic_model_remaining_after_higman_sims hmodel hu

end CFSG.Quasithin.Chapter1.Section02.MovedMaximality
