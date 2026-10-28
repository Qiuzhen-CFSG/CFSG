module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.ThompsonAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.Lifting.SourceInputs
public import Theory.GroupTheory.CComponent.ResidualLifting

/-!
# Lift a prescribed star component with its orbit bound

Take the literal inverse image of E in J(I). The complete universal A.3.9
input, applied after quotienting that inverse image by its two-core, says
that its C-components generate its solvable residual. At least one has
nontrivial image in E; perfectness, subnormality and E's minimality make
that image exactly E. This proves the lift without a solvability assumption
on C_I(U_I) or its intersection with J(I).

Normality of J(I) in I transfers the lift to a C-component of I. A.3.8,
applied to the actual two-core quotient of I, bounds its normalizer's
relative index by two. The ambient image and relative subgroup transports
are literal. No quotient component is selected here.

The universal A.3.8 and A.3.9 inputs remain obligations of the earlier
source owner. The deduction needs only finite SQTK I, so it applies to both
rank branches with all the earlier Chapter 15 hypotheses supplied by the
consumer. The escape condition then gives L not contained in M.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.8–9,
1.2.1(1),(3), and 15.3.15(2)/26(2), printed pp.45–46, 503–504, 1125, 1130.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
open StarSelection.Lifting
universe u
variable {G : Type u} [Group G] [Finite G]
namespace LocalData
variable (d : LocalData G)

/-- Lift the specified component of the actual Thompson star image. The
complete source inputs imply the required preimage generation and orbit
bound; neither a lift nor solvability of the star kernel is assumed. -/
theorem exists_thompsonStar_component_lift {I : Subgroup G} {K : GroupClass.{u}}
    (h38 : A38Input K) (h39 : A39Input K) (hI : IsSQTK K I)
    (E : Subgroup (d.thompsonStar I))
    (hE : Theory.GroupTheory.IsComponent (d.thompsonStar I) E) :
    ∃ L : Subgroup G, L ≤ Stellmacher.elementaryAbelianMaxJ I ∧
      (L.subgroupOf (Stellmacher.elementaryAbelianMaxJ I)).IsCComponent ∧
      d.starImage I L = E.map (d.thompsonStar I).subtype ∧
      (normalizer (L : Set G)).relIndex I ≤ 2 := by
  let J := Stellmacher.elementaryAbelianMaxJ I
  have hJI : J ≤ I := sSup_le fun _ hA => hA.1
  let f : J →* d.thompsonStar I := d.componentStarMap hJI
  have hf : Function.Surjective f := d.componentStarMap_surjective hJI
  have hJ : IsSQTK K J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJI)).mp (hI.subgroup (J.subgroupOf I))
  obtain ⟨D, hD, hDE⟩ := exists_cComponent_map_eq_of_preimage_layer f hf hE.isCComponent
    (layer_eq_residual h39 (hJ.subgroup (E.comap f)))
  let L := D.map J.subtype
  have hLJ : L ≤ J := map_subtype_le D
  have hL : (L.subgroupOf J).IsCComponent := by
    simpa only [L, subgroupOf, comap_map_eq_self_of_injective J.subtype_injective] using hD
  refine ⟨L, hLJ, hL, ?_, ?_⟩
  · rw [← hDE]
    change (L.subgroupOf I).map (d.starMap I) = _
    have he : L.subgroupOf I = D.map (inclusion hJI) := by
      apply map_injective I.subtype_injective
      rw [map_subgroupOf_eq_of_le (hLJ.trans hJI), map_map, subtype_comp_inclusion]
    rw [he, map_map, map_map]
    rfl
  · have hLI := thompson_component_in hLJ hL
    have hb := cComponent_normalizer_index_le_two h38 hI hLI
    rwa [← subgroupOf_normalizer_eq (hLJ.trans hJI)] at hb

/-- The prescribed escaping star component lifts outside M, with literal
image equality and the same bound in I. This is the output used by the
parent's candidate assembly. -/
theorem exists_outside_thompsonStar_component_lift {I : Subgroup G} {K : GroupClass.{u}}
    (h38 : A38Input K) (h39 : A39Input K) (hI : IsSQTK K I)
    (E : Subgroup (d.thompsonStar I))
    (hE : Theory.GroupTheory.IsComponent (d.thompsonStar I) E)
    (houtside : ¬ E.map (d.thompsonStar I).subtype ≤ d.starImage I d.M) :
    ∃ L : Subgroup G, L ≤ Stellmacher.elementaryAbelianMaxJ I ∧
      (L.subgroupOf (Stellmacher.elementaryAbelianMaxJ I)).IsCComponent ∧
      d.starImage I L = E.map (d.thompsonStar I).subtype ∧
      (normalizer (L : Set G)).relIndex I ≤ 2 ∧ ¬ L ≤ d.M := by
  obtain ⟨L, hLJ, hL, himage, horbit⟩ :=
    d.exists_thompsonStar_component_lift h38 h39 hI E hE
  refine ⟨L, hLJ, hL, himage, horbit, ?_⟩
  intro hLM
  apply houtside
  rw [← himage]
  exact map_mono (comap_mono hLM)

end LocalData
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
