module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks.Sections
public import Theory.SpecificGroups.FFG2DerivedCenter.Even

/-!
# Model maps on the actual G₂ parabolic pullbacks

The coordinate map is surjective onto the derived model. Restricting it
to each parabolic gives a surjection onto that parabolic's intersection
with the derived model, with a two-group kernel. The center calculation
also shows that the seed map kills every central component overlap.
Thus these maps work for G₂(2)′ and arbitrary central two-covers of G₂(4).

These are the model inputs for the commuting-component orbit construction
in Aschbacher–Smith 2.3.9(7), printed p.526.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2
namespace ParabolicCoordinates
variable {G : Type*} [Group G] {L S : Subgroup G} (d : ParabolicCoordinates L S)

/-- The actual model map with its codomain restricted to its derived range. -/
def derivedMap : L →* commutator (Atlas.G2.Model d.field) :=
  d.modelMap.codRestrict _ (fun x => d.model_range ▸ (show d.modelMap x ∈ d.modelMap.range from ⟨x, rfl⟩))

theorem derivedMap_surjective : Function.Surjective d.derivedMap := by
  intro x
  have hx : x.val ∈ d.modelMap.range := by rw [d.model_range]; exact x.property
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩

theorem modelMap_center (x : L) (hx : x ∈ center L) : d.modelMap x = 1 := by
  have hc : d.derivedMap x ∈ center _ := by
    rw [mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := d.derivedMap_surjective y
    simpa only [map_mul] using congrArg d.derivedMap (mem_center_iff.mp hx y)
  rw [Theory.SpecificGroups.g2_derived_even_center_eq_bot, mem_bot] at hc
  exact congrArg Subtype.val hc

/-- Restrict the derived-range map to the literal parabolic pullback in L. -/
def pullbackMapIn (Q : Subgroup (Atlas.G2.Model d.field)) :
    Q.comap d.modelMap →* Q.subgroupOf (commutator (Atlas.G2.Model d.field)) :=
  d.derivedMap.subgroupComap (Q.subgroupOf _)

/-- The seed projection, retaining the pullback as an ambient subgroup. -/
noncomputable def pullbackMap (Q : Subgroup (Atlas.G2.Model d.field)) :
    (Q.comap d.modelMap).map L.subtype →* Q.subgroupOf (commutator (Atlas.G2.Model d.field)) :=
  (d.pullbackMapIn Q).comp
    ((Q.comap d.modelMap).equivMapOfInjective L.subtype L.subtype_injective).symm.toMonoidHom

theorem pullbackMap_surjective (Q : Subgroup (Atlas.G2.Model d.field)) :
    Function.Surjective (d.pullbackMap Q) :=
  (d.derivedMap.subgroupComap_surjective_of_surjective _ d.derivedMap_surjective).comp
    ((Q.comap d.modelMap).equivMapOfInjective L.subtype L.subtype_injective).symm.surjective

theorem pullbackMap_kernel_two (Q : Subgroup (Atlas.G2.Model d.field)) :
    IsPGroup 2 (d.pullbackMap Q).ker := by
  have hk : IsPGroup 2 d.modelMap.ker := by
    rcases d.model_kernel with hk | ⟨_, hk, hZ, _⟩
    · rw [hk]; exact IsPGroup.of_bot
    · rw [hk, hZ]; exact pCore_isPGroup
  have he : (d.pullbackMapIn Q).ker =
      d.modelMap.ker.subgroupOf (Q.comap d.modelMap) := by
    ext x
    change (⟨d.derivedMap x, x.property⟩ : Q.subgroupOf _) = 1 ↔ d.modelMap x = 1
    exact Subtype.ext_iff.trans Subtype.ext_iff
  change IsPGroup 2 ((d.pullbackMapIn Q).comp _).ker
  rw [← MonoidHom.comap_ker, he]
  exact hk.comap_subtype.comap_of_injective _
    ((Q.comap d.modelMap).equivMapOfInjective L.subtype L.subtype_injective).symm.injective

theorem pullbackMap_kills_center (Q : Subgroup (Atlas.G2.Model d.field))
    (x : (Q.comap d.modelMap).map L.subtype)
    (hx : (⟨x.val, map_subtype_le (Q.comap d.modelMap) x.property⟩ : L) ∈ center L) :
    d.pullbackMap Q x = 1 := by
  let e := (Q.comap d.modelMap).equivMapOfInjective L.subtype L.subtype_injective
  have he : ((e.symm x : Q.comap d.modelMap) : L) =
      (⟨x.val, map_subtype_le (Q.comap d.modelMap) x.property⟩ : L) := by
    apply Subtype.ext
    exact congrArg (fun y : (Q.comap d.modelMap).map L.subtype => (y : G))
      (e.apply_symm_apply x)
  apply Subtype.ext
  apply Subtype.ext
  change d.modelMap (e.symm x) = 1
  rw [he]
  exact d.modelMap_center _ hx

end ParabolicCoordinates
end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2

end
