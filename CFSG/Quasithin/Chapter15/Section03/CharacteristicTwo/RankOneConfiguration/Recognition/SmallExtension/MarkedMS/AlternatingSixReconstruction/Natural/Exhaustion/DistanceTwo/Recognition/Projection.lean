module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.Layer
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Normalizer

/-!
# The actual six-letter marking of the characteristic replacement

The natural central quotient carries a faithful action of the two-core
quotient. Its component image is the literal natural A₆ image, whose linear
normalizer is the natural S₆ image. Factoring through that image supplies a
permutation marking with kernel exactly the replacement two-core. This
argument retains the original central cover and does not assert surjectivity
onto S₆; that follows separately from the paired orbit's strict index bound.

Source: MS93 (3.6), printed p.871, and Section 7, pp.932--933.
-/

@[expose] public noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Recognition
open LargeDistance
open Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R)

theorem replacementAction_component_image :
    (replacementComponent d).map (replacementAction h e hz hn d).asGroupHom =
      alternatingImage := by
  ext f
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨LargeDistance.componentMap h e hz hn d ⟨k, hk⟩, ?_⟩
    apply Units.ext
    apply LinearMap.ext
    intro v
    exact (replacementAction_component h e hz hn d ⟨k, hk⟩ v).symm
  · rintro ⟨a, rfl⟩
    obtain ⟨k, hk⟩ := LargeDistance.componentMap_surjective h e hz hn d a
    refine ⟨k, k.property, ?_⟩
    apply Units.ext
    apply LinearMap.ext
    intro v
    rw [← hk]
    exact replacementAction_component h e hz hn d k v

theorem replacementAction_mem_symmetric (g : d.overgroup) :
    (replacementAction h e hz hn d).asGroupHom g ∈ symmetricImage := by
  let := replacementComponent_normal h d
  have hg : g ∈ normalizer (replacementComponent d : Set d.overgroup) := by
    rw [normalizer_eq_top]
    trivial
  have hm := (replacementComponent d).le_normalizer_map
    (replacementAction h e hz hn d).asGroupHom (mem_map_of_mem _ hg)
  rw [replacementAction_component_image h e hz hn d, normalizer_alternatingImage] at hm
  exact hm

noncomputable def sourceProjection : d.overgroup →* Equiv.Perm (Fin 6) :=
  (MonoidHom.ofInjective symmetricHom_injective).symm.toMonoidHom.comp
    ((replacementAction h e hz hn d).asGroupHom.codRestrict symmetricImage
      (replacementAction_mem_symmetric h e hz hn d))

theorem sourceProjection_action (g : d.overgroup) :
    BinaryPermutation.naturalRepresentation (Fin 6) (sourceProjection h e hz hn d g) =
      replacementAction h e hz hn d g := by
  have he := (MonoidHom.ofInjective symmetricHom_injective).apply_symm_apply
    (⟨(replacementAction h e hz hn d).asGroupHom g,
      replacementAction_mem_symmetric h e hz hn d g⟩ : symmetricImage)
  exact congrArg (fun x : symmetricImage => x.val.val) he

theorem sourceProjection_kernel :
    (sourceProjection h e hz hn d).ker = pCore 2 d.overgroup := by
  have he : (BinaryPermutation.naturalRepresentation (Fin 6)).comp
      (sourceProjection h e hz hn d) = replacementAction h e hz hn d :=
    MonoidHom.ext (sourceProjection_action h e hz hn d)
  rw [← replacementAction_kernel h e hz hn d, ← he,
    MonoidHom.ker_comp_of_injective _ _
      (BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide))]

theorem sourceProjection_component :
    (pResidual 2 d.overgroup).map (sourceProjection h e hz hn d) =
      alternatingGroup (Fin 6) := by
  rw [replacement_residual h d]
  have he (k : replacementComponent d) : sourceProjection h e hz hn d k =
      (LargeDistance.componentMap h e hz hn d k : Equiv.Perm (Fin 6)) := by
    apply BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
    rw [sourceProjection_action]
    exact LinearMap.ext (replacementAction_component h e hz hn d k)
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [he ⟨k, hk⟩]
    exact (LargeDistance.componentMap h e hz hn d ⟨k, hk⟩).property
  · intro hg
    obtain ⟨k, hk⟩ := LargeDistance.componentMap_surjective h e hz hn d ⟨g, hg⟩
    exact ⟨k, k.property, (he k).trans (congrArg Subtype.val hk)⟩

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Recognition
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
