module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.Marking
public import Theory.Representation.BinaryAlternatingSixNaturalNormalizer

/-!
# The literal six-letter marking of the replacement action

The full linear normalizer of the natural A₆ image is the natural S₆.
Normality and surjectivity of the marked component therefore place every
replacement operator in that image. Faithfulness recovers a unique map to
S₆, with kernel the actual replacement two-core and component image A₆.
Its range is A₆ or S₆; excluding the first alternative remains a source
argument. The entire central cover is equivariant for the same marking.

Source: MS93 (3.8), pp.877--879, and the natural four-space normalizer
calculation in Aschbacher--Smith K.1.1, p.452.
-/

public noncomputable section
open Subgroup Representation
open Representation.BinaryAlternatingSixNaturalNormalizer
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R)

private theorem natural_injective : Function.Injective naturalLinearAction := by
  intro g k he
  apply BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
  apply LinearMap.ext
  intro v
  exact LinearEquiv.congr_fun he v

private theorem exists_projection_of_natural
    {M : Type*} [Group M] (N : Subgroup M) [N.Normal]
    (σ : Representation (ZMod 2) M Vector)
    (a : N →* alternatingGroup (Fin 6)) (ha : Function.Surjective a)
    (hcompat : ∀ (k : N) v, σ k v = BinaryPermutation.naturalRepresentation (Fin 6) (a k) v) :
    ∃ p : M →* Equiv.Perm (Fin 6), ∀ g v,
      σ g v =
        BinaryPermutation.naturalRepresentation (Fin 6) (p g) v := by
  let f : M →* (Vector ≃ₗ[ZMod 2] Vector) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Vector).toMonoidHom.comp
      (σ).asGroupHom
  have he (k : N) :
      f k = naturalLinearAction (a k).val := by
    apply LinearEquiv.ext
    intro v
    exact hcompat k v
  have himage : (N).map f = alternatingLinearImage := by
    ext t
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨a ⟨k, hk⟩, (he ⟨k, hk⟩).symm⟩
    · rintro ⟨k, rfl⟩
      obtain ⟨l, hl⟩ := ha k
      refine ⟨l, l.property, ?_⟩
      rw [he, hl]
      rfl
  have hmem (g : M) : f g ∈ naturalLinearAction.range := by
    rw [← Representation.BinaryAlternatingSixNaturalNormalizer.normalizer, ← himage]
    apply Subgroup.le_normalizer_map f
    exact ⟨g, by rw [Subgroup.normalizer_eq_top]; trivial, rfl⟩
  let j := f.codRestrict naturalLinearAction.range hmem
  let p : M →* Equiv.Perm (Fin 6) :=
    (MonoidHom.ofInjective natural_injective).symm.toMonoidHom.comp j
  refine ⟨p, ?_⟩
  intro g v
  have hp : naturalLinearAction (p g) = f g :=
    MonoidHom.apply_ofInjective_symm natural_injective (j g)
  exact (LinearEquiv.congr_fun hp v).symm


private theorem exists_projection :
    ∃ p : d.overgroup →* Equiv.Perm (Fin 6), ∀ g v,
      replacementAction h e hz hn d g v =
        BinaryPermutation.naturalRepresentation (Fin 6) (p g) v := by
  let := replacementComponent_normal h d
  exact exists_projection_of_natural (replacementComponent d)
    (replacementAction h e hz hn d) (componentMap h e hz hn d)
    (componentMap_surjective h e hz hn d) (replacementAction_component h e hz hn d)

/-- The six-letter map determined by the literal natural quotient action. -/
noncomputable def projection : d.overgroup →* Equiv.Perm (Fin 6) :=
  Classical.choose (exists_projection h e hz hn d)

theorem projection_action (g : d.overgroup) (v : Vector) :
    replacementAction h e hz hn d g v =
      BinaryPermutation.naturalRepresentation (Fin 6) (projection h e hz hn d g) v :=
  Classical.choose_spec (exists_projection h e hz hn d) g v

theorem projection_kernel : (projection h e hz hn d).ker = pCore 2 d.overgroup := by
  have he : (BinaryPermutation.naturalRepresentation (Fin 6)).comp
      (projection h e hz hn d) = replacementAction h e hz hn d := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    exact (projection_action h e hz hn d g v).symm
  rw [← replacementAction_kernel h e hz hn d, ← he,
    MonoidHom.ker_comp_of_injective _ _
      (BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide))]

theorem projection_component (k : replacementComponent d) :
    projection h e hz hn d k = (componentMap h e hz hn d k : Equiv.Perm (Fin 6)) := by
  apply BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
  apply LinearMap.ext
  intro v
  exact (projection_action h e hz hn d k v).symm.trans
    (replacementAction_component h e hz hn d k v)

theorem component_image : (replacementComponent d).map (projection h e hz hn d) =
    alternatingGroup (Fin 6) := by
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [projection_component h e hz hn d ⟨k, hk⟩]
    exact (componentMap h e hz hn d ⟨k, hk⟩).property
  · intro hg
    obtain ⟨k, hk⟩ := componentMap_surjective h e hz hn d ⟨g, hg⟩
    refine ⟨k, k.property, ?_⟩
    rw [projection_component, hk]

theorem alternating_le_range :
    alternatingGroup (Fin 6) ≤ (projection h e hz hn d).range := by
  rw [← component_image h e hz hn d]
  exact Subgroup.map_le_range _ _

/-- The normalizer calculation leaves precisely the derived and full images. -/
theorem range_alternatives :
    (projection h e hz hn d).range = alternatingGroup (Fin 6) ∨
      Function.Surjective (projection h e hz hn d) := by
  have hd : (projection h e hz hn d).range.index ∣ 2 := by
    simpa only [alternatingGroup.index_eq_two] using
      index_dvd_of_le (alternating_le_range h e hz hn d)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hi | hi
  · exact Or.inr (MonoidHom.range_eq_top.mp (index_eq_one.mp hi))
  · exact Or.inl (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi)

/-- Direct construction of the required action after excluding the derived image. -/
noncomputable def fullSymmetricAction
    (hex : (projection h e hz hn d).range ≠ alternatingGroup (Fin 6)) :
    FullSymmetricAction h e hz hn d where
  projection := projection h e hz hn d
  surjective := (range_alternatives h e hz hn d).resolve_left hex
  action := projection_action h e hz hn d

/-- Every full marking equals this canonical map, since the natural action is faithful. -/
theorem fullSymmetricAction_projection_unique (s : FullSymmetricAction h e hz hn d) :
    s.projection = projection h e hz hn d := by
  apply MonoidHom.ext
  intro g
  apply BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
  apply LinearMap.ext
  intro v
  exact (s.action g v).symm.trans (projection_action h e hz hn d g v)

/-- The nonsplit central cover is equivariant for this same six-letter map. -/
theorem cover_conjugate (g : d.overgroup) (v w : replacementMoved d)
    (hw : (w : d.overgroup) = g * (v : d.overgroup) * g⁻¹) :
    (coverProjection h e hz hn d w).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (projection h e hz hn d g)
        (coverProjection h e hz hn d v).toAdd :=
  (coverProjection_conjugate h e hz hn d g v w hw).trans
    (projection_action h e hz hn d g _)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
