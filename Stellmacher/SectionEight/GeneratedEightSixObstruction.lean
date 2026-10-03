module

public import Stellmacher.LaterDefs
public import Theory.SpecificGroups.PSL3Two.NonSolvable

/-!
# Ambient normalizer obstructions for generated Section Eight

An injective embedding carries the normalizer of a subgroup into the
normalizer of its image. Nonsolvability therefore passes to the latter.
For a nontrivial two-subgroup this gives an actual nonsolvable two-local
subgroup of the ambient group, without descending Hypothesis Two.

The two final interfaces consume the normalizer conclusions of (8.6)(b)
and (8.6)(c), respectively. They do not assert either classification branch.
The projective special linear model uses its independently proved intrinsic
nonsolvability. Source: `refs/files/stellmacher-n-group.pdf`, pp. 41, 44–45.
-/

namespace Stellmacher.SectionEight

open Later

universe u v

public theorem nonsolvable_normalizer_map_of_injective
    {G : Type u} {H : Type v} [Group G] [Group H]
    (embedding : G →* H) (hinjective : Function.Injective embedding)
    (W : Subgroup G) (hbad : IsNonsolvableNormalizer W) :
    IsNonsolvableNormalizer (W.map embedding) := by
  intro hsolvable
  let normalizerMap : Subgroup.normalizer (W : Set G) →*
      Subgroup.normalizer (W.map embedding : Set H) :=
    (embedding.comp (Subgroup.normalizer (W : Set G)).subtype).codRestrict
      (Subgroup.normalizer (W.map embedding : Set H))
      (fun element => Subgroup.le_normalizer_map embedding
        (Subgroup.mem_map_of_mem embedding element.property))
  have hinjectiveMap : Function.Injective normalizerMap := by
    intro first second heq
    apply Subtype.ext
    apply hinjective
    exact congrArg Subtype.val heq
  let : Group.IsSolvable (Subgroup.normalizer (W.map embedding : Set H)) := hsolvable
  exact hbad (Group.isSolvable_of_isSolvable_injective hinjectiveMap)

public theorem ambient_bad_local_of_nonsolvable_normalizer
    {G : Type u} {H : Type v} [Group G] [Group H]
    (embedding : G →* H) (hinjective : Function.Injective embedding)
    (W : Subgroup G) (hne : W ≠ ⊥) (htwo : IsPGroup 2 W)
    (hbad : IsNonsolvableNormalizer W) :
    ∃ U : Subgroup H, IsTwoLocal U ∧ ¬ Group.IsSolvable U := by
  refine ⟨Subgroup.normalizer (W.map embedding : Set H), ?_,
    nonsolvable_normalizer_map_of_injective embedding hinjective W hbad⟩
  exact ⟨W.map embedding,
    fun hbot => hne ((Subgroup.map_eq_bot_iff_of_injective W hinjective).mp hbot),
    htwo.map embedding, rfl⟩

public theorem ambient_bad_local_of_elementary_sixteen_normalizer
    {G : Type u} {H : Type v} [Group G] [Group H]
    (embedding : G →* H) (hinjective : Function.Injective embedding)
    (W : Subgroup G) (helementary : IsElementaryAbelianSubgroup 2 W)
    (hcard : Nat.card W = 2 ^ 4) (hbad : IsNonsolvableNormalizer W) :
    ∃ U : Subgroup H, IsTwoLocal U ∧ ¬ Group.IsSolvable U := by
  have hne : W ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  exact ambient_bad_local_of_nonsolvable_normalizer embedding hinjective W hne
    helementary.isPGroup hbad

public theorem ambient_bad_local_of_psl3_two_normalizer_quotient
    {G : Type u} {H : Type v} [Group G] [Group H]
    (embedding : G →* H) (hinjective : Function.Injective embedding)
    (W : Subgroup G) (hne : W ≠ ⊥) (htwo : IsPGroup 2 W)
    (hmodel : QuotientIsModel (Subgroup.normalizer (W : Set G))
      (Subgroup.centralizer (W : Set G)) L3Two) :
    ∃ U : Subgroup H, IsTwoLocal U ∧ ¬ Group.IsSolvable U := by
  apply ambient_bad_local_of_nonsolvable_normalizer embedding hinjective W hne htwo
  intro hsolvable
  let : Group.IsSolvable (Subgroup.normalizer (W : Set G)) := hsolvable
  obtain ⟨projection, hsurjective, _⟩ := hmodel
  exact not_isSolvable_psl3_two (Group.isSolvable_of_surjective hsurjective)

end Stellmacher.SectionEight
