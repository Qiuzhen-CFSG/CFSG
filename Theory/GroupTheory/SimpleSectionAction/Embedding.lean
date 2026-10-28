module
public import Theory.GroupTheory.SimpleSectionAction

/-!
# Embedding a simple section in a larger ambient group

An inclusion of ambient groups preserves both section endpoints and their
quotient, provided the upper endpoint is still subnormal. If the acting
subgroup lies in the smaller ambient group, its stabilizer and induced
extension are unchanged. The comparison is proved on quotient representatives.

This is the ambient-inclusion step in Aschbacher--Smith, E.1.11, printed p.212.
-/

@[expose] public section
open Subgroup
namespace ChiefFactor.SimpleSection
universe u v
variable {G : Type u} [Group G] {L : Type v} [Group L]
variable {H : Subgroup G}

/-- Regard a section of an overgroup as an ambient section when its upper
endpoint is subnormal in the ambient group. -/
noncomputable def embed (s : SimpleSection H L)
    (hs : (s.subgroup.map H.subtype).IsSubnormal) : SimpleSection G L := by
  let := s.simple
  let e := s.subgroup.equivMapOfInjective H.subtype H.subtype_injective
  exact ChiefFactor.simpleSectionOfSurjective _ hs
    (s.projection.comp e.symm.toMonoidHom) (s.projection_surjective.comp e.symm.surjective)

theorem embed_projection (s : SimpleSection H L)
    (hs : (s.subgroup.map H.subtype).IsSubnormal) (x : s.subgroup) :
    (s.embed hs).projection (s.subgroup.equivMapOfInjective H.subtype H.subtype_injective x) =
      s.projection x := by
  let e := s.subgroup.equivMapOfInjective H.subtype H.subtype_injective
  change s.projection (e.symm (e x)) = s.projection x
  rw [MulEquiv.symm_apply_apply]

theorem embed_kernelImage (s : SimpleSection H L)
    (hs : (s.subgroup.map H.subtype).IsSubnormal) :
    (s.embed hs).kernelImage = s.kernelImage.map H.subtype := by
  let e := s.subgroup.equivMapOfInjective H.subtype H.subtype_injective
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hk : e.symm y ∈ s.kernel := (s.projection_eq_one _).mp hy
    refine ⟨(e.symm y : H), ⟨e.symm y, hk, rfl⟩, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply y)
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨e z, ?_, rfl⟩
    change s.projection (e.symm (e z)) = 1
    rw [e.symm_apply_apply]
    exact (s.projection_eq_one z).mpr hz

private theorem normalizer_map_subtype (K : Subgroup H) :
    (normalizer (K.map H.subtype)).comap H.subtype = normalizer K := by
  rw [comap_normalizer_eq_of_le_range (map_le_range _ _),
    comap_map_eq_self_of_injective H.subtype_injective]

theorem embed_stabilizer (s : SimpleSection H L)
    (hs : (s.subgroup.map H.subtype).IsSubnormal) (T : Subgroup G) :
    ((s.embed hs).stabilizer T).comap H.subtype = s.stabilizer (T.subgroupOf H) := by
  simp only [stabilizer, embed_kernelImage, comap_inf]
  change T.comap H.subtype ⊓
    ((normalizer (s.subgroup.map H.subtype)).comap H.subtype ⊓ _) = _
  rw [normalizer_map_subtype, normalizer_map_subtype]
  rfl

/-- The same element of T in either ambient group stabilizes precisely the
same two endpoints. -/
def embedStabilizerMap (s : SimpleSection H L)
    (hs : (s.subgroup.map H.subtype).IsSubnormal) (T : Subgroup G) (hT : T ≤ H) :
    (s.embed hs).stabilizer T →* s.stabilizer (T.subgroupOf H) where
  toFun g := ⟨⟨g, hT g.property.1⟩,
    (s.embed_stabilizer hs T).le g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem embedStabilizerMap_surjective (s : SimpleSection H L)
    (hs : (s.subgroup.map H.subtype).IsSubnormal) (T : Subgroup G) (hT : T ≤ H) :
    Function.Surjective (s.embedStabilizerMap hs T hT) := by
  intro g
  exact ⟨⟨g, (s.embed_stabilizer hs T).ge g.property⟩, rfl⟩

theorem embed_action (s : SimpleSection H L)
    (hs : (s.subgroup.map H.subtype).IsSubnormal) (T : Subgroup G) (hT : T ≤ H)
    (g : (s.embed hs).stabilizer T) :
    (s.embed hs).action T g =
      s.action (T.subgroupOf H) (s.embedStabilizerMap hs T hT g) := by
  let e := s.subgroup.equivMapOfInjective H.subtype H.subtype_injective
  ext z
  obtain ⟨x, rfl⟩ := s.projection_surjective z
  rw [s.action_projection]
  have he : (s.embed hs).upperAction T g (e x) =
      e (s.upperAction (T.subgroupOf H) (s.embedStabilizerMap hs T hT g) x) :=
    Subtype.ext rfl
  calc
    (s.embed hs).action T g (s.projection x) =
        (s.embed hs).action T g ((s.embed hs).projection (e x)) := by
      rw [s.embed_projection]
    _ = (s.embed hs).projection ((s.embed hs).upperAction T g (e x)) :=
      (s.embed hs).action_projection T g (e x)
    _ = _ := by rw [he, s.embed_projection]

theorem embed_extension (s : SimpleSection H L)
    (hs : (s.subgroup.map H.subtype).IsSubnormal) (T : Subgroup G) (hT : T ≤ H) :
    (s.embed hs).extension T = s.extension (T.subgroupOf H) := by
  apply congrArg (fun K => MulAut.innerSubgroup L ⊔ K)
  ext a
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨s.embedStabilizerMap hs T hT g, (s.embed_action hs T hT g).symm⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨k, rfl⟩ := s.embedStabilizerMap_surjective hs T hT g
    exact ⟨k, s.embed_action hs T hT k⟩

end ChiefFactor.SimpleSection
