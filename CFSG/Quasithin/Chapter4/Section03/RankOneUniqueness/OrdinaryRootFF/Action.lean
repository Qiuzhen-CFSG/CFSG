module

public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootGeometry
public import Theory.Representation.NormalElementaryQuotient
public import Theory.GroupTheory.PCoreImage

/-!
# The literal faithful action in the ordinary root argument

The actor is the actual root normalizer modulo the centralizer of its
normal closure U. The representation acts on U itself, with the original
conjugation formula. Reducedness makes the root two-core vanish in this
quotient. All subgroup images below use this one quotient projection.

Source: Aschbacher--Smith 4.3.6, printed p.615, following (*) and (**).
This construction does not assert the subsequent FF classification.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
variable {G : Type*} [Group G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} (m : OrdinarySymplecticMarking c n)

/-- U inside its original normalizer, with no change of ambient group. -/
abbrev moduleSubgroup : Subgroup m.rootNormalizer :=
  m.rootSpan.subgroupOf m.rootNormalizer

instance moduleSubgroup_normal : (moduleSubgroup m).Normal :=
  normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)

/-- The source group G_Z^*. -/
abbrev Actor := m.rootNormalizer ⧸ centralizer (moduleSubgroup m : Set m.rootNormalizer)

/-- The quotient projection used for every source subgroup. -/
def projection : m.rootNormalizer →* Actor m :=
  QuotientGroup.mk' (centralizer (moduleSubgroup m : Set m.rootNormalizer))

def image (A : Subgroup G) : Subgroup (Actor m) :=
  (A.subgroupOf m.rootNormalizer).map (projection m)

theorem image_mono {A B : Subgroup G} (hAB : A ≤ B) : image m A ≤ image m B :=
  map_mono (fun _ hx => hAB hx)

theorem projection_kernel (hUN : m.rootSpan ≤ m.rootNormalizer) :
    (projection m).ker = (centralizer (m.rootSpan : Set G)).subgroupOf m.rootNormalizer := by
  rw [projection, QuotientGroup.ker_mk']
  ext x
  constructor
  · intro hx u hu
    exact congrArg Subtype.val (hx ⟨u, hUN hu⟩ hu)
  · intro hx u hu
    exact Subtype.ext (hx u hu)

/-- Conjugation descended to the actual centralizer quotient. -/
def representation (hr : IsPReduced 2 (moduleSubgroup m)) :
    letI := hr.elementary
    Representation (ZMod 2) (Actor m) (Additive (moduleSubgroup m)) :=
  letI := hr.elementary
  Representation.NormalElementaryQuotient.representation (moduleSubgroup m)
    (projection m) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

theorem representation_injective (hr : IsPReduced 2 (moduleSubgroup m)) :
    letI := hr.elementary
    Function.Injective (representation m hr) := by
  let := hr.elementary
  exact Representation.NormalElementaryQuotient.representation_injective _ _ _ _

theorem representation_apply (hr : IsPReduced 2 (moduleSubgroup m)) :
    letI := hr.elementary
    ∀ (g : m.rootNormalizer) (u : Additive (moduleSubgroup m)),
      ((representation m hr (projection m g) u).toMul.val : G) =
        (g : G) * (u.toMul.val : G) * (g : G)⁻¹ := by
  let := hr.elementary
  intro g u
  exact congrArg Subtype.val
    (Representation.NormalElementaryQuotient.representation_apply _ _ _ _ g u)

/-- The source reducedness premise applies to precisely this actor. -/
theorem actor_pCore_eq_bot (hr : IsPReduced 2 (moduleSubgroup m)) :
    pCore 2 (Actor m) = ⊥ := hr.quotient_pCore_eq_bot

theorem core_le_kernel (hr : IsPReduced 2 (moduleSubgroup m)) :
    pCore 2 m.rootNormalizer ≤ (projection m).ker := by
  rw [projection, QuotientGroup.ker_mk']
  exact le_centralizer_iff.mp hr.le_centralizer_pCore

theorem core_image_eq_bot (hr : IsPReduced 2 (moduleSubgroup m)) :
    image m m.rootCore = ⊥ := by
  apply (Subgroup.map_eq_bot_iff _).mpr
  change ((pCore 2 m.rootNormalizer).map m.rootNormalizer.subtype).comap
    m.rootNormalizer.subtype ≤ _
  rw [comap_map_eq_self_of_injective m.rootNormalizer.subtype_injective]
  exact core_le_kernel m hr

theorem secondaryCore_le_rootCore {KZ : Subgroup G}
    (hKN : KZ ≤ m.rootNormalizer)
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G)) :
    KZ.pCoreIn 2 ≤ m.rootCore :=
  pCoreIn_mono_of_normalizes hKN hnormal

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
