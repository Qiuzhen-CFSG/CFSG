module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Interface
public import Theory.Mathieu.M24.LocalGeometry.Defs
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore

/-!
# Pulling M24 geometry back to the component

The quotient map here is the supplied isomorphism after the projection by
the actual O₂(L). A geometric local subgroup is pulled back to L, embedded
in G, and joined with the supplied Sylow subgroup. Generation on the model
then gives generation of L by these overgroups. No normalization of L by S
is assumed: S may permute components of H.

The remaining calculations are separated into a geometric pair (including
the local two-core conditions) and the obstruction for its subnormal blocks.
The final theorem below is conditional on both calculations, and does not
assert the M24 exclusion.

Source: Aschbacher–Smith, 2.3.9(7), printed p.526; GLS, volume 3,
Table 5.3e, for the candidate octad and sextet geometries.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.M24Exclusion

open Subgroup Theory.GroupTheory Sporadic.Mathieu
open M24LocalGeometry

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The given quotient identification, retaining precisely O₂(L) as kernel. -/
noncomputable def quotientMap (d : SporadicQuotientInput L z .m24) : L →* M24 :=
  d.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

theorem quotientMap_surjective (d : SporadicQuotientInput L z .m24) :
    Function.Surjective (quotientMap d) :=
  d.quotientIso.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))

theorem quotientMap_ker (d : SporadicQuotientInput L z .m24) :
    (quotientMap d).ker = pCore 2 L := by
  ext x
  change d.quotientIso (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
  rw [map_eq_one_iff d.quotientIso d.quotientIso.injective]
  exact QuotientGroup.eq_one_iff x

/-- The subgroup over P in the actual central cover, embedded in G. -/
noncomputable def lift (d : SporadicQuotientInput L z .m24)
    (P : Subgroup M24) : Subgroup G :=
  (P.comap (quotientMap d)).map L.subtype

/-- The local overgroup generated with the supplied subgroup S. -/
noncomputable def localOvergroup (d : SporadicQuotientInput L z .m24)
    (A : Subgroup G) (P : Subgroup M24) : Subgroup G :=
  lift d P ⊔ A

theorem lift_le (d : SporadicQuotientInput L z .m24) (P : Subgroup M24) :
    lift d P ≤ L := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem lift_top (d : SporadicQuotientInput L z .m24) : lift d ⊤ = L := by
  ext x
  constructor
  · exact fun hx => lift_le d ⊤ hx
  · intro hx
    exact ⟨⟨x, hx⟩, mem_top _, rfl⟩

theorem lift_sup (d : SporadicQuotientInput L z .m24) (P Q : Subgroup M24) :
    lift d (P ⊔ Q) = lift d P ⊔ lift d Q := by
  unfold lift
  rw [← comap_sup_eq (quotientMap d) P Q (quotientMap_surjective d), Subgroup.map_sup]

theorem localOvergroup_within (d : SporadicQuotientInput L z .m24)
    (A : Subgroup G) (P : Subgroup M24) : localOvergroup d A P ≤ L ⊔ A :=
  sup_le_sup (lift_le d P) le_rfl

theorem le_localOvergroup (d : SporadicQuotientInput L z .m24)
    (A : Subgroup G) (P : Subgroup M24) : A ≤ localOvergroup d A P := le_sup_right

/-- Generation survives the actual central cover, without discarding its kernel. -/
theorem generated_of_model_pair (d : SporadicQuotientInput L z .m24)
    (A : Subgroup G) {P Q : Subgroup M24} (hgen : P ⊔ Q = ⊤) :
    L ≤ localOvergroup d A P ⊔ localOvergroup d A Q := by
  have he : lift d P ⊔ lift d Q = L := by rw [← lift_sup, hgen, lift_top]
  exact he.ge.trans (sup_le_sup le_sup_left le_sup_left)

/-- The full two-kernel belongs to the given Sylow subgroup, not just to
some Sylow subgroup chosen on the model. -/
theorem core_le_sylow (h : LocalSetup H L M S z) :
    (pCore 2 L).map L.subtype ≤ (S : Subgroup H).map H.subtype := by
  obtain ⟨R, hR⟩ := h.exists_component_sylow
  have hc := map_mono (f := L.subtype) (pCore_isPGroup.le_sylow_of_normal R)
  rw [hR] at hc
  exact hc.trans inf_le_right

/-- Centrality follows from intrinsic quasisimplicity, rather than being
an extra assumption on the cover. -/
theorem core_le_center (h : LocalSetup H L M S z) : pCore 2 L ≤ center L := by
  let := h.finite
  let := h.quasisimple
  exact IsQuasisimple.pCore_le_center 2

theorem core_le_centralizer (h : LocalSetup H L M S z) :
    (pCore 2 L).map L.subtype ≤ centralizer ({z} : Set G) := by
  intro x hx
  exact mem_centralizer_singleton_iff.mpr (h.central x (core_le_sylow h hx))

/-- The model Sylow subgroup comes from the supplied component restriction,
and the actual involution action fixes that restriction pointwise. -/
theorem exists_model_sylow (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .m24) :
    ∃ R : Sylow 2 L, ∃ T : Sylow 2 M24,
      (R : Subgroup L).map L.subtype = L ⊓ (S : Subgroup H).map H.subtype ∧
      (R : Subgroup L).map (quotientMap d) = (T : Subgroup M24) ∧
      ∀ r ∈ (R : Subgroup L), d.action r = r := by
  let := h.finite
  obtain ⟨R, hR, hfix⟩ := h.exists_fixed_component_sylow d.action d.conjugation
  exact ⟨R, R.mapSurjective (quotientMap_surjective d), hR, rfl, hfix⟩

/-- Contract for the geometric calculation. Both subgroups are actual
octad/sextet stabilizers. The intersection identities ensure that adjoining
S does not enlarge the subgroup induced on the distinguished component.
No block-obstruction conclusion is assumed here. -/
structure GeometryPair (d : SporadicQuotientInput L z .m24) (A : Subgroup G) where
  left : Subgroup M24
  right : Subgroup M24
  left_geometry : IsGeometryLocal left
  right_geometry : IsGeometryLocal right
  generated : left ⊔ right = ⊤
  left_intersection : L ⊓ localOvergroup d A left = lift d left
  right_intersection : L ⊓ localOvergroup d A right = lift d right
  left_even : localOvergroup d A left ∈ Chapter1.HeOver G (A : Set G)
  right_even : localOvergroup d A right ∈ Chapter1.HeOver G (A : Set G)

/-- Conditional assembly for independently proved geometric and block
calculations. The caller must still construct the pair and discharge hobs. -/
theorem cover_of_geometry_pair (d : SporadicQuotientInput L z .m24)
    (A : Subgroup G) (pair : GeometryPair d A)
    (hobs : ∀ P : Subgroup M24, IsGeometryLocal P →
      L ⊓ localOvergroup d A P = lift d P →
      localOvergroup d A P ∈ Chapter1.HeOver G (A : Set G) →
      BlockObstruction M A (localOvergroup d A P)) :
    Nonempty (CentralizerBlockCover L M A z) := by
  let K := localOvergroup d A pair.left
  let J := localOvergroup d A pair.right
  refine ⟨{
    locals := {K, J}
    generated := (generated_of_model_pair d A pair.generated).trans ?_
    within := ?_
    even := ?_
    obstruction := ?_
  }⟩
  · apply le_sup_of_le_right
    exact sup_le (le_sSup (by simp [K])) (le_sSup (by simp [J]))
  · intro U hU
    rcases Set.mem_insert_iff.mp hU with rfl | hU
    · exact localOvergroup_within d A pair.left
    · rcases Set.mem_singleton_iff.mp hU with rfl
      exact localOvergroup_within d A pair.right
  · intro U hU
    rcases Set.mem_insert_iff.mp hU with rfl | hU
    · exact pair.left_even
    · rcases Set.mem_singleton_iff.mp hU with rfl
      exact pair.right_even
  · intro U hU
    rcases Set.mem_insert_iff.mp hU with rfl | hU
    · exact hobs pair.left pair.left_geometry pair.left_intersection pair.left_even
    · rcases Set.mem_singleton_iff.mp hU with rfl
      exact hobs pair.right pair.right_geometry pair.right_intersection pair.right_even

end CFSG.Quasithin.Chapter2.ComponentRefinement.M24Exclusion

end
