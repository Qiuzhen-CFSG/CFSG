module

public import CFSG.Quasithin.Chapter16.Section04To05.Basic

/-!
# Conjugacy and transport for relative Sylow subgroups

A two-subgroup of H can be placed in any chosen Sylow two-subgroup of H
by conjugation within H. An ambient automorphism transports the chosen
relative Sylow subgroup and its overgroup together.

These common interfaces are used by both the inner-family selection and
intersection-structure arguments. Keeping one declaration of each avoids
incompatible duplicate exports when the two developments are imported together.

Source: the Sylow conjugacy theorem, applied in Aschbacher–Smith's
Notation 16.4.1 and Lemma 16.4.9, printed pp.1183 and 1189.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Transport a relative Sylow subgroup through an ambient automorphism. -/
theorem SylowIn.map {R H : Subgroup G} (hR : SylowIn R H) (e : G ≃* G) :
    SylowIn (R.map e.toMonoidHom) (H.map e.toMonoidHom) := by
  obtain ⟨S, rfl⟩ := hR
  let f := H.equivMapOfInjective e.toMonoidHom e.injective
  have hf : Function.Surjective f.toMonoidHom := f.surjective
  refine ⟨S.mapSurjective hf, ?_⟩
  rw [Sylow.coe_mapSurjective, map_map, map_map]
  rfl

/-- Conjugate a two-subgroup into a specified relative Sylow subgroup. -/
theorem SylowIn.exists_conjugate_le {R Q H : Subgroup G} (hR : SylowIn R H)
    (hQ : IsPGroup 2 Q) (hQH : Q ≤ H) : ∃ x ∈ H, Q.conjBy x ≤ R := by
  obtain ⟨S, rfl⟩ := hR
  obtain ⟨U, hU⟩ := (hQ.of_equiv (subgroupOfEquivOfLe hQH).symm).exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq H U S
  refine ⟨a, a.property, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨a * ⟨y, hQH hy⟩ * a⁻¹, ?_, rfl⟩
  rw [← ha]
  exact mem_map_of_mem (MulAut.conj a).toMonoidHom (hU hy)

end CFSG.Quasithin.Chapter16.Intersections
