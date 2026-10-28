module
public import Theory.SpecificGroups.SymmetricSevenSylowNormalizer
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupTheory.SymmetricThreeTwoCore

/-!
# Self-normalizing Sylow subgroups in the two symmetric source models

The known S₃ result applies after identifying its trivial two-core.
The sixteen-word S₇ calculation supplies the second model. Multiplicative
isomorphisms transport both conclusions to the actual supplied finite group.
Source: Aschbacher–Smith C.5.12, printed p.163, final paragraph.
-/
public section
open Subgroup
namespace SymmetricThreeSeven
private theorem three (P : Sylow 2 (Equiv.Perm (Fin 3))) :
    normalizer (P : Set (Equiv.Perm (Fin 3))) = (P : Subgroup (Equiv.Perm (Fin 3))) := by
  have hc : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
    have hh := ker_eq_twoCore_of_surjective_perm_three (MonoidHom.id (Equiv.Perm (Fin 3)))
      Function.surjective_id (by
        simp only [MonoidHom.ker_id]
        exact IsPGroup.of_subsingleton 2 _)
    simpa only [MonoidHom.ker_id] using hh.symm
  let e := (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  exact SymmetricThreeTwoCore.sylow_self_normalizing e P
private theorem transport {H D : Type*} [Group H] [Group D] [Finite H] [Finite D]
    (e : H ≃* D) (P : Sylow 2 H)
    (h : ∀ Q : Sylow 2 D, normalizer (Q : Set D) = (Q : Subgroup D)) :
    normalizer (P : Set H) = (P : Subgroup H) := by
  apply map_injective (f := e.toMonoidHom) e.injective
  change (normalizer ((P : Subgroup H) : Set H)).map e.toMonoidHom =
    (P : Subgroup H).map e.toMonoidHom
  rw [map_equiv_normalizer_eq]
  exact h (P.mapSurjective e.surjective)
/-- An actual S₃ or S₇ isomorphism makes every supplied Sylow two-subgroup
self-normalizing. -/
theorem sylow_normalizer_eq_self {H : Type*} [Group H] [Finite H]
    (P : Sylow 2 H)
    (hmodel : Nonempty (H ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (H ≃* Equiv.Perm (Fin 7))) :
    normalizer (P : Set H) = (P : Subgroup H) := by
  rcases hmodel with hm | hm
  · obtain ⟨e⟩ := hm
    exact transport e P three
  · obtain ⟨e⟩ := hm
    exact transport e P SymmetricSevenSylow.sylow_normalizer_eq_self
end SymmetricThreeSeven
