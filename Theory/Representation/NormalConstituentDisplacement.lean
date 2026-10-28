module

public import Theory.Representation.ConjugateRep
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Displacement smaller than an irreducible constituent

If an actor centralizes a subgroup, its displacement space is a submodule
for that subgroup. A nonzero displacement space therefore cannot have smaller
dimension than every irreducible submodule. For a normal subgroup, an actor
whose displacement has dimension smaller than a simple submodule must preserve
that submodule: otherwise it and its translate are disjoint, making the
displacement map injective on it.

These are the first two reductions in Aschbacher–Smith 15.3.57(2), printed
p.1148 of the combined manuscript (1 March 2004). They do not require
semisimplicity or any classification theorem, and hold over any field.
-/

public section

open Subgroup
namespace Representation
variable {k H W : Type*} [Field k] [Group H] [AddCommGroup W] [Module k W]
  [FiniteDimensional k W] (ρ : Representation k H W)

/-- A nonzero displacement smaller than every simple submodule prevents
centralization of the acting subgroup. -/
theorem not_le_centralizer_of_small_displacement
    (K : Subgroup H) (v : H)
    (hsmall : ∀ J : Subrepresentation (ρ.comp K.subtype),
      J.toRepresentation.IsIrreducible →
        Module.finrank k (LinearMap.range (ρ v - LinearMap.id)) <
          Module.finrank k J.toSubmodule)
    (hpos : 0 < Module.finrank k (LinearMap.range (ρ v - LinearMap.id))) :
    ¬ K ≤ centralizer ({v} : Set H) := by
  intro hc
  let D : Subrepresentation (ρ.comp K.subtype) := {
    toSubmodule := LinearMap.range (ρ v - LinearMap.id)
    apply_mem_toSubmodule a w hw := by
      obtain ⟨x, rfl⟩ := hw
      refine ⟨ρ a x, ?_⟩
      change ρ v (ρ (a : H) x) - ρ a x = ρ a (ρ v x - x)
      have he : v * (a : H) = (a : H) * v := hc a.property v rfl
      have he' := congrArg (fun g => ρ g x) he
      simpa only [map_mul, Module.End.mul_apply, LinearMap.sub_apply,
        LinearMap.id_apply, map_sub] using congrArg (fun y => y - ρ a x) he'
  }
  have hn : D ≠ ⊥ := by
    intro he
    have hz : D.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule he
    have hd : Module.finrank k D.toSubmodule = 0 := by rw [hz]; simp
    exact (Nat.ne_of_gt hpos) hd
  obtain ⟨J, hJ, hJD⟩ := (eq_bot_or_exists_atom_le D).resolve_left hn
  exact (not_lt_of_ge (Submodule.finrank_mono
    (show J.toSubmodule ≤ D.toSubmodule from hJD)))
      (hsmall J ((Subrepresentation.irreducible_iff_isAtom J).mpr hJ))

/-- The group commutator with the actual cyclic actor is nontrivial. -/
theorem commutator_zpowers_ne_bot_of_small_displacement
    (K : Subgroup H) (v : H)
    (hsmall : ∀ J : Subrepresentation (ρ.comp K.subtype),
      J.toRepresentation.IsIrreducible →
        Module.finrank k (LinearMap.range (ρ v - LinearMap.id)) <
          Module.finrank k J.toSubmodule)
    (hpos : 0 < Module.finrank k (LinearMap.range (ρ v - LinearMap.id))) :
    ⁅K, zpowers v⁆ ≠ ⊥ := by
  intro hbot
  apply not_le_centralizer_of_small_displacement ρ K v hsmall hpos
  exact (commutator_eq_bot_iff_le_centralizer.mp hbot).trans
    (centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers v)))

/-- A simple submodule of a normal subgroup is invariant under any actor
whose displacement has smaller dimension. -/
theorem map_constituent_eq_self_of_displacement_lt
    (K : Subgroup H) [K.Normal] (v : H)
    (J : Subrepresentation (ρ.comp K.subtype))
    (hJ : J.toRepresentation.IsIrreducible)
    (hdim : Module.finrank k (LinearMap.range (ρ v - LinearMap.id)) <
      Module.finrank k J.toSubmodule) :
    J.toSubmodule.map (ρ v) = J.toSubmodule := by
  let Jv := conjugateSubrepresentationOrderIso ρ K v J
  have ha : IsAtom J := (Subrepresentation.irreducible_iff_isAtom J).mp hJ
  have hav : IsAtom Jv := ((conjugateSubrepresentationOrderIso ρ K v).isAtom_iff J).mpr ha
  suffices he : Jv = J by
    simpa only [Jv, conjugateSubrepresentationOrderIso_toSubmodule] using
      congrArg Subrepresentation.toSubmodule he
  by_contra hne
  have hdis : Disjoint Jv.toSubmodule J.toSubmodule := by
    rw [disjoint_iff]
    exact congrArg Subrepresentation.toSubmodule (hav.disjoint_of_ne ha hne).eq_bot
  let f : J.toSubmodule →ₗ[k] LinearMap.range (ρ v - LinearMap.id) :=
    ((ρ v - LinearMap.id).comp J.toSubmodule.subtype).codRestrict _
      (fun x => ⟨x.val, rfl⟩)
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro x hx
    have he : ρ v x.val = x.val := by
      have he := congrArg Subtype.val hx
      change ρ v x.val - x.val = 0 at he
      exact sub_eq_zero.mp he
    have hv : x.val ∈ Jv.toSubmodule := by
      rw [show Jv.toSubmodule = J.toSubmodule.map (ρ v) from
        conjugateSubrepresentationOrderIso_toSubmodule ρ K v J]
      exact ⟨x.val, x.property, he⟩
    have hz := (Submodule.disjoint_def.mp hdis) x.val hv x.property
    exact Subtype.ext hz
  exact (not_le_of_gt hdim) (LinearMap.finrank_le_finrank_of_injective hf)

end Representation
