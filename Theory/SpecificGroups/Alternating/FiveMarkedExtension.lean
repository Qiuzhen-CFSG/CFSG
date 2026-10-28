module
public import Theory.SpecificGroups.Alternating.FiveExtensionAction
/-!
# Retaining actors in the five-point extension isomorphism

A subgroup outside a self-centralizing normal A₅ contains an element inducing
an outer automorphism. The conjugation action identifies the whole group
with S₅. Its restriction to the given A₅ is the prescribed equivalence, so
the original actor maps outside the actual alternating subgroup.

Source: Aut(A₅) = S₅; Aschbacher--Smith E.1.14(7), p.214.
-/
public section
open Subgroup
namespace Theory.SpecificGroups.Alternating.FiveMarkedExtension
variable {H : Type*} [Group H]

/-- An actor outside a self-centralizing normal A₅ identifies the whole group
with S₅ and remains outside the actual alternating subgroup. -/
theorem exists_marked_equiv (D : Subgroup H) [D.Normal]
    (eD : D ≃* alternatingGroup (Fin 5))
    (hC : centralizer (D : Set H) = ⊥)
    (A : Subgroup H) (hA : ¬ A ≤ D) :
    ∃ e : H ≃* Equiv.Perm (Fin 5),
      D.map e.toMonoidHom = alternatingGroup (Fin 5) ∧
      ¬ A.map e.toMonoidHom ≤ alternatingGroup (Fin 5) := by
  classical
  obtain ⟨t, htA, htD⟩ : ∃ t ∈ A, t ∉ D := Set.not_subset.mp hA
  have ht : (MulAut.conjNormal t : MulAut D) ∉ MulAut.innerSubgroup D := by
    intro hh
    have hh' : t ∈ (MulAut.innerSubgroup D).comap MulAut.conjNormal := hh
    rw [MulAut.conjNormal_comap_innerSubgroup, hC, sup_bot_eq] at hh'
    exact htD hh'
  obtain ⟨e, he⟩ := Theory.SpecificGroups.Alternating.FiveExtensionAction.exists_equiv D eD hC t ht
  have hm : D.map e.toMonoidHom = alternatingGroup (Fin 5) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change e x ∈ alternatingGroup (Fin 5)
      rw [he ⟨x, hx⟩]
      exact (eD ⟨x, hx⟩).property
    · intro hy
      obtain ⟨x, hx⟩ := eD.surjective ⟨y, hy⟩
      exact ⟨x, x.property, (he x).trans (congrArg Subtype.val hx)⟩
  refine ⟨e, hm, ?_⟩
  intro hle
  apply hA
  rw [← hm] at hle
  exact (map_le_map_iff_of_injective e.injective).mp hle

end Theory.SpecificGroups.Alternating.FiveMarkedExtension
