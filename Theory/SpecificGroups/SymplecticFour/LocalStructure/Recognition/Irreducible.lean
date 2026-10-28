module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Basic
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Action

/-!
# Binary irreducibility of the extension module

Transitivity on nonzero vectors leaves no proper nonzero invariant additive
subgroup. Pulling this fact back through the actual quotient isomorphism
gives the normal-subgroup interval required by Aschbacher–Smith C.1.7.
No closure under scalars in the larger defining field is assumed.
-/

@[expose] public section

namespace Theory.SpecificGroups.SymplecticFour.NaturalExtension
variable {F L : Type*} [Field F] [Group L]
variable {Q : Subgroup L} [Q.Normal] (d : NaturalExtension (F := F) Q)

/-- Coordinates of an element of the elementary abelian kernel. -/
def coordinates : Q →* Multiplicative (Fin 2 → F) :=
  d.moduleIso.toMonoidHom.comp (QuotientGroup.mk' ((Subgroup.center L).subgroupOf Q))

@[simp] theorem coordinates_eq_one (u : Q) :
    d.coordinates u = 1 ↔ (u : L) ∈ Subgroup.center L := by
  change d.moduleIso (QuotientGroup.mk' _ u) = 1 ↔ _
  rw [← d.moduleIso.map_one, d.moduleIso.injective.eq_iff]
  exact QuotientGroup.eq_one_iff u

include d
/-- The quotient module is nonzero. -/
theorem central_lt : Q ⊓ Subgroup.center L < Q := by
  have hn : Nontrivial (Q ⧸ (Subgroup.center L).subgroupOf Q) :=
    d.moduleIso.symm.injective.nontrivial
  have hne := QuotientGroup.nontrivial_iff.mp hn
  refine lt_of_le_of_ne inf_le_left ?_
  intro he
  apply hne
  apply Subgroup.subgroupOf_eq_top.mpr
  exact he.ge.trans inf_le_right

/-- Normal subgroups between the fixed points and the kernel are trivial or full.
This is irreducibility for additive subgroups, hence over the binary field. -/
theorem invariant_interval (N : Subgroup L) [N.Normal]
    (hlo : Q ⊓ Subgroup.center L ≤ N) (hhi : N ≤ Q) :
    N = Q ⊓ Subgroup.center L ∨ N = Q := by
  classical
  by_cases hc : N ≤ Subgroup.center L
  · exact Or.inl (le_antisymm (le_inf hhi hc) hlo)
  · right
    obtain ⟨x, hx, hxc⟩ := SetLike.not_le_iff_exists.mp hc
    let u : Q := ⟨x, hhi hx⟩
    have hu : Multiplicative.toAdd (d.coordinates u) ≠ 0 := by
      intro h
      apply hxc
      exact (d.coordinates_eq_one u).mp h
    let K := N.subgroupOf Q
    have hmap : K.map d.coordinates = ⊤ := by
      apply top_unique
      intro v _
      by_cases hv : v = 1
      · subst v
        exact (K.map d.coordinates).one_mem
      have hv0 : Multiplicative.toAdd v ≠ 0 := hv
      obtain ⟨g, hg⟩ := natural_transitive hu hv0
      obtain ⟨l, rfl⟩ := d.surjective g
      refine ⟨extensionConjugate Q l u, ?_, ?_⟩
      · exact (inferInstance : N.Normal).conj_mem x hx l
      · apply Multiplicative.toAdd.injective
        exact (d.intertwining l u).trans hg
    have hker : d.coordinates.ker ≤ K := by
      intro u hu
      exact hlo ⟨u.property, (d.coordinates_eq_one u).mp hu⟩
    have he := Subgroup.comap_map_eq_self hker
    rw [hmap, Subgroup.comap_top] at he
    exact le_antisymm hhi (Subgroup.subgroupOf_eq_top.mp he.symm)
end Theory.SpecificGroups.SymplecticFour.NaturalExtension
