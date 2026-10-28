module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The alternating group on the fixed points inside a centralizer

Extend even permutations of the fixed points of an even permutation by the
identity on its support. The image consists exactly of the centralizer elements
fixing that support pointwise. It is normal because every element of the
centralizer preserves the support, and it is isomorphic to the alternating group
on the fixed points.

This elementary support decomposition is used in Aschbacher, “A 2-local
characterization of M12”, Proposition 3.3, printed p.38.
-/

@[expose] public section

open Equiv Equiv.Perm Subgroup
namespace alternatingGroup.FixedPointCentralizer
variable {α : Type*} [Fintype α] [DecidableEq α] (t : alternatingGroup α)
abbrev C := centralizer ({t} : Set (alternatingGroup α))
/-- The points fixed by the chosen permutation. -/
abbrev points : Finset α := (t : Perm α).supportᶜ

/-- The even permutations of the fixed points, viewed inside the centralizer. -/
def fixed : Subgroup (C t) :=
  (alternatingGroup.ofSubtype (points t)).range.comap (C t).subtype

theorem mem_fixed (g : C t) :
    g ∈ fixed t ↔ ∀ x ∈ (t : Perm α).support, (g.val : Perm α) x = x := by
  change g.val ∈ (alternatingGroup.ofSubtype (points t)).range ↔ _
  rw [alternatingGroup.mem_range_ofSubtype_iff]
  constructor
  · intro h x hx
    apply notMem_support.mp
    intro hg
    exact (Finset.mem_compl.mp (h hg)) hx
  · intro h x hx
    exact Finset.mem_compl.mpr (fun ht => (mem_support.mp hx) (h x ht))

theorem preserves_support (g : C t) (x : α) :
    (g.val : Perm α) x ∈ (t : Perm α).support ↔ x ∈ (t : Perm α).support := by
  have hc := congrArg (fun a : alternatingGroup α => (a : Perm α) x)
    (mem_centralizer_singleton_iff.mp g.property)
  change (g.val : Perm α) ((t : Perm α) x) = (t : Perm α) ((g.val : Perm α) x) at hc
  simp only [mem_support, ← hc, (g.val : Perm α).injective.ne_iff]

instance fixed_normal : (fixed t).Normal where
  conj_mem n hn g := by
    rw [mem_fixed] at hn ⊢
    intro x hx
    change (g.val : Perm α) ((n.val : Perm α) ((g.val : Perm α)⁻¹ x)) = x
    have hxi : ((g.val : Perm α)⁻¹ x) ∈ (t : Perm α).support :=
      (preserves_support t g⁻¹ x).mpr hx
    rw [hn _ hxi]
    exact (g.val : Perm α).apply_symm_apply x

/-- Extend an even permutation of the fixed points by the identity. -/
def inclusion : alternatingGroup (points t) →* C t :=
  (alternatingGroup.ofSubtype (points t)).codRestrict (C t) (by
    intro a
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    apply Equiv.Perm.Disjoint.commute
    apply disjoint_iff_disjoint_support.mpr
    apply Finset.disjoint_left.mpr
    intro x hx ht
    have hs := (alternatingGroup.mem_range_ofSubtype_iff (points t)
      (alternatingGroup.ofSubtype (points t) a)).mp ⟨a, rfl⟩
    exact (Finset.mem_compl.mp (hs hx)) ht)

theorem inclusion_injective : Function.Injective (inclusion t) := by
  intro a b h
  exact alternatingGroup.ofSubtype_injective (congrArg Subtype.val h)

theorem range_inclusion : (inclusion t).range = fixed t := by
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

/-- The supported subgroup is the actual alternating group on the fixed points. -/
noncomputable def equiv : fixed t ≃* alternatingGroup (points t) :=
  (MulEquiv.subgroupCongr (range_inclusion t).symm).trans
    (MonoidHom.ofInjective (inclusion_injective t)).symm
end alternatingGroup.FixedPointCentralizer
end
