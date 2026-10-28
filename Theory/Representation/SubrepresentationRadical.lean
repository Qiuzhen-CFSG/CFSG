module

public import Theory.Representation.SubrepresentationLattice

/-!
# Iterated radicals of restricted representations

The radical is the intersection of maximal subrepresentations. For a subspace
of a fixed ambient representation, take that radical using the restricted
action and map it back along the inclusion. Iterating this construction keeps
every term in the same ambient lattice and gives a decreasing series.

Source application: Aschbacher–Smith, G.5.3, printed pp.343–345.
-/

@[expose] public section

namespace Representation.ModuleRadical
variable {k H V : Type*} [Field k] [Group H] [AddCommGroup V] [Module k V]
  {ρ : Representation k H V}

/-- The radical is the intersection of all maximal invariant subspaces. -/
def radical (σ : Representation k H V) : Subrepresentation σ :=
  sInf {N : Subrepresentation σ | IsCoatom N}

/-- Take the radical with the restricted action, then embed it in the ambient module. -/
def within (S : Subrepresentation ρ) : Subrepresentation ρ where
  toSubmodule := (radical S.toRepresentation).toSubmodule.map S.toSubmodule.subtype
  apply_mem_toSubmodule g := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨S.toRepresentation g v, (radical S.toRepresentation).apply_mem_toSubmodule g hv, rfl⟩

theorem within_le (S : Subrepresentation ρ) : within S ≤ S := by
  rintro _ ⟨v, _, rfl⟩
  exact v.property

theorem mem_within (S : Subrepresentation ρ) (v : S.toSubmodule) :
    v.val ∈ within S ↔ v ∈ radical S.toRepresentation := by
  constructor
  · rintro ⟨w, hw, he⟩
    exact (Subtype.ext he : w = v) ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

/-- Iterate actual radicals of the successively restricted representations. -/
def series (S : Subrepresentation ρ) : ℕ → Subrepresentation ρ
  | 0 => S
  | n + 1 => within (series S n)

@[simp] theorem series_zero (S : Subrepresentation ρ) : series S 0 = S := rfl

@[simp] theorem series_succ (S : Subrepresentation ρ) (n : ℕ) :
    series S (n + 1) = within (series S n) := rfl

theorem series_antitone (S : Subrepresentation ρ) : Antitone (series S) :=
  antitone_nat_of_succ_le (fun n => within_le (series S n))

end Representation.ModuleRadical
