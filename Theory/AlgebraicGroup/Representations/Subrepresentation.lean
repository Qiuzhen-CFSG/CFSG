module

public import Mathlib.RepresentationTheory.Irreducible

universe u v w

namespace Theory.AlgebraicGroup.Subrepresentation

variable {k : Type u} {Γ : Type v} {V : Type w}
  [Field k] [Group Γ] [AddCommGroup V] [Module k V]
variable {ρ : Representation k Γ V}

/-- Restricting a representation to an atom in its subrepresentation lattice
gives an irreducible representation. -/
public lemma isIrreducible_toRepresentation_of_isAtom
    (s : Subrepresentation ρ) (hs : IsAtom s) :
    s.toRepresentation.IsIrreducible := by
  change IsSimpleOrder (Subrepresentation s.toRepresentation)
  rw [isSimpleOrder_iff]
  have hsSub : s.toSubmodule ≠ ⊥ := by
    intro h
    apply hs.1
    apply Subrepresentation.ext
    exact h
  let : Nontrivial s.toSubmodule :=
    Submodule.nontrivial_iff_ne_bot.mpr hsSub
  let : Nontrivial (Subrepresentation s.toRepresentation) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro hbot
    obtain ⟨x, hx⟩ := exists_ne (0 : s.toSubmodule)
    have hxbot : x ∈ (⊥ : Subrepresentation s.toRepresentation) := by
      rw [hbot]
      trivial
    change (x : s.toSubmodule) ∈ (⊥ : Submodule k s.toSubmodule) at hxbot
    exact hx (by simpa using hxbot)
  constructor
  · infer_instance
  · intro t
    let lift : Subrepresentation ρ :=
      { toSubmodule := t.toSubmodule.map s.toSubmodule.subtype
        apply_mem_toSubmodule := by
          intro g x hx
          rcases hx with ⟨y, hy, rfl⟩
          refine ⟨s.toRepresentation g y, t.apply_mem_toSubmodule g hy, ?_⟩
          rfl }
    have hlift_le : lift ≤ s := by
      intro x hx
      rcases hx with ⟨y, _, rfl⟩
      exact y.property
    by_cases hlift : lift = s
    · right
      ext x
      constructor
      · intro _
        trivial
      · intro _
        have hx : (x : V) ∈ lift := by
          rw [hlift]
          exact x.property
        rcases hx with ⟨y, hy, hxy⟩
        have : y = x := by
          apply Subtype.ext
          exact hxy
        simpa [this] using hy
    · left
      have hliftbot : lift = ⊥ :=
        hs.2 lift (lt_of_le_of_ne hlift_le hlift)
      ext x
      constructor
      · intro hx
        have hx' : (x : V) ∈ lift := ⟨x, hx, rfl⟩
        rw [hliftbot] at hx'
        change (x : V) ∈ (⊥ : Submodule k V) at hx'
        change x = 0
        apply Subtype.ext
        simpa using hx'
      · intro hx
        change x = 0 at hx
        subst x
        exact t.toSubmodule.zero_mem

end Theory.AlgebraicGroup.Subrepresentation
