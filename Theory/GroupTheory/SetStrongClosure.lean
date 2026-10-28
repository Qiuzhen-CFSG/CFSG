module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Conj

/-!
# Strong closure of a set under group fusion

The strong closure of `S` in `T` with respect to `H` consists of the
`H`-conjugates of elements of `S` which lie in `T`. It is a set, with no
closure under multiplication imposed. The universal property below identifies
it as the least strongly closed subset containing `S`, when `S ⊆ T`.

Conjugation is written on the right, `x^g = g⁻¹ * x * g`.
This is the convention used in Aschbacher–Smith, *The Classification of
Quasithin Groups*, Lemma 16.2.10, printed pp.1175–1176.
-/

@[expose] public section
namespace Theory.GroupTheory

variable {G : Type*} [Group G]

/-- Strong closure for a set, with the fusion overgroup explicit. -/
def IsStronglyClosedSet (S : Set G) (T H : Subgroup G) : Prop :=
  S ⊆ T ∧ ∀ x ∈ S, ∀ g ∈ H, g⁻¹ * x * g ∈ T → g⁻¹ * x * g ∈ S

/-- The set of conjugates which return to the specified subgroup. -/
def setStrongClosure (S : Set G) (T H : Subgroup G) : Set G :=
  {y | y ∈ T ∧ ∃ x ∈ S, ∃ g ∈ H, g⁻¹ * x * g = y}

theorem setStrongClosure_subset (S : Set G) (T H : Subgroup G) :
    setStrongClosure S T H ⊆ T := fun _ hy => hy.1

theorem subset_setStrongClosure {S : Set G} {T H : Subgroup G} (hST : S ⊆ T) :
    S ⊆ setStrongClosure S T H := by
  intro x hx
  exact ⟨hST hx, x, hx, 1, H.one_mem, by simp⟩

theorem setStrongClosure_mono {S R : Set G} {T H : Subgroup G} (hSR : S ⊆ R) :
    setStrongClosure S T H ⊆ setStrongClosure R T H := by
  rintro y ⟨hy, x, hx, g, hg, rfl⟩
  exact ⟨hy, x, hSR hx, g, hg, rfl⟩

theorem setStrongClosure_isStronglyClosed (S : Set G) (T H : Subgroup G) :
    IsStronglyClosedSet (setStrongClosure S T H) T H := by
  refine ⟨setStrongClosure_subset S T H, ?_⟩
  rintro y ⟨_, x, hx, g, hg, rfl⟩ k hk hyk
  exact ⟨hyk, x, hx, g * k, H.mul_mem hg hk, by simp [mul_assoc]⟩

theorem IsStronglyClosedSet.setStrongClosure_subset {R S : Set G} {T H : Subgroup G}
    (hR : IsStronglyClosedSet R T H) (hSR : S ⊆ R) :
    setStrongClosure S T H ⊆ R := by
  rintro y ⟨hy, x, hx, g, hg, rfl⟩
  exact hR.2 x (hSR hx) g hg hy

theorem setStrongClosure_eq_iff {S : Set G} {T H : Subgroup G} (hST : S ⊆ T) :
    setStrongClosure S T H = S ↔ IsStronglyClosedSet S T H := by
  constructor
  · intro he
    rw [← he]
    exact setStrongClosure_isStronglyClosed S T H
  · intro hs
    exact Set.Subset.antisymm (hs.setStrongClosure_subset Set.Subset.rfl)
      (subset_setStrongClosure hST)

/-- A set already contained in the closure is a proper subset exactly when
it fails strong closure. This applies, in particular, to a union of subgroups. -/
theorem ssubset_setStrongClosure_iff {R S : Set G} {T H : Subgroup G}
    (hSR : S ⊆ R) (hR : R ⊆ setStrongClosure S T H) :
    R ⊂ setStrongClosure S T H ↔ ¬ IsStronglyClosedSet R T H := by
  constructor
  · intro hlt hclosed
    exact hlt.2 (hclosed.setStrongClosure_subset hSR)
  · intro hn
    refine ⟨hR, ?_⟩
    intro hc
    have he : R = setStrongClosure S T H := Set.Subset.antisymm hR hc
    exact hn (he.symm ▸ setStrongClosure_isStronglyClosed S T H)

end Theory.GroupTheory
end
