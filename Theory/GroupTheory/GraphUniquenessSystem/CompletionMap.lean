module

public import Theory.GroupTheory.GraphUniquenessSystem.LocalComparison
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Maps extending the local comparisons

For a similarity from a source system to a target system, an extension is a
homomorphism from the target group to the source group restricting to the
inverse local isomorphisms. Such a map is automatically surjective by (U).
If the target is simple, it is an isomorphism, since a uniqueness system has
nontrivial local edge reversals.

This isolates the elementary final step in Aschbacher, *Sporadic Groups*,
Exercise 13.1(b). The substantive universal-completion step must construct the
extension from equivalence and the target base condition. No source base
condition is needed for the results here.
-/

@[expose] public section

namespace Theory.GroupTheory.GraphUniquenessSystem

universe u v u' v'
variable {G : Type u} {V : Type v} [Group G] [MulAction G V]
variable {G' : Type u'} {V' : Type v'} [Group G'] [MulAction G' V']

namespace System

/-- A uniqueness system has a nontrivial acting group. -/
theorem nontrivial (U : System G V) : Nontrivial G := by
  obtain ⟨t, ht, _⟩ := U.exists_swap
  refine ⟨⟨(t : G), 1, ?_⟩⟩
  intro h
  rw [h, one_smul] at ht
  exact U.adjacent.ne ht

/-- The vertex and local groups determine a homomorphism out of the acting group. -/
theorem hom_ext (U : System G V) {K : Type*} [Group K] (f g : G →* K)
    (hH : ∀ a : U.H, f a = g a) (hx : ∀ a : U.vertexGroup, f a = g a) : f = g := by
  have hle : U.H ⊔ U.vertexGroup ≤ f.eqLocus g :=
    sup_le (fun a ha => hH ⟨a, ha⟩) (fun a ha => hx ⟨a, ha⟩)
  rw [U.generate] at hle
  ext a
  exact hle (Subgroup.mem_top a)

end System

namespace Similarity
variable {U : System G V} {U' : System G' V'} (s : Similarity U U')

/-- A global homomorphism extending the inverses of the local comparisons. -/
structure Extension where
  hom : G' →* G
  onVertex : ∀ a : U.vertexGroup, hom (s.vertexIso a) = a
  onLocal : ∀ a : U.H, hom (s.localIso a) = a

namespace Extension
variable {s} (f : s.Extension)

/-- Local isomorphisms and (U) make every extension surjective. -/
theorem surjective : Function.Surjective f.hom := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← U.generate]
  exact sup_le
    (fun a ha => ⟨s.localIso ⟨a, ha⟩, f.onLocal ⟨a, ha⟩⟩)
    (fun a ha => ⟨s.vertexIso ⟨a, ha⟩, f.onVertex ⟨a, ha⟩⟩)

/-- An extension is uniquely determined by its local restrictions. -/
theorem hom_unique (g : s.Extension) : f.hom = g.hom := by
  apply U'.hom_ext
  · intro a
    obtain ⟨b, rfl⟩ := s.localIso.surjective a
    exact (f.onLocal b).trans (g.onLocal b).symm
  · intro a
    obtain ⟨b, rfl⟩ := s.vertexIso.surjective a
    exact (f.onVertex b).trans (g.onVertex b).symm

/-- A simple target has no nontrivial kernel in an extension. -/
theorem injective [IsSimpleGroup G'] : Function.Injective f.hom := by
  rcases (inferInstance : f.hom.ker.Normal).eq_bot_or_eq_top with h | h
  · exact (MonoidHom.ker_eq_bot_iff f.hom).mp h
  · have hf : f.hom = 1 := MonoidHom.ker_eq_top_iff.mp h
    obtain ⟨t, ht, _⟩ := U.exists_swap
    have ht1 : (t : G) = 1 := by simpa [hf] using (f.onLocal t).symm
    rw [ht1, one_smul] at ht
    exact False.elim (U.adjacent.ne ht)

/-- The isomorphism obtained once the universal-completion map is constructed. -/
noncomputable def mulEquiv [IsSimpleGroup G'] : G' ≃* G :=
  MulEquiv.ofBijective f.hom ⟨f.injective, f.surjective⟩

end Extension
end Similarity

end Theory.GroupTheory.GraphUniquenessSystem
