module

public import Theory.Representation.FirstCohomologyDuality

/-!
# Indecomposability of central covers with simple head

In a commutator-generated module with fixed kernel, an invariant subspace
surjecting onto the quotient is the entire module: subtract a lift in the
subspace and use fixation of the resulting kernel vector. If the quotient
is simple, one summand of any invariant direct decomposition surjects,
so the other vanishes. No finite-dimensionality assumption is required.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 14.7.73(3), printed pp.1076–1077.
-/

public section

open Representation Representation.OneCohomology
namespace Representation.OneCohomology
variable {k D V W : Type*} [Field k] [Group D]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {ρ : Representation k D V} {σ : Representation k D W}

/-- An invariant subspace surjecting onto the head of a central cover is the whole source. -/
theorem invariant_eq_top_of_cover_image_eq_top
    (p : σ.IntertwiningMap ρ) (hp : IsCover p)
    (A : Submodule k W) (hA : ∀ g v, v ∈ A → σ g v ∈ A)
    (hmap : A.map p.toLinearMap = ⊤) : A = ⊤ := by
  apply top_unique
  rw [← hp.2.2]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g, v⟩, rfl⟩
  obtain ⟨a, ha, he⟩ := show p v ∈ A.map p.toLinearMap from hmap ▸ Submodule.mem_top
  change p a = p v at he
  have hk : v - a ∈ p.toLinearMap.ker := by
    change p (v - a) = 0
    rw [map_sub, he, sub_self]
  have hfix := hp.2.1 hk g
  have heq : σ g v - v = σ g a - a := by
    rw [map_sub] at hfix
    exact sub_eq_sub_iff_sub_eq_sub.mp hfix
  change σ g v - v ∈ A
  rw [heq]
  exact A.sub_mem (hA g a ha) ha

/-- A central cover of a simple module admits no nontrivial invariant direct decomposition. -/
theorem indecomposable_of_cover_of_simple
    (p : σ.IntertwiningMap ρ) (hp : IsCover p)
    (hsimple : ∀ X : Submodule k V,
      (∀ g v, v ∈ X → ρ g v ∈ X) → X = ⊥ ∨ X = ⊤)
    (A B : Submodule k W)
    (hA : ∀ g v, v ∈ A → σ g v ∈ A)
    (hB : ∀ g v, v ∈ B → σ g v ∈ B)
    (hAB : IsCompl A B) : A = ⊥ ∨ B = ⊥ := by
  have hAi : ∀ g v, v ∈ A.map p.toLinearMap → ρ g v ∈ A.map p.toLinearMap := by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨σ g v, hA g v hv, LinearMap.congr_fun (p.isIntertwining' g) v⟩
  rcases hsimple (A.map p.toLinearMap) hAi with ha | ha
  · have hb : B.map p.toLinearMap = ⊤ := by
      have hm : (A.map p.toLinearMap) ⊔ (B.map p.toLinearMap) = ⊤ := by
        rw [← Submodule.map_sup, hAB.sup_eq_top, Submodule.map_top,
          LinearMap.range_eq_top.mpr hp.1]
      simpa only [ha, bot_sup_eq] using hm
    have hBtop := invariant_eq_top_of_cover_image_eq_top p hp B hB hb
    exact Or.inl (by simpa only [hBtop, inf_top_eq] using hAB.inf_eq_bot)
  · have hAtop := invariant_eq_top_of_cover_image_eq_top p hp A hA ha
    exact Or.inr (by simpa only [hAtop, top_inf_eq] using hAB.inf_eq_bot)

end Representation.OneCohomology

