module

public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Centralizer rigidity and conjugate intersections

Let `M` be self-normalizing. Suppose centralizers of nonidentity elements of
`U` lie in `M`, and a conjugate of each local centralizer `C_M(u)` can lie in
`M` only when that conjugation fixes `M`. Then any conjugator carrying a
nonidentity element of `U` back into `U` belongs to `M`.

The proof conjugates `C_M(u)` into the centralizer of the image of `u`.
If `M` normalizes `U`, this also determines the full normalizer of `U`.
No finiteness or commutativity assumption is needed.

Source: the group-theoretic step in Aschbacher--Smith, *The Classification of
Quasithin Groups*, combined manuscript (1 March 2004), Lemma 13.1.13,
printed p. 875. The source establishes the centralizer and rigidity inputs
separately in 13.1.11--12; those results are not assumed to hold in general.
-/

namespace Subgroup
variable {G : Type*} [Group G] {U M : Subgroup G}

/-- A conjugator carrying a nonidentity element back into `U` lies in `M`. -/
public theorem conjugator_mem_of_centralizer_conjugate_rigidity
    (hself : normalizer (M : Set G) ≤ M)
    (hcentral : ∀ u ∈ U, u ≠ 1 → centralizer ({u} : Set G) ≤ M)
    (hrigid : ∀ u ∈ U, u ≠ 1 → ∀ g : G,
      (M ⊓ centralizer ({u} : Set G)).map (MulAut.conj g).toMonoidHom ≤ M →
      M.map (MulAut.conj g).toMonoidHom = M)
    {u g : G} (hu : u ∈ U) (hne : u ≠ 1)
    (hgu : MulAut.conj g u ∈ U) : g ∈ M := by
  have hgne : MulAut.conj g u ≠ 1 := by
    intro h
    apply hne
    exact (MulAut.conj g).injective (h.trans (map_one _).symm)
  have hC : (M ⊓ centralizer ({u} : Set G)).map (MulAut.conj g).toMonoidHom ≤ M := by
    apply le_trans (map_mono inf_le_right)
    apply le_trans (map_centralizer_le_centralizer_image _ _)
    simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom] using hcentral _ hgu hgne
  exact hself (mem_normalizer_iff_map_conj_eq.mpr (hrigid u hu hne g hC))

/-- Conjugates indexed outside `M` have trivial intersection with `U`. -/
public theorem inf_conjugate_eq_bot_of_centralizer_conjugate_rigidity
    (hself : normalizer (M : Set G) ≤ M)
    (hcentral : ∀ u ∈ U, u ≠ 1 → centralizer ({u} : Set G) ≤ M)
    (hrigid : ∀ u ∈ U, u ≠ 1 → ∀ g : G,
      (M ⊓ centralizer ({u} : Set G)).map (MulAut.conj g).toMonoidHom ≤ M →
      M.map (MulAut.conj g).toMonoidHom = M)
    {g : G} (hg : g ∉ M) : U ⊓ U.map (MulAut.conj g).toMonoidHom = ⊥ := by
  apply eq_bot_iff.mpr
  rintro x ⟨hx, u, hu, rfl⟩
  by_cases h : u = 1
  · simp [h]
  · exact (hg (conjugator_mem_of_centralizer_conjugate_rigidity hself hcentral hrigid hu h hx)).elim

/-- If `M` normalizes nontrivial `U`, it is the full normalizer. -/
public theorem normalizer_eq_of_centralizer_conjugate_rigidity
    (hself : normalizer (M : Set G) ≤ M)
    (hcentral : ∀ u ∈ U, u ≠ 1 → centralizer ({u} : Set G) ≤ M)
    (hrigid : ∀ u ∈ U, u ≠ 1 → ∀ g : G,
      (M ⊓ centralizer ({u} : Set G)).map (MulAut.conj g).toMonoidHom ≤ M →
      M.map (MulAut.conj g).toMonoidHom = M)
    (hU : U ≠ ⊥) (hMU : M ≤ normalizer (U : Set G)) : normalizer (U : Set G) = M := by
  apply le_antisymm _ hMU
  intro g hg
  have hex : ∃ u ∈ U, u ≠ (1 : G) := by
    by_contra! hn
    exact hU (eq_bot_iff.mpr (fun u hu => hn u hu))
  obtain ⟨u, hu, hne⟩ := hex
  apply conjugator_mem_of_centralizer_conjugate_rigidity hself hcentral hrigid hu hne
  have he := mem_normalizer_iff_map_conj_eq.mp hg
  rw [← he]
  exact mem_map.mpr ⟨u, hu, rfl⟩
end Subgroup
