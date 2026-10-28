module

public import CFSG.Quasithin.ChapterG.Section03.Recognition.RootGeometry
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Data.Set.Finite.Powerset
public import Mathlib.Data.Set.Card

/-!
# Full-action configurations in G.3.1

A configuration is a set of nonzero points carrying the full linear group on
its span. We retain its actual ambient root groups and restriction map.
The finite maximality reduction below is conditional on constructing seeds
and enlarging proper configurations; it does not assert recognition.

Source: Aschbacher--Smith, G.3.1, printed pp.337--338.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section03
open BinaryLinear BinaryTransvectionGroups
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

structure LinearConfiguration (G : Subgroup (GL V)) (Δ Γ : Set V) : Prop where
  subset : Γ ⊆ Δ
  all_points : Γ = {v | v ∈ Submodule.span (ZMod 2) Γ ∧ v ≠ 0}
  surjective : Function.Surjective (spanAction G Γ)
  dimension_ge_two : 2 ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) Γ)

theorem LinearConfiguration.stable {G : Subgroup (GL V)} {Δ Γ : Set V}
    (c : LinearConfiguration G Δ Γ) :
    ∀ g ∈ generated G Γ, ∀ x ∈ Γ, g x ∈ Γ := by
  intro g hg x hx
  rw [c.all_points] at hx ⊢
  refine ⟨?_, fun hz => hx.2 (g.map_eq_zero_iff.mp hz)⟩
  exact (quotientFixer_le_parabolic _ (generated_le_quotientFixer G Γ hg) x).mpr hx.1

theorem Hypotheses.finite_centers {G : Subgroup (GL V)} [Finite G] {Δ : Set V}
    (h : Hypotheses G Δ) : Δ.Finite := by
  obtain ⟨x, rfl⟩ := h.orbit
  exact Finite.finite_mulAction_orbit x

theorem LinearConfiguration.finite {G : Subgroup (GL V)} [Finite G] {Δ Γ : Set V}
    (h : Hypotheses G Δ) (c : LinearConfiguration G Δ Γ) : Γ.Finite :=
  h.finite_centers.subset c.subset

theorem fullAction_of_seed_and_enlargement {G : Subgroup (GL V)} [Finite G]
    {Δ : Set V} (h : Hypotheses G Δ)
    (hseed : ∀ i : OrbitBlock G Δ, ∃ Γ : Set V,
      LinearConfiguration G Δ Γ ∧ Γ ⊆ i.val)
    (henlarge : ∀ (i : OrbitBlock G Δ) (Γ : Set V),
      LinearConfiguration G Δ Γ → Γ ⊆ i.val → Γ ≠ i.val →
      ∃ Γ' : Set V, LinearConfiguration G Δ Γ' ∧ Γ' ⊆ i.val ∧ Γ.ncard < Γ'.ncard) :
    FullAction G Δ := by
  refine ⟨?_, h.block_dimension_ge_two⟩
  intro i
  let S : Set (Set V) := {Γ | LinearConfiguration G Δ Γ ∧ Γ ⊆ i.val}
  have hS : S.Finite := (orbitBlock_finite i).finite_subsets.subset
    (fun _ hΓ => hΓ.2)
  obtain ⟨Γ, hΓ, hmax⟩ := Set.exists_max_image S Set.ncard hS (hseed i)
  have he : Γ = i.val := by
    by_contra hne
    obtain ⟨Γ', hc', hi', hlt⟩ := henlarge i Γ hΓ.1 hΓ.2 hne
    exact (not_lt_of_ge (hmax Γ' ⟨hc', hi'⟩)) hlt
  exact he ▸ hΓ.1.surjective

end CFSG.Quasithin.ChapterG.Section03
