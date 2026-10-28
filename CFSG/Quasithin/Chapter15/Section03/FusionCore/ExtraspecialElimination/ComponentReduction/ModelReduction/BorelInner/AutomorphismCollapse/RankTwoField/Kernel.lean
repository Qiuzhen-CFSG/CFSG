module

public import Mathlib.GroupTheory.Sylow
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The local torus rigidity contract

An automorphism stabilizing a Sylow two-subgroup and acting trivially on
its normalizer modulo that subgroup is required to be inner. This is a
local model property, not a classification assumption on the source setup.
It transports through actual group isomorphisms.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, printed p.1144, the
automorphism calculation in the proof of 15.3.49(k).
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.RankTwoField

/-- The kernel of the action on a Sylow-normalizer quotient consists of inner actors. -/
def TorusRigid (D : Type*) [Group D] : Prop :=
  ∀ (P : Sylow 2 D) (a : MulAut D),
    (P : Subgroup D).map a.toMonoidHom = P →
    (∀ b ∈ normalizer (P : Set D), b⁻¹ * a b ∈ P) →
    a ∈ MulAut.innerSubgroup D

/-- The rigidity property is unchanged by an actual identification of carriers. -/
theorem TorusRigid.of_equiv {D E : Type*} [Group D] [Group E] [Finite D]
    (e : D ≃* E) (h : TorusRigid E) : TorusRigid D := by
  intro P a hP ha
  let Q : Sylow 2 E := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let b : MulAut E := MulAut.congr e a
  have hQ : (Q : Subgroup E).map b.toMonoidHom = Q := by
    change ((P : Subgroup D).map e.toMonoidHom).map b.toMonoidHom =
      (P : Subgroup D).map e.toMonoidHom
    rw [Subgroup.map_map]
    have he : b.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp a.toMonoidHom := by
      ext x
      simp [b, MulAut.congr_apply]
    rw [he, ← Subgroup.map_map, hP]
  have hb : ∀ x ∈ normalizer (Q : Set E), x⁻¹ * b x ∈ Q := by
    intro x hx
    have hN : normalizer (Q : Set E) =
        (normalizer (P : Set D)).map e.toMonoidHom := by
      exact (map_equiv_normalizer_eq (P : Subgroup D) e).symm
    obtain ⟨y, hy, rfl⟩ := hN.le hx
    have hm := mem_map_of_mem e.toMonoidHom (ha y hy)
    change e (y⁻¹ * a y) ∈ (P : Subgroup D).map e.toMonoidHom at hm
    change (e y)⁻¹ * e (a (e.symm (e y))) ∈ (P : Subgroup D).map e.toMonoidHom
    simpa only [e.symm_apply_apply, map_mul, map_inv] using hm
  obtain ⟨g, hg⟩ := h Q b hQ hb
  refine ⟨e.symm g, ?_⟩
  ext x
  apply e.injective
  have hx := MulEquiv.congr_fun hg (e x)
  change g * e x * g⁻¹ = e (a (e.symm (e x))) at hx
  simpa only [MulAut.conj_apply, map_mul, map_inv, e.apply_symm_apply,
    e.symm_apply_apply] using hx

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.RankTwoField
