module
public import Theory.GroupTheory.CrossingFusionCentralizer
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Translating a crossing while keeping the chosen element

If the H-orbit of u meets its g-conjugate, conjugating the second module by
an element of H arranges that this intersection contains u itself. The
resulting conjugator acts on every label by the same translation. Only the
two specified orbit matches are used. Noncommutation is preserved because
H normalizes the first module.

This is the change of endpoint used in Aschbacher--Smith, 14.6.24(4),
printed p.1041. It does not assert preservation of a normalized graph edge.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- Translating one endpoint by a normalizer preserves noncommutation. -/
theorem noncommuting_conjugate_mul_left
    (U H : Subgroup G) (hHU : H ≤ normalizer (U : Set G))
    (g x : G) (hx : x ∈ H)
    (hn : ¬ U ≤ centralizer (U.map (MulAut.conj g).toMonoidHom : Set G)) :
    ¬ U ≤ centralizer (U.map (MulAut.conj (x * g)).toMonoidHom : Set G) := by
  intro hc
  apply hn
  intro a ha b hb
  apply (MulAut.conj x).injective
  have hb' : (MulAut.conj x) b ∈ U.map (MulAut.conj (x * g)).toMonoidHom := by
    change (MulAut.conj x) b ∈ U.conjBy (x * g)
    rw [conjBy_mul]
    exact mem_map_of_mem (MulAut.conj x).toMonoidHom hb
  simpa only [map_mul, MulAut.conj_apply] using hc ((hHU hx a).mp ha) _ hb'

/-- A common point of the two specified orbits produces a translated crossing
for the original u. The equality for every label records the endpoint change. -/
theorem translated_crossing_of_orbit_intersection
    (U H : Subgroup G) (hHU : H ≤ normalizer (U : Set G))
    (u : G) (hu : u ∈ U) (g a b : G)
    (hga : (MulAut.conj g) b = a)
    (ha : ∃ x ∈ H, (MulAut.conj x) u = a)
    (hb : ∃ y ∈ H, (MulAut.conj y) u = b)
    (hn : ¬ U ≤ centralizer (U.map (MulAut.conj g).toMonoidHom : Set G)) :
    ∃ x ∈ H, ∃ k : G,
      k = x⁻¹ * g ∧
      (∀ A : Subgroup G, A.map (MulAut.conj k).toMonoidHom =
        (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom) ∧
      u ∈ U.map (MulAut.conj k).toMonoidHom ∧
      (∃ y ∈ H, (MulAut.conj y) u = (MulAut.conj k⁻¹) u) ∧
      ¬ U ≤ centralizer (U.map (MulAut.conj k).toMonoidHom : Set G) := by
  obtain ⟨x,hx,hxu⟩ := ha
  obtain ⟨y,hy,hyu⟩ := hb
  have hgb : (MulAut.conj g) b = (MulAut.conj x) u := hga.trans hxu.symm
  have hku : (MulAut.conj (x⁻¹ * g)) b = u := by
    have he := congrArg (MulAut.conj x⁻¹) hgb
    simpa [MulAut.conj_apply,mul_assoc] using he
  refine ⟨x,hx,x⁻¹ * g,rfl,fun A => conjBy_mul A x⁻¹ g,?_,?_,
    noncommuting_conjugate_mul_left U H hHU g x⁻¹ (H.inv_mem hx) hn⟩
  · exact ⟨b,hyu ▸ (hHU hy u).mp hu,hku⟩
  · refine ⟨y,hy,hyu.trans ?_⟩
    have he := congrArg (MulAut.conj (x⁻¹ * g)⁻¹) hku
    simpa [MulAut.conj_apply,mul_assoc] using he

end Subgroup
