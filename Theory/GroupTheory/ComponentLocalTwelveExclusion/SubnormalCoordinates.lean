module

public import Theory.GroupTheory.ComponentLocalTwelveExclusion.CentralOrbit

/-!
# Subnormal coordinates in a central component orbit

A two-perfect group embedded subnormally in the join of a component local
and a two-group lies in the local's conjugate orbit. Restrict the central
quotient of that orbit to obtain a map to a finite direct power of the native
local. Its kernel remains central and its image remains subnormal.

The component need only be subnormal in the displayed ambient group, and
the two-group may permute components. This isolates the group-theoretic
transfer used in Aschbacher–Smith 2.3.9(7), printed p.526, and E.6.7–8,
printed pp.246–248. The Held local-block calculation is an actual consumer.
-/

public section

namespace Theory.GroupTheory.ComponentLocalTwelveExclusion
open Subgroup
variable {G : Type*} [Group G]

/-- Two-perfection localizes the embedded group in the orbit; the literal
orbit quotient preserves relative subnormality and has central kernel. -/
theorem subnormal_central_coordinates [Finite G]
    {L K A : Subgroup G} {P B : Type*} [Group P] [Group B]
    (hL : IsComponent G L) (hKL : K ≤ L) (hA : IsPGroup 2 A)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (f : K →* P) (hf : Function.Surjective f) (hcentral : f.ker ≤ center K)
    (hkill : ∀ k : K, inclusion hKL k ∈ center L → f k = 1)
    (hp : IsPPerfect 2 B) (g : B →* (K ⊔ A : Subgroup G))
    (hg : Function.Injective g) (hs : g.range.IsSubnormal) :
    ∃ n : ℕ, ∃ q : B →* (Fin n → P), q.ker ≤ center B ∧ q.range.IsSubnormal := by
  obtain ⟨n, q, hq, hqc⟩ :=
    ComponentLocalTwelveExclusion.central_power_of_component_orbit hL hKL hinv f hf hcentral hkill
  let X := K ⊔ A
  let N := (componentOrbit K A).subgroupOf X
  have hgr : g.range ≤ N := le_local_orbit_of_isPPerfect K A hA g.range
    (hp.of_surjective g.rangeRestrict g.rangeRestrict_surjective)
  let r : B →* N := g.codRestrict N (fun x => hgr ⟨x, rfl⟩)
  have hr : Function.Injective r := fun x y h => hg (congrArg Subtype.val h)
  have hrs : r.range.IsSubnormal := by
    rw [← MonoidHom.subgroupOf_range_eq_of_le g hgr]
    exact hs.subgroupOf
  let e : N ≃* componentOrbit K A := subgroupOfEquivOfLe (componentOrbit_le_sup K A)
  let j := e.toMonoidHom.comp r
  have hj : Function.Injective j := e.injective.comp hr
  refine ⟨n, q.comp j, ?_, ?_⟩
  · intro b hb
    apply mem_center_iff.mpr
    intro c
    apply hj
    simpa only [map_mul] using mem_center_iff.mp (hqc hb) (j c)
  · rw [MonoidHom.range_comp, MonoidHom.range_comp]
    exact (hrs.map e.surjective).map hq

end Theory.GroupTheory.ComponentLocalTwelveExclusion

end
