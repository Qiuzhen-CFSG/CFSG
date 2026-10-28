module

public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.FirstCohomologyDuality.QuotientGeometry
public import Theory.Representation.BinaryOffender.DualFixedSupplement

/-!
# Dual quadratic bounds through equivariant quotients

An equivariant quotient cannot increase the dimension moved by a fixed
subgroup. Duality identifies that dimension with the fixed codimension on
the dual, and preserves quadraticity. Thus the same elementary actor proves
the dual ratio bound for every quotient of a concrete covering module.

This is the transport used for the natural central covers in
Aschbacher–Smith B.5.13, printed pp.110–112.
-/

public section
namespace Representation.BinaryOffender
open Representation.OneCohomology
variable {G U V : Type*} [Group G] [Finite G]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G U} {σ : Representation (ZMod 2) G V}

/-- The dual bound descends through the actual surjective intertwiner. -/
theorem dual_quadraticRatio_le_two_of_surjective
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f)
    (hq : quadraticRatio ρ.dual ≤ 2) : quadraticRatio σ.dual ≤ 2 := by
  obtain ⟨A, hA, ha, hb⟩ := (quadraticRatio_le_two_iff ρ.dual).mp hq
  refine (quadraticRatio_le_two_iff σ.dual).mpr ⟨A, hA, ?_, ?_⟩
  · apply (isQuadratic_dual_iff σ A).mpr
    exact quadratic_of_equivariant_surjection ρ σ f.toLinearMap hf
      (fun g v => IntertwiningMap.isIntertwining ρ σ f g v) A ((isQuadratic_dual_iff ρ A).mp ha)
  · let fA : Representation.IntertwiningMap (ρ.comp A.subtype) (σ.comp A.subtype) :=
      f.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _
        (fun g v => IntertwiningMap.isIntertwining ρ σ f g v)
    have hm := map_coinvariants_of_surjective fA hf
    have hd := Submodule.finrank_map_le fA.toLinearMap (Coinvariants.ker (ρ.comp A.subtype))
    rw [hm] at hd
    have hρ := finrank_dual_quotient_invariants (ρ.comp A.subtype)
    have hσ := finrank_dual_quotient_invariants (σ.comp A.subtype)
    exact hσ.le.trans (hd.trans (hρ.ge.trans hb))

end Representation.BinaryOffender
