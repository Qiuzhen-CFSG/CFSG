module

public import Theory.Representation.Mathieu.M24SmallFF.Mixed
public import Theory.Representation.Mathieu.M24SmallFF.Filtration
public import Theory.Representation.Mathieu.M24SmallFF.PointInduction

/-!
# Native M24 has no small faithful irreducible binary FF module

A simple constituent of the native M23 point restriction gives a nonzero map
from Full, Full tensor Code, or Full tensor Cocode into the original action.
The Golay filtration and the proved native code, exterior-square and
trace-kernel obstructions make all three maps zero. Thus a faithful
irreducible binary M24 action of degree at most 24 is not an FF module.

This is the unconditional native callback for the M24 branch of B.4.
It preserves the original vector space and action, and does not assume
small-degree recognition or realizations of the larger M24 matrix models.
Source: Aschbacher–Smith, B.4.2 and K.4, with the native H.13–H.16 modules.
-/

open Representation Sporadic.Mathieu MathieuCode BinaryOffender
namespace Representation.Mathieu.M24SmallFF
public section
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) M24 V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hff : IsFFModule ρ) (hd : Module.finrank (ZMod 2) V ≤ 24)
omit [FiniteDimensional (ZMod 2) V] in
include hf hff in
lemma full_map_zero (f : fullRepresentation.IntertwiningMap ρ) : f = 0 :=
  full_maps_zero_of_constituents ρ (trivial_map_zero ρ hf)
    (code_map_zero ρ hff) (cocode_map_zero ρ hff) f
include hf hff hd in
lemma full_code_map_zero (f : (fullRepresentation.tprod codeRepresentation).IntertwiningMap ρ) : f = 0 :=
  full_tensor_maps_zero_of_constituents ρ codeRepresentation
    (map_zero_of_equiv (Representation.TensorProduct.lid (ZMod 2) codeRepresentation)
      (code_map_zero ρ hff))
    (code_code_map_zero ρ hff hd) (cocode_code_map_zero ρ hf hd) f
include hf hff hd in
lemma full_cocode_map_zero (f : (fullRepresentation.tprod cocodeRepresentation).IntertwiningMap ρ) : f = 0 :=
  full_tensor_maps_zero_of_constituents ρ cocodeRepresentation
    (map_zero_of_equiv (Representation.TensorProduct.lid (ZMod 2) cocodeRepresentation)
      (cocode_map_zero ρ hff))
    (code_cocode_map_zero ρ hf hd) (cocode_cocode_map_zero ρ hff hd) f
include hf hd in
/-- No faithful irreducible binary representation of native M24 of degree at most 24 is FF. -/
theorem not_isFFModule : ¬ IsFFModule ρ := by
  intro hff
  exact Representation.MathieuSmall.M24SmallFF.PointInduction.false_of_native_source_maps_eq_zero ρ hd
    (full_map_zero ρ hf hff) (full_code_map_zero ρ hf hff hd) (full_cocode_map_zero ρ hf hff hd)
end
end Representation.Mathieu.M24SmallFF
