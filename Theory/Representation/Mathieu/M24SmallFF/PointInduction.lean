module
public import Theory.Representation.Mathieu.M24SmallFF.PointInduction.Transport
public import Theory.Representation.Mathieu.M24SmallFF.PointInduction.Restriction

/-!
# Three native sources for small irreducible M24 representations

Select a simple socle constituent of the actual M23 point restriction.
The proved binary M23 degree gap and identity-marked recognition give a
fixed line, the native code, or the native cocode. Point induction then
constructs a nonzero map from Full, Full ⊗ Code, or Full ⊗ Cocode into the
original irreducible M24 action. Only the binary degree bound 24 is used;
faithfulness and the FF hypothesis are reserved for the three source-map
exclusions in the B.4 consumer. The final callback discharges the source
selection step of that exclusion on the same σ and literal tensor actions.

Source: Aschbacher–Smith, B.4.2 and H.13.1; Guralnick–Malle,
Classification of 2F-modules I, Proposition 5.1, M24 paragraph.
-/

public section
open Representation Sporadic.Mathieu MathieuCode
namespace Representation.MathieuSmall.M24SmallFF.PointInduction
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem exists_nonzero_native_source
    (σ : Representation (ZMod 2) M24 V) [σ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 24) :
    (∃ f : fullRepresentation.IntertwiningMap σ, f ≠ 0) ∨
      (∃ f : (fullRepresentation.tprod codeRepresentation).IntertwiningMap σ, f ≠ 0) ∨
      (∃ f : (fullRepresentation.tprod cocodeRepresentation).IntertwiningMap σ, f ≠ 0) := by
  rcases point_fixed_or_native_map σ hd with h | ⟨f,hf⟩ | ⟨f,hf⟩
  · exact Or.inl (permutation_map_of_point_fixed σ h)
  · exact Or.inr (Or.inl ⟨tensorInduce codeRepresentation σ f,
      tensorInduce_ne_zero codeRepresentation σ f hf⟩)
  · exact Or.inr (Or.inr ⟨tensorInduce cocodeRepresentation σ f,
      tensorInduce_ne_zero cocodeRepresentation σ f hf⟩)

/-- The three literal source exclusions contradict a small irreducible σ.
The FF-specific exclusion producers supply these callbacks in B.4. -/
theorem false_of_native_source_maps_eq_zero
    (σ : Representation (ZMod 2) M24 V) [σ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 24)
    (hfull : ∀ f : fullRepresentation.IntertwiningMap σ, f = 0)
    (hcode : ∀ f : (fullRepresentation.tprod codeRepresentation).IntertwiningMap σ, f = 0)
    (hcocode : ∀ f : (fullRepresentation.tprod cocodeRepresentation).IntertwiningMap σ, f = 0) :
    False := by
  rcases exists_nonzero_native_source σ hd with ⟨f,hf⟩ | ⟨f,hf⟩ | ⟨f,hf⟩
  · exact hf (hfull f)
  · exact hf (hcode f)
  · exact hf (hcocode f)
end Representation.MathieuSmall.M24SmallFF.PointInduction
