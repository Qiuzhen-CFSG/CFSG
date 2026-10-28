module

public import Theory.Representation.InvertedCubicTensor

/-!
# A commuting action on a binary S₃ plane

If the cubic subgroup of S₃ has no fixed vectors on a two-dimensional binary
module, the inverter-fixed multiplicity space has dimension one. Its only
invertible binary linear map is the identity. Consequently every group
commuting with S₃ fixes this plane pointwise.

This is the seed-action calculation used in Aschbacher–Smith 13.8.21(1),
printed p.957, with the explicit inverted-cubic decomposition.
-/

public section
namespace InvertedCubicTensor

open Representation Representation.BinaryOffender InvertedCubicTensor

variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
private theorem binary_line_fixed (ρ : Representation (ZMod 2) K V)
    (hd : Module.finrank (ZMod 2) V = 1) (g : K) (v : V) : ρ g v = v := by
  by_cases hv : v = 0
  · simp [hv]
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one hd hv (ρ g v)
  have han : a ≠ 0 := by
    intro he
    rw [he, zero_smul] at ha
    have hh := congrArg (ρ g⁻¹) ha
    simp only [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] at hh
    exact hv hh.symm
  have ha1 : a = 1 := by
    have hc : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    exact hc a han
  simpa only [ha1, one_smul] using ha.symm

/-- A commuting factor fixes a binary plane with fixed-point-free cubic action. -/
theorem left_fixed_of_finrank_two (ρ : Representation (ZMod 2) (K × S₃) V)
    (hd : Module.finrank (ZMod 2) V = 2)
    (h : fixedSpace (rightAction ρ) (alternatingGroup (Fin 3)) = ⊥)
    (k : K) (v : V) : ρ (k, 1) v = v := by
  have he := (productPairEquiv ρ h).finrank_eq
  rw [Module.finrank_prod, hd] at he
  change Module.finrank (ZMod 2) (multiplicitySpace (rightAction ρ)) +
    Module.finrank (ZMod 2) (multiplicitySpace (rightAction ρ)) = 2 at he
  have hi : Module.finrank (ZMod 2) (multiplicitySpace (rightAction ρ)) = 1 := by omega
  obtain ⟨⟨a,b⟩, rfl⟩ := (productPairEquiv ρ h).surjective v
  rw [← productPairEquiv_equivariant,
    binary_line_fixed (productMultiplicity ρ) hi,
    binary_line_fixed (productMultiplicity ρ) hi]

end InvertedCubicTensor
