module
public import Theory.Representation.BinaryAlternatingFiveFixedPoint.Coordinates

/-!
# Deleted A₅ coordinates on invariant subspaces

The intersection of kernels of all maps to a fixed representation vanishes
on any representation that embeds into one with the same vanishing property.
For the binary deleted A₅ type, canonical splitting then gives finite-copy
coordinates on every invariant subspace. Its dimension bounds the number of
copies without assuming semisimplicity of the subspace.

Source: Aschbacher--Smith I.1.6 and the restriction step in 5.1.13,
printed pp.408,638.
-/

public noncomputable section
open Representation
namespace Representation
variable {k D V W E : Type*} [Field k] [Group D]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup E] [Module k E]

/-- An injective intertwiner preserves vanishing of the kernel intersection. -/
theorem typeReject_eq_bot_of_injective_map
    {ρ : Representation k D V} {τ : Representation k D W}
    (σ : Representation k D E) (f : ρ.IntertwiningMap τ)
    (hf : Function.Injective f) (hτ : typeReject τ σ = ⊥) :
    typeReject ρ σ = ⊥ := by
  apply bot_unique
  intro v hv
  have hm : f v ∈ typeReject τ σ := by
    rw [mem_typeReject_iff]
    intro g
    exact (mem_typeReject_iff ρ σ v).mp hv (g.comp f)
  have hz : f v = 0 := by
    rw [hτ] at hm
    exact hm
  exact hf (hz.trans (map_zero f).symm)

namespace BinaryAlternatingFiveFixedPoint
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Every invariant subspace has deleted coordinates, with its multiplicity bounded by dimension. -/
theorem subrepresentation_coordinates
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 5)) V)
    (hρ : typeReject ρ (BinaryPermutation.alternatingCoreRepresentation (Fin 5)) = ⊥)
    (U : Subrepresentation ρ) :
    ∃ m : ℕ, ∃ c : U.toSubmodule ≃ₗ[ZMod 2]
      (Fin m → BinaryPermutation.natural (Fin 5)),
      (∀ g v, c (U.toRepresentation g v) = fun i =>
        BinaryPermutation.alternatingNaturalRepresentation (Fin 5) g (c v i)) ∧
      4 * m ≤ Module.finrank (ZMod 2) V := by
  let f : U.toRepresentation.IntertwiningMap ρ :=
    ⟨U.toSubmodule.subtype, fun _ => rfl⟩
  have hU := typeReject_eq_bot_of_injective_map
    (BinaryPermutation.alternatingCoreRepresentation (Fin 5)) f Subtype.val_injective hρ
  obtain ⟨m,c,hc⟩ := exists_natural_coordinates_of_typeReject_eq_bot U.toRepresentation hU
  refine ⟨m,c,hc,?_⟩
  have he := c.finrank_eq
  have hd := BinaryPermutation.finrank_natural_odd (Fin 5) (by decide)
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at he
  have hb := Submodule.finrank_le U.toSubmodule
  simp only [Fintype.card_fin] at hd
  rw [hd] at he
  norm_num at he
  omega
end BinaryAlternatingFiveFixedPoint
end Representation
