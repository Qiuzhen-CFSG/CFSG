module

public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Best offenders under an equivariant identification

A group equivalence identifies subgroup lattices, while its compatible linear
coordinates identify fixed spaces. Consequently it preserves weights and best
offenders, including each comparison with a proper subgroup.

Source: Aschbacher–Smith B.1.1–3 and B.1.11, printed pp.67–69,72–73.
-/

public section
namespace Representation.BinaryOffender
variable {G D V W : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W)
  (f : G ≃* D) (E : V ≃ₗ[ZMod 2] W)
  (hE : ∀ g v, E (ρ g v) = σ (f g) (E v))

include hE

/-- Equivariant group and module coordinates preserve the source weight. -/
theorem weight_map_equivariant (A : Subgroup G) :
    weight ρ A = weight σ (A.map f.toMonoidHom) := by
  unfold weight
  rw [rank_map_injective _ f.injective]
  have h := E.finrank_map_eq (fixedSpace ρ A)
  rw [fixedSpace_map_equivariant ρ σ f.toMonoidHom E hE] at h
  rw [h]

/-- Best-offender membership is preserved on the same transported actor. -/
theorem IsBestOffender.map_equivariant [FiniteDimensional (ZMod 2) V]
    {A : Subgroup G} (hA : IsBestOffender ρ A) :
    IsBestOffender σ (A.map f.toMonoidHom) := by
  have hoff := (hA.isOffender ρ).map_equivariant ρ σ f.toMonoidHom f.injective E hE
  refine ⟨hoff.1, ?_⟩
  intro B hB
  let S := f.mapSubgroup
  have hle : S.symm B ≤ A := S.symm_apply_le.mpr hB
  have he : (S.symm B).map f.toMonoidHom = B := S.apply_symm_apply B
  rw [← weight_map_equivariant ρ σ f E hE A, ← he,
    ← weight_map_equivariant ρ σ f E hE (S.symm B)]
  exact hA.2 _ hle

end Representation.BinaryOffender
