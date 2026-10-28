module
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Theory.Representation.BinaryOffender.CubicRatio

/-!
# Cubic bounds on an equivariant quotient

A surjective equivariant linear map preserves cubicity and can only decrease
fixed codimension. Hence a cubic-ratio bound descends while retaining the
same acting group and the same elementary subgroup. In particular, no lifting
of elementary subgroups through an actor quotient is needed.

Source application: Aschbacher–Smith, D.3.9 and 3.2.6, passing from the
original binary module to its central quotient.
-/

public noncomputable section
namespace Representation.BinaryOffender
variable {G U V : Type*} [Group G]
  [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G U) (σ : Representation (ZMod 2) G V)
/-- Cubicity descends through a surjective intertwining map. -/
theorem cubic_of_equivariant_surjection (f : U →ₗ[ZMod 2] V) (hf : Function.Surjective f)
    (he : ∀ g v, f (ρ g v) = σ g (f v)) {A : Subgroup G}
    (hc : IsCubic ρ A) : IsCubic σ A := by
  have hd (g : G) (v : U) : f (displacement ρ g v) = displacement σ g (f v) := by
    simp only [displacement,LinearMap.sub_apply,LinearMap.id_apply,map_sub,he]
  intro a ha b hb c hc' v
  obtain ⟨u,rfl⟩ := hf v
  rw [← hd,← hd,← hd,hc a ha b hb c hc' u,map_zero]

/-- The cubic ratio bound descends at the unchanged actor. -/
theorem cubicRatio_le_nat_of_equivariant_surjection [Finite G] [FiniteDimensional (ZMod 2) U]
    (f : U →ₗ[ZMod 2] V) (hf : Function.Surjective f)
    (he : ∀ g v, f (ρ g v) = σ g (f v)) (n : ℕ)
    (hc : cubicRatio ρ ≤ n) : cubicRatio σ ≤ n := by
  obtain ⟨A,hA,hcA,hdA⟩ := (cubicRatio_le_nat_iff ρ n).mp hc
  exact (cubicRatio_le_nat_iff σ n).mpr ⟨A,hA,
    cubic_of_equivariant_surjection ρ σ f hf he hcA,
    (fixedCodim_le_of_equivariant_surjection ρ σ f hf he A).trans hdA⟩
end Representation.BinaryOffender
