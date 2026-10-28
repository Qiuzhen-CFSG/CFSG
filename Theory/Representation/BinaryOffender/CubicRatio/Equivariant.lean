module
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.BinaryOffender.EquivariantOffender
/-!
# Cubic bounds under equivariant identifications

An injective actor map and an intertwining linear equivalence preserve the
cubic displacement condition, fixed codimension and elementary actor rank.
Thus every finite natural-number cubic bound transfers to the target action.
The source application compares the literal centralizer quotient in 3.1.8
with the faithful action on the same whole orbit in 3.2.5.
-/
public section
open Subgroup
namespace Representation.BinaryOffender
variable {G H V W : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) H W)

theorem IsCubic.map_equivariant (f : G →* H) (E : V ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (ρ g v) = σ (f g) (E v))
    {A : Subgroup G} (hA : IsCubic ρ A) : IsCubic σ (A.map f) := by
  have hd (g : G) (v : V) : E (displacement ρ g v) = displacement σ (f g) (E v) := by
    simp only [displacement, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hE]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ w
  obtain ⟨v, rfl⟩ := E.surjective w
  rw [← hd, ← hd, ← hd, hA a ha b hb c hc v, map_zero]

theorem cubicRatio_le_nat_of_equivariant [Finite G] [Finite H]
    (f : G →* H) (hf : Function.Injective f) (E : V ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (ρ g v) = σ (f g) (E v)) (n : ℕ)
    (h : cubicRatio ρ ≤ n) : cubicRatio σ ≤ n := by
  obtain ⟨A, hA, hc, hr⟩ := (cubicRatio_le_nat_iff ρ n).mp h
  let : IsElementaryAbelian 2 A := hA.2
  refine (cubicRatio_le_nat_iff σ n).mpr ⟨A.map f, ⟨?_, IsElementaryAbelian.map f⟩,
    hc.map_equivariant ρ σ f E hE, ?_⟩
  · intro hb
    apply hA.1
    apply Subgroup.map_injective hf
    simpa only [Subgroup.map_bot] using hb
  · rw [← fixedCodim_map_equivariant ρ σ f E hE, rank_map_injective f hf]
    exact hr
end Representation.BinaryOffender
