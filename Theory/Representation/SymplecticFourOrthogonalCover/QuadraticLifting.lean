module
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedLifting
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Quadraticity lifts through the whole symplectic central cover

A fixed natural displacement has every lift fixed in a central cover.
Consequently quadratic action on the natural quotient gives trivial second
commutator on the entire embedded cover, including its full fixed kernel.
The application uses the literal covering embedding and actor homomorphism.

Source: MS93 (1.5)(ii), used in (3.6), printed p.871.
-/

public noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace Representation.SymplecticFourOrthogonalCover
open Representation.OneCohomology
variable {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]

theorem embedded_quadratic_of_natural_quadratic
    (U A : Subgroup G) (j : Multiplicative W →* G) (hjU : j.range = U)
    (β : A →* L (K := F)) (σ : Representation (ZMod 2) (L (K := F)) W)
    (hact : ∀ a : A, ∀ w : W, j (Multiplicative.ofAdd (σ (β a) w)) =
      (a:G)*j (Multiplicative.ofAdd w)*(a:G)⁻¹)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (hq : ∀ a b : A, ∀ v, binaryNatural (β a) (binaryNatural (β b) v-v) =
      binaryNatural (β b) v-v) : ⁅⁅U,A⁆,A⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rw [commutator_comm U A]
  apply commutator_le.mpr
  intro b hb u hu
  obtain ⟨w,rfl⟩ := (hjU.symm ▸ hu : u ∈ j.range)
  have he : j (Multiplicative.ofAdd (σ (β ⟨b,hb⟩) w.toAdd-w.toAdd)) = ⁅b,j w⁆ := by
    rw [ofAdd_sub,div_eq_mul_inv,map_mul,map_inv,hact]
    rfl
  rw [←he]
  intro a ha
  have hf : σ (β ⟨a,ha⟩) (σ (β ⟨b,hb⟩) w.toAdd-w.toAdd) =
      σ (β ⟨b,hb⟩) w.toAdd-w.toAdd := by
    apply cover_fixed_of_projection_fixed p hp
    rw [map_sub,p.isIntertwining]
    exact hq ⟨a,ha⟩ ⟨b,hb⟩ (p w.toAdd)
  have hh := congrArg (fun v => j (Multiplicative.ofAdd v)) hf
  rw [hact] at hh
  exact mul_inv_eq_iff_eq_mul.mp hh
end Representation.SymplecticFourOrthogonalCover
