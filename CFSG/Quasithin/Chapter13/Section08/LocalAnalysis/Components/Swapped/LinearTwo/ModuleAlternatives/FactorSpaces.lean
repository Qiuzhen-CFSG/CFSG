module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SeedTransport

/-!
# Canonical factor spaces and the actual exchange operator

For two normal factors, the factor spaces are the literal commutator
submodules. If the factors generate the actor and the actor generates the
module by commutators, these spaces sum to the whole module. An operator
intertwining a factor-exchanging group automorphism exchanges the spaces.
Conjugation in an overgroup supplies exactly such an operator.

Together with cross-factor fixation from the earlier module classification,
these constructions feed the existing projected-marking obstruction. The
sum need not be direct, so the result also treats source case (b1).
This module does not assert the classification or its cross-factor fixation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.8.16(1), printed p.952 (PDF p.969).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
variable {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]

/-- The canonical commutator spaces sum to the module; no directness is claimed. -/
theorem factor_spaces_sum (ρ : Representation (ZMod 2) D U) (A B : Subgroup D)
    [A.Normal] [B.Normal] (hAB : A ⊔ B = ⊤)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤) :
    (movedSubrepresentation ρ A).toSubmodule ⊔
      (movedSubrepresentation ρ B).toSubmodule = ⊤ := by
  let W : Subrepresentation ρ := movedSubrepresentation ρ A ⊔ movedSubrepresentation ρ B
  have hA : A ≤ W.quotientRepresentation.ker := by
    intro a ha
    apply LinearMap.ext
    intro v
    obtain ⟨u, rfl⟩ := W.toSubmodule.mkQ_surjective v
    change W.toSubmodule.mkQ (ρ a u) = W.toSubmodule.mkQ u
    apply (Submodule.Quotient.eq W.toSubmodule).mpr
    exact (show (movedSubrepresentation ρ A).toSubmodule ≤ W.toSubmodule from le_sup_left)
      (Submodule.subset_span ⟨a, ha, u, Submodule.mem_top, rfl⟩)
  have hB : B ≤ W.quotientRepresentation.ker := by
    intro b hb
    apply LinearMap.ext
    intro v
    obtain ⟨u, rfl⟩ := W.toSubmodule.mkQ_surjective v
    change W.toSubmodule.mkQ (ρ b u) = W.toSubmodule.mkQ u
    apply (Submodule.Quotient.eq W.toSubmodule).mpr
    exact (show (movedSubrepresentation ρ B).toSubmodule ≤ W.toSubmodule from le_sup_right)
      (Submodule.subset_span ⟨b, hb, u, Submodule.mem_top, rfl⟩)
  have hk : (⊤ : Subgroup D) ≤ W.quotientRepresentation.ker := hAB ▸ sup_le hA hB
  have hc : subspaceCommutator ρ ⊤ ⊤ ≤ W.toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, _, u, _, rfl⟩
    apply (Submodule.Quotient.eq W.toSubmodule).mp
    exact congrArg (fun f => f (W.toSubmodule.mkQ u)) (hk (Subgroup.mem_top g))
  have he : W.toSubmodule = ⊤ := top_unique (hfull ▸ hc)
  exact (Subrepresentation.toSubmodule_sup _ _).symm.trans he

/-- Equivariance under an actual group automorphism transports the canonical
commutator space, retaining the marked subgroup image. -/
theorem moved_map_automorphism (ρ : Representation (ZMod 2) D U)
    (α : D ≃* D) (s : U ≃ₗ[ZMod 2] U)
    (hs : ∀ g u, s (ρ g u) = ρ (α g) (s u)) (A : Subgroup D) :
    (subspaceCommutator ρ ⊤ A).map s.toLinearMap =
      subspaceCommutator ρ ⊤ (A.map α.toMonoidHom) := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, u, _, rfl⟩
    change s (ρ a u - u) ∈ subspaceCommutator ρ ⊤ (A.map α.toMonoidHom)
    rw [map_sub, hs]
    exact Submodule.subset_span ⟨α a, mem_map_of_mem _ ha, s u, Submodule.mem_top, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨a, ha, rfl⟩, u, _, rfl⟩
    obtain ⟨v, rfl⟩ := s.surjective u
    refine ⟨ρ a v - v, Submodule.subset_span ⟨a, ha, v, Submodule.mem_top, rfl⟩, ?_⟩
    exact (s.map_sub _ _).trans (congrArg (fun w => w - s v) (hs a v))

/-- The exchange operator in the source is the action of the actual moving
ambient group element on the normal component orbit. -/
theorem operator_conjugation_intertwines (ρ : Representation (ZMod 2) D U)
    (K₀ : Subgroup D) [K₀.Normal] (t : D) (k : K₀) (u : U) :
    operator ρ t ((ρ.comp K₀.subtype) k u) =
      (ρ.comp K₀.subtype) ((MulAut.conjNormal t) k) (operator ρ t u) := by
  change ρ t (ρ (k : D) u) = ρ (t * (k : D) * t⁻¹) (ρ t u)
  simp only [map_mul, Module.End.mul_apply, inv_self_apply]

/-- All constructed factor-space premises feed the existing obstruction.
The only representation-theoretic input left here is cross-factor fixation;
its derivation belongs to the F.9.18/B.5 alternatives. -/
theorem not_factor_sum_of_projected_markings {P : Type*} [Group P]
    (ρ : Representation (ZMod 2) D U) (A B L₀ Lplus : Subgroup D)
    [A.Normal] [B.Normal] (hAB : A ⊔ B = ⊤)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (α : D ≃* D) (s : U ≃ₗ[ZMod 2] U)
    (hs : ∀ g u, s (ρ g u) = ρ (α g) (s u)) (hswap : B.map α.toMonoidHom = A)
    (hcross₁ : subspaceCommutator ρ ⊤ B ≤ fixedSpace ρ A)
    (hcross₂ : subspaceCommutator ρ ⊤ A ≤ fixedSpace ρ B)
    (X : Submodule (ZMod 2) U) (hX : X ≠ ⊥)
    (hXgen : subspaceCommutator ρ X Lplus = X)
    (hXswap : X.map s.toLinearMap = X) (hXfix : X ≤ fixedSpace ρ L₀)
    (f : D →* P) (hker : f.ker = B) (himage : L₀.map f = Lplus.map f) : False := by
  apply not_sum_of_projected_markings ρ (movedSubrepresentation ρ A)
    (movedSubrepresentation ρ B) X A B L₀ Lplus s
    (factor_spaces_sum ρ A B hAB hfull) hX hXgen _ hcross₁ hcross₂ hXswap _ f hker himage hXfix
  · rw [hAB]
    exact le_top
  · change (subspaceCommutator ρ ⊤ B).map s.toLinearMap ≤ subspaceCommutator ρ ⊤ A
    rw [moved_map_automorphism ρ α s hs B, hswap]

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
