module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Transfer.SourceFusion.LocalCoordinates
/-!
# Finite fusion-coordinate calculations

The involutory lifts leave three noncentral candidate pairs outside the seven
permitted words. These finite identities reduce their exclusion to ambient
fusion arguments; they assert no ambient conjugacy.

Source: Held, Illinois J. Math. 13 (1969), pp.233--234.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.SourceFusion
open TransferModel (Model l z t m)
local notation "p₀" => TransferModel.p

@[expose] public def Allowed (x : Model) : Prop :=
  x = p₀ ∨ x = l * t ∨ x = p₀ * (l * t) ∨
  x = z * m ∨ x = p₀ * (z * m) ∨
  x = z * l * m ∨ x = p₀ * (z * l * m)

public instance (x : Model) : Decidable (Allowed x) := by unfold Allowed; infer_instance

namespace Local

public theorem central_p : ∀ x : Model, x * p₀ = p₀ * x := by decide +kernel

public theorem p_commutator : t * m * t⁻¹ * m⁻¹ = p₀ := by decide +kernel

set_option maxHeartbeats 800000 in
public theorem commutator_cases : ∀ x y : Model,
    x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = p₀ := by decide +kernel

set_option maxHeartbeats 800000 in
public theorem lift_involution_cases : ∀ x : Model, (liftWord x) ^ 2 = 1 →
    Allowed x ∨ (∀ y : Model, x * y = y * x) ∨
    (∃ b : Fin 2, x = p₀ ^ b.val * t) ∨
    (∃ b : Fin 2, x = p₀ ^ b.val * m) ∨
    (∃ b : Fin 2, x = p₀ ^ b.val * (z * l * t)) := by decide +kernel

public theorem mu_lift_square : ∀ x : Model,
    (Coordinates.mu * liftWord x)^2 = (liftWord x)^2 := by decide +kernel

public theorem m_shift_t : ∀ b : Fin 2,
    m ^ b.val * (p₀ ^ b.val * t) * (m ^ b.val)⁻¹ = t := by decide +kernel

public theorem m_shift_zlt : ∀ b : Fin 2,
    m ^ b.val * (p₀ ^ b.val * (z*l*t)) * (m ^ b.val)⁻¹ = z*l*t := by decide +kernel

public theorem m_shift_lt : ∀ b : Fin 2,
    m ^ (b.val + 1) * (p₀ ^ (b.val + 1) * (l*t)) * (m ^ (b.val + 1))⁻¹ = l*t := by decide +kernel

public theorem t_shift_zm : ∀ b : Fin 2,
    t ^ (b.val + 1) * (p₀ ^ (b.val + 1) * (z*m)) * (t ^ (b.val + 1))⁻¹ = z*m := by decide +kernel

public theorem central_before : ∀ d : Fin 2,
    (∀ x : Model, (p₀ ^ (d.val + 1) * z) * x = x * (p₀ ^ (d.val + 1) * z)) ∧
    p₀ ^ (d.val + 1) * z ≠ p₀ := by decide +kernel

public theorem m_shift_after : ∀ b d : Fin 2,
    m ^ (b.val + d.val + 1) * (z*l*t) * (m ^ (b.val + d.val + 1))⁻¹ =
      (p₀ ^ (b.val + 1) * (l*t)) * (p₀ ^ d.val * z) := by decide +kernel

open Coordinates in
public theorem mup_conjugator : ∀ b c : Fin 2,
    (rho ^ (if c = 0 then 2 else 1) * tau ^ b.val) *
      (Coordinates.mu ^ c.val * liftWord (p₀ ^ b.val * m)) *
      (rho ^ (if c = 0 then 2 else 1) * tau ^ b.val)⁻¹ = Coordinates.mu := by
  decide +kernel

end Local
end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.SourceFusion
