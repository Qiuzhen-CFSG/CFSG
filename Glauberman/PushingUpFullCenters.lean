module
public import Glauberman.FixedNormalPairCenters
public import Glauberman.PushingUpIntersectionRows

/-!
# Full centers in the original Main Hypothesis

Finite intersection descent constructs an elementary subgroup of maximum
abelian order in both original Sylows. Their centers and the center of
O₂(H) are therefore elementary and coincide with central omega. Generalized
Fitting self-centralization identifies the ambient-fixed part as Z(H), while
the Sylow-fixed part is the full embedded Sylow center. These are the actual
center identifications used before the intersection-lattice covering step.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition4.6(d)–(g),
printedpp46–47. All natural-recognition inputs are discharged internally.
-/

public section
open Subgroup Theory.GroupTheory
namespace Glauberman
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]

/-- Under the original Main Hypothesis, central omega is the full center
of the original Sylow and of its literal two-core. -/
theorem original_psl2_four_omegaCenters_eq_centers
    (hF : Nat.card F = 4) (S : Sylow 2 H) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoInvariantNormal (S : Subgroup H) α) :
    omegaCenterIn (S : Subgroup H) = centerIn (S : Subgroup H) ∧
      omegaCenterIn (pCore 2 H) = centerIn (pCore 2 H) := by
  obtain ⟨q,hq,hk,_,_,_,E,hE⟩ := original_psl2_four_omegaAction_recognition
    hF S hu K e hf hno.noCharacteristicNormal
  obtain ⟨g,_,hinter,hpair⟩ := original_numerical_pair_of_natural_quotient
    hF S α hu K e hno q hq hk E hE
  obtain ⟨hS,_,hQ⟩ := hpair.omegaCenters_eq_centers
  rw [hinter] at hQ
  exact ⟨hS,hQ⟩
/-- The ambient-fixed part of the full center of O₂(H) is exactly Z(H),
and the Sylow-fixed part is exactly the full original Sylow center. -/
theorem original_psl2_four_full_center_fixed_spaces
    (hF : Nat.card F = 4) (S : Sylow 2 H) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoInvariantNormal (S : Subgroup H) α) :
    omegaCenterIn (pCore 2 H) ⊓ center H = center H ∧
      omegaCenterIn (pCore 2 H) ⊓ centralizer (S : Set H) = centerIn (S : Subgroup H) := by
  obtain ⟨hS,hQ⟩ := original_psl2_four_omegaCenters_eq_centers hF S α hu K e hf hno
  have hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
    simpa only [hf] using centralizer_generalizedFitting_le H
  have hzQ : center H ≤ pCore 2 H :=
    (center_le_centralizer (pCore 2 H : Set H)).trans hc
  constructor
  · rw [hQ]
    exact inf_eq_right.mpr (le_inf hzQ (center_le_centralizer _))
  · have hQS : pCore 2 H ≤ (S : Subgroup H) := pCore_isPGroup.le_sylow_of_normal S
    have hzS : centerIn (S : Subgroup H) ≤ pCore 2 H :=
      inf_le_right.trans ((centralizer_le hQS).trans hc)
    exact (omegaCenterIn_eq_inf_of_center_le (pCore 2 H) (S : Subgroup H) hQS hzS).symm.trans hS
end Glauberman
