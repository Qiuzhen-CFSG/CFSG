/-
Authors: OpenAI
-/

module

public import BenderSuzuki.External.Huppert.IV.theorem_5_2.Core
public import BenderSuzuki.External.Huppert.IV.theorem_5_1

/-!
# Huppert IV.5.2

Book-order entry file for the center-transport step that turns weak-closure
failure of `Z(S)` into the Burnside IV.5.1 configuration.

Principal exported declarations include:
* `hkt_huppert_iv52_characteristic_center_transport_subgroup`
* `hkt_huppert_iv52_normalizer_failure_of_center_mismatch`
-/

namespace BenderSuzuki
namespace External


universe u
/-- Huppert IV.5.2, characteristic-center transport form. -/
public theorem huppert_IV_5_2_characteristic_center_transport_subgroup
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S T : Sylow q Q)
    (hcenter_le_T :
      centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q)) :
    ∃ M : Subgroup Q,
      IsPGroup q M ∧
        M ≤ (S : Subgroup Q) ∧
          (S : Subgroup Q) ≤ Subgroup.normalizer (M : Set Q) ∧
            M ≤ (T : Subgroup Q) :=
  hkt_huppert_iv52_characteristic_center_transport_subgroup (Q := Q) (q := q) S T hcenter_le_T

/-- Huppert IV.5.2, normalizer-failure form. -/
public theorem huppert_IV_5_2_normalizer_failure_of_center_mismatch
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S T : Sylow q Q)
    (hcenter_le_T :
      centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q))
    (hcenter_ne_T :
      centerIn (G := Q) (S : Subgroup Q) ≠
        centerIn (G := Q) (T : Subgroup Q)) :
    ¬ (T : Subgroup Q) ≤
      Subgroup.normalizer
        ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q) :=
  hkt_huppert_iv52_normalizer_failure_of_center_mismatch (Q := Q) (q := q) S T hcenter_le_T hcenter_ne_T

end External
end BenderSuzuki
