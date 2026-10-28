module
public import Theory.SpecificGroups.SU3.ThreeWeightLift
public import Theory.Representation.ThreeWeightSquare.CentralQuotient

/-!
# The three-weight square theorem on the original PSU₃ model

Apply the compatible two-power lift through the actual special-to-projective
map. Its faithful matrix inclusion and characteristic-prime scalar kernel
satisfy the central-quotient three-weight theorem without a replacement action
or quotient. This discharges the odd nondefining PSU₃ input of A.3.15.
-/

public section
open Matrix Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm.ThreeWeightLift
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- A two-power automorphism preserving a nondefining p-subgroup has square one there. -/
theorem square_on_pSubgroup
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p q : ℕ} [Fact p.Prime] [CharP F q]
    (hq : q.Prime) (ho : Odd q)
    (hcard : Nat.card F = q^2) (hfixed : Nat.card {x : F // J.conj x = x} = q)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hp : 3 < p) (hpq : p ≠ q)
    (β : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hβ : ∃ n : ℕ, β^(2^n) = 1)
    (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hP : IsPGroup p P)
    (hPβ : ∀ x, β x ∈ P ↔ x ∈ P) :
    ∀ b ∈ P, β (β b) = b := by
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨n, hn⟩ := hβ
  obtain ⟨α, hc, hα, hf⟩ := exists_lift J hq ho hcard hfixed hJ β n hn
  exact Representation.ThreeWeightSquare.central_quotient_square hp hpq
    J.specialSubgroup.subtype Subtype.val_injective
    J.specialToProjective J.specialToProjective_surjective
    J.specialToProjective_ker_le_center (kernel_card_cast_ne_zero J hq hcard)
    P hP α β hc ⟨n, hα⟩ hPβ hf

end BenderSuzuki.MatrixGroups.HermitianForm.ThreeWeightLift
