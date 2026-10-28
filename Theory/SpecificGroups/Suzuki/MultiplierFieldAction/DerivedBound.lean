module

public import Theory.GroupTheory.Commutator.CentralElementaryEightQuotient
public import Theory.SpecificGroups.Suzuki.MultiplierFieldAction.RootQuotient

/-!
# Noncentrality of the lifted Suzuki root center

In a quasisimple covering of Sz(8) with kernel of order four, the full
inverse image of the root center cannot be central in the lifted root
group. The literal quotient by that inverse image is elementary abelian
of order eight. If the inverse image were central, the general class-two
bound would give derived order at most eight, whereas Sylow transfer and
the restricted covering map give derived order 32.

No field-action hypothesis is needed. This discharges the counting step
in GLS3, section 6.3, Sz(8) case, printed p.337; the field-action argument
must separately produce centrality from trivial action on the kernel.
-/

namespace BenderSuzuki.MatrixGroups.MultiplierFieldAction
open Subgroup Theory.GroupTheory

universe u
variable {S U : Type u}
variable [Group S] [Finite S] [IsQuasisimple S]
variable [Group U] [Finite U] [IsQuasisimple U]

/-- The actual full root-center preimage is not central in the lifted root
group of a quasisimple fourfold covering of Sz(8). -/
public theorem rootCenterPreimage_not_le_center
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hfour : Nat.card f.toMonoidHom.ker = 4) :
    ¬ rootCenterPreimage e f ≤ center (rootPreimage e f) := by
  intro hcentral
  let := rootPreimage_quotient_elementary e f
  have hbound := card_commutator_le_eight_of_central_elementary_eight_quotient
    (rootCenterPreimage e f) hcentral (rootPreimage_quotient_card e f)
  rw [rootPreimage_commutator_card e f hfour] at hbound
  omega

end BenderSuzuki.MatrixGroups.MultiplierFieldAction
