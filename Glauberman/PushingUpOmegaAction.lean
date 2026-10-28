module
public import Theory.Representation.NormalElementaryQuotient.OriginalAction
public import Glauberman.PushingUpNontrivialAction
/-!
# Conjugation on the original central omega subgroup

This is the binary action of the original H on Ω₁(Z(O₂(H))), using the
literal centralizer quotient construction. Its fixed-index and moved-space
centralizer identities feed Niles7.4 and7.6 without deleting central fixed
attachments or changing the source actor.

Source: Niles, *Pushing-up in finite groups* (1979), pp.33,60–62.
-/

public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace Glauberman
variable (H : Type*) [Group H]

/-- The literal original action on Ω₁(Z(O₂(H))). -/
noncomputable def omegaAction : Representation (ZMod 2) H
    (Additive (omegaCenterIn (pCore 2 H))) := by
  let _ := omegaCenterIn_normal_of_normal (pCore 2 H)
  exact Representation.NormalElementaryQuotient.originalAction (omegaCenterIn (pCore 2 H))

/-- The actor and vectors are the original group elements, with literal
conjugation in H. -/
theorem omegaAction_apply (h : H) (v : Additive (omegaCenterIn (pCore 2 H))) :
    ((omegaAction H h v).toMul : H) = h * (v.toMul : H) * h⁻¹ := by
  let _ := omegaCenterIn_normal_of_normal (pCore 2 H)
  exact Representation.NormalElementaryQuotient.originalAction_apply
    (omegaCenterIn (pCore 2 H)) h v

theorem omegaAction_fixedSpace (A : Subgroup H)
    (v : Additive (omegaCenterIn (pCore 2 H))) :
    v ∈ fixedSpace (omegaAction H) A ↔
      (v.toMul : H) ∈ centralizer (A : Set H) := by
  let _ := omegaCenterIn_normal_of_normal (pCore 2 H)
  exact Representation.NormalElementaryQuotient.original_fixedSpace
    (omegaCenterIn (pCore 2 H)) A v

theorem omegaAction_kernel : (omegaAction H).ker =
    centralizer (omegaCenterIn (pCore 2 H) : Set H) := by
  let _ := omegaCenterIn_normal_of_normal (pCore 2 H)
  exact Representation.NormalElementaryQuotient.originalAction_kernel (omegaCenterIn (pCore 2 H))

theorem omegaAction_fixed_index [Finite H] (A : Subgroup H) :
    (omegaCenterIn (pCore 2 H) ⊓ centralizer (A : Set H)).relIndex
        (omegaCenterIn (pCore 2 H)) = 2 ^ fixedCodim (omegaAction H) A := by
  let _ := omegaCenterIn_normal_of_normal (pCore 2 H)
  exact Representation.NormalElementaryQuotient.original_fixed_index (omegaCenterIn (pCore 2 H)) A

theorem omegaAction_moved_centralizer (L : Subgroup H) (h : H) :
    h ∈ centralizer ((⁅omegaCenterIn (pCore 2 H),L⁆ : Subgroup H) : Set H) ↔
      ∀ w ∈ subspaceCommutator (omegaAction H) ⊤ L, omegaAction H h w = w := by
  let _ := omegaCenterIn_normal_of_normal (pCore 2 H)
  exact Representation.NormalElementaryQuotient.original_moved_centralizer (omegaCenterIn (pCore 2 H)) L h
end Glauberman
