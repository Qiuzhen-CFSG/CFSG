module
public import Theory.GroupTheory.CenterFreeOddImageCore

/-!
# Self-centralization of an abelian residual intersection

In a finite center-free group P, suppose normal E supplements a supplied
Sylow two-subgroup and normal Q is a two-group. If E has odd image in P/Q
and E∩Q is abelian, then Q∩C_P(E∩Q)=E∩Q. Both normality instances and the
literal quotient image are retained; no faithful action is assumed.

Set R=E∩Q and K=Q∩C_P(R). Abelianness gives R≤K and hence E∩K=R. Thus the
E images modulo Q and K have equal odd order. The commutator [K,E] lies
in R, which centralizes K, so the existing center-free odd-image collapse
gives K≤R. This exposes the kernel reduction used by the C4-square core
cardinality theorem and by the subsequent actual Section Ten core action.

Source: Stellmacher (10.1)(a), printed p.61/PDF p.51,
`refs/files/stellmacher-n-group.pdf`; the result isolates the source's
centralizer-kernel argument with its sufficient group-theoretic hypotheses.
-/

open Subgroup
open scoped IsMulCommutative

public theorem inf_centralizer_inf_eq_of_centerfree_odd_image
    {P : Type*} [Group P] [Finite P]
    (S : Sylow 2 P) (E Q : Subgroup P) [E.Normal] [Q.Normal]
    (hcover : E ⊔ (S : Subgroup P) = ⊤) (hQ : IsPGroup 2 Q)
    (hcenter : center P = ⊥) [IsMulCommutative (E ⊓ Q : Subgroup P)]
    (hodd : Odd (Nat.card (E.map (QuotientGroup.mk' Q)))) :
    Q ⊓ centralizer (E ⊓ Q : Set P) = E ⊓ Q := by
  let R := E ⊓ Q
  let K := Q ⊓ centralizer (R : Set P)
  have hRK : R ≤ K := le_inf inf_le_right (le_centralizer R)
  have hEK : E ⊓ K = R := by
    apply le_antisymm
    · exact le_inf inf_le_left (inf_le_right.trans inf_le_left)
    · exact le_inf inf_le_left hRK
  have hKcard : Nat.card (E.map (QuotientGroup.mk' K)) =
      Nat.card (E.map (QuotientGroup.mk' Q)) := by
    rw [← relIndex_ker, QuotientGroup.ker_mk', ← inf_relIndex_left E K, hEK]
    dsimp [R]
    rw [inf_relIndex_left]
    simpa only [QuotientGroup.ker_mk'] using (relIndex_ker E (QuotientGroup.mk' Q))
  have hKle : K ≤ R := le_of_centerfree_odd_image_commutator_le
    S E K R hcover (hQ.to_le inf_le_left) (hKcard.symm ▸ hodd) hcenter
    (le_centralizer_iff.mp inf_le_right)
    ((commutator_le_inf K E).trans (by rw [inf_comm, hEK]))
  exact le_antisymm hKle hRK

