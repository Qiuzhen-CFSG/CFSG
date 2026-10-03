module
public import Stellmacher.SectionFiveToSeven.SixFourSubnormalTransfer
public import Stellmacher.SectionThree.OmegaNormalClosureElementary

/-!
# Centralizing the omega normal closure in a normal container

In the central branch of Hypothesis Two, let K <= P2 satisfy K=[K,B(S)].
Suppose the two-local overgroup U contains B(S) and K, and Q is normal in
U, lies in S, and contains both Omega1(Z(S)) and O2(K). Then K centralizes
the U-normal closure of Omega1(Z(S)), viewed in the original ambient group.

The Section Three normal-container theorem puts that closure inside
Omega1(Z(Q)) and proves it elementary abelian. Consequently it centralizes
O2(K), and the repeated subnormal transfer applies. This also centralizes
the commutator [Omega1(Z(S)),F] for every F <= U, without presupposing that
this smaller commutator is normal in U.

This is the first commutator paragraph of Stellmacher (6.4), Journal of
Algebra 190 (1997), p.32, after (5.4) and the common-core normalizer
consequence of (3.8) produce Q=T intersect O2(U).
Source: `refs/files/stellmacher-n-group.pdf` and
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

public theorem sixFour_normal_container_transfer
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (hcomm : ⁅P2, omegaOneCenter S⁆ = ⊥)
    (K : Subgroup H) (hKP : K ≤ P2) (hKB : K = ⁅K, baumannIn S⁆)
    (U : Subgroup H) (hU : IsTwoLocal U) (hBU : baumannIn S ⊔ K ≤ U)
    (Q : Subgroup H) (hQU : Q ≤ U) (hQS : Q ≤ S)
    (hQn : (Q.subgroupOf U).Normal) (hZQ : omegaOneCenter S ≤ Q)
    (hKQ : twoCoreAmbient K ≤ Q) :
    ⁅(Subgroup.normalClosure ((omegaOneCenter S).subgroupOf U : Set U)).map U.subtype, K⁆ = ⊥ := by
  let A0 := Subgroup.normalClosure ((omegaOneCenter S).subgroupOf U : Set U)
  let A := A0.map U.subtype
  let _ : IsElementaryAbelian 2 A0 :=
    SectionThree.omegaOneCenter_normalClosure_isElementaryAbelian S U Q hQU hQS hQn hZQ
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : IsElementaryAbelian 2 A := IsElementaryAbelian.map U.subtype
  have hAn : (A.subgroupOf U).Normal := by
    rw [show A = A0.map U.subtype from rfl, subgroupOf_map_subtype_eq]
    exact Subgroup.normalClosure_normal
  have hAomega : A ≤ omegaOneCenterAmbient Q := by
    have hm := Subgroup.map_mono (f := U.subtype)
      (SectionThree.omegaOneCenter_normalClosure_le_containerOmega S U Q hQU hQS hQn hZQ)
    rw [← omegaOneCenterAmbient_map_injective U.subtype U.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hQU] at hm
    exact hm
  have hAQ : A ≤ Subgroup.centralizer (Q : Set H) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    exact (mem_omegaOneCenterAmbient_iff Q a).mp (hAomega ha) |>.2.2
  have hcore : ⁅A, twoCoreAmbient K⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hAQ.trans (Subgroup.centralizer_le hKQ))
  exact sixFour_subnormal_transfer h hcomm K hKP hKB U hU hBU A
    (Subgroup.map_subtype_le _) hAn hcore

end Stellmacher.SectionsFiveToSeven
