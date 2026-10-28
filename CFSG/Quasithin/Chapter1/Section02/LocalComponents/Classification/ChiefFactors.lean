module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Structure
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.CentralPChiefFactorsOddQuotient
public import Theory.GroupTheory.CentralPChiefFactorsQuotient

/-!
# The central-chief-factor input to Lemma 1.2.10

The common conclusions of A.3.6 say that F(K) is the odd core and K/F(K)
is quasisimple. The general odd-normal-quotient argument therefore makes
all two-chief factors of K central. For a C-component L of H, apply this
to the actual image of L in H/O₂(H), then transport along the canonical
isomorphism from L/O₂(L).

This supplies the chief-factor input to A.4.11 in the proof of 1.2.10.
The common A.3.6 conclusions remain explicit premises; this module does
not assert the classification providing them or the reduced-witness theorem.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.3.6,
printed pp.43–45, and the proof of 1.2.10, p.507 (1 March 2004 manuscript).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02

variable {K : Type*} [Group K] [Finite K]

/-- The odd Fitting subgroup and quasisimple quotient in the common A.3.6
conclusions imply centrality of all actual two-chief factors. -/
theorem A36Common.hasCentralTwoChiefFactors (h : A36Common K) :
    HasCentralPChiefFactors 2 K := by
  apply hasCentralTwoChiefFactors_of_odd_normal_quasisimple_quotient
    (fittingSubgroup K) _ h.2.1
  rw [h.1]
  exact pPrimeCore_coprime_card

/-- Apply the common A.3.6 conclusions to the actual quotient image of a
C-component and transport to its intrinsic two-core quotient. -/
theorem hasCentralTwoChiefFactors_cComponent_twoCore_quotient
    {H : Type*} [Group H] [Finite H] {L : Subgroup H} (hL : L.IsCComponent)
    (hc : A36Common (L.map (QuotientGroup.mk' (pCore 2 H)))) :
    HasCentralPChiefFactors 2 (L ⧸ pCore 2 L) := by
  let e := cComponentTwoCoreQuotientEquiv hL
  exact hc.hasCentralTwoChiefFactors.of_surjective e.symm.toMonoidHom e.symm.surjective

end CFSG.Quasithin.Chapter1.Section02
