module

public import Stellmacher.SectionFour.NormalSupplement
public import Stellmacher.SectionFour.PartnerCentralizerSylow
public import Stellmacher.SectionTwo.NormalSupplementCore
public import Stellmacher.SectionTwo.LemmaTwoOne

/-!
# The actual hypotheses for (2.3) in Stellmacher (4.6)

For the residual-core product `E = O²(Pstar)O₂(C)` in the proved
Baumann configuration, this module constructs a Sylow subgroup of the
native group `E.subgroupOf Pstar` whose image is `O₂(C)`, together
with all standing Section Two hypotheses and the exact extra core
equality required by (2.3).

The normal-supplement data supplies solvability, even order,
characteristic 2, and compatible native Sylow witnesses. Injective
omega-center transport identifies the fixed Sylow's central involutions
with the original Section Four subgroup. Critical-partner centralizer
control therefore applies to the same normal closure. The normal-supplement
core criterion then gives `O₂(E)=C_Q(vSubgroup Q)`.

Source: `refs/latex/stellmacher-n-group.tex`, the application of (2.3)
in the second paragraph of (4.6). This module isolates input verification
from the subsequent application of (2.3).
-/

open scoped Pointwise

namespace Stellmacher.SectionFour

/-- The native local group in the Baumann configuration satisfies all
hypotheses of (2.3), with the prescribed Sylow image. -/
public theorem baumann_two_three_hypotheses
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (heven : Even (Nat.card G))
    (P Pstar E : Subgroup G) (hpair : (P, Pstar) ∈ Lambda S)
    (hPC : P ≤ cSubgroup S) (hEP : E ≤ Pstar)
    (hsolv : Group.IsSolvable Pstar) (hchar : IsCharacteristicTwoType Pstar)
    (hE : (E : Set G) = (twoResidualAmbient Pstar : Set G) *
      (twoCoreAmbient (cSubgroup S) : Set G))
    (hSyl : IsSylowSubgroupIn (twoCoreAmbient (cSubgroup S)) E) :
    ∃ Q : Sylow 2 (E.subgroupOf Pstar),
      SectionTwo.Hypotheses (E.subgroupOf Pstar) ∧
      (((Q : Subgroup (E.subgroupOf Pstar)).map (E.subgroupOf Pstar).subtype).map
        Pstar.subtype) = twoCoreAmbient (cSubgroup S) ∧
      pCore 2 (E.subgroupOf Pstar) = (Q : Subgroup (E.subgroupOf Pstar)) ⊓
        Subgroup.centralizer (SectionTwo.vSubgroup Q : Set (E.subgroupOf Pstar)) := by
  obtain ⟨hEN, hsolvE, hcharE, hevenE, SP, Q, hSP, hQm, hgen, hQS, hZQ, hSN⟩ :=
    baumann_normal_supplement_data S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  let _ : (E.subgroupOf Pstar).Normal := hEN
  have hSylCent := partner_normal_centralizer_sylow S heven P Pstar hpair hPC hsolv
    (E.subgroupOf Pstar)
  have hZP : zSubgroup S ≤ Pstar := by
    intro z hz
    have hzS := ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
    rw [← hSP] at hzS
    exact (Subgroup.map_subtype_le _) hzS
  have hZnative : SectionTwo.zSubgroup SP = (zSubgroup S).subgroupOf Pstar := by
    apply Subgroup.map_injective Pstar.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hZP]
    change (omegaOneCenterAmbient (SP : Subgroup Pstar)).map Pstar.subtype = zSubgroup S
    rw [← omegaOneCenterAmbient_map_injective Pstar.subtype Pstar.subtype_injective, hSP]
    rfl
  have hVnative : SectionTwo.vSubgroup SP =
      Subgroup.normalClosure ((zSubgroup S).subgroupOf Pstar : Set Pstar) := by
    change Subgroup.normalClosure (SectionTwo.zSubgroup SP : Set Pstar) = _
    rw [hZnative]
  change ∃ T : Sylow 2 ((Subgroup.centralizer
      (Subgroup.normalClosure ((zSubgroup S).subgroupOf Pstar : Set Pstar) : Set Pstar)).subgroupOf
        (E.subgroupOf Pstar)), _ at hSylCent
  rw [← hVnative] at hSylCent
  refine ⟨Q, ⟨hsolvE, hevenE, hcharE⟩, hQm, ?_⟩
  exact SectionTwo.normal_supplement_core_centralizer (E.subgroupOf Pstar) SP Q
    hgen hQS hZQ hSN hSylCent

end Stellmacher.SectionFour
