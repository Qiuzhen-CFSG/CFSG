module
public import Stellmacher.SectionFour.BaumannSylow

/-!
# The original Section Four module lies in the core Sylow

In the critical-partner setup of Stellmacher (4.6), let `Z = Ω₁(Z(S))` for
the original Sylow subgroup `S`, and let `V` be the image of the normal
closure of `Z.subgroupOf Pstar` inside `Pstar`. This module proves
the stronger containment in the Baumann subgroup of `O₂(C)`, and hence
`V ≤ O₂(C)`, for `C = cSubgroup S`, using the prescribed residual-core
product and its Sylow hypothesis. The supporting public theorem identifies
the original `V` with the Section Two module of a Sylow of `Pstar` whose
ambient image is exactly the original `S`.

The normal-supplement data puts `Z` inside `Q = O₂(C) ≤ S`. Since `Z`
centralizes `S`, it lies in the Baumann subgroup `B₀` of `Q`. Taking normal
closures inside `Pstar` therefore gives `V ≤ L = ⟨B₀^Pstar⟩`. The native
Section Two hypotheses and the transported original Sylow show that `V` is
a 2-group; its defining normal closure makes it normal in `Pstar`, hence
normal in `L`. The accepted Baumann Sylow theorem now places this normal
2-subgroup in `B₀`, and `B₀ ≤ Q` proves the containment.

The two Sylow subgroups have distinct roles: the original Sylow defines
`V`, while the core Sylow controls its containment via the Baumann theorem.
Source: B. Stellmacher, *2-Local structure of N-groups*, Journal of Algebra
190 (1997), proof of (4.6), p.26; `refs/latex/stellmacher-n-group.tex`.
-/

open scoped Pointwise
namespace Stellmacher.SectionFour

private theorem original_partner_data_with_center
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (heven : Even (Nat.card G))
    (P Pstar E : Subgroup G) (hpair : (P, Pstar) ∈ Lambda S)
    (hPC : P ≤ cSubgroup S) (hEP : E ≤ Pstar)
    (hsolv : Group.IsSolvable Pstar) (hchar : IsCharacteristicTwoType Pstar)
    (hE : (E : Set G) = (twoResidualAmbient Pstar : Set G) *
      (twoCoreAmbient (cSubgroup S) : Set G))
    (hSyl : IsSylowSubgroupIn (twoCoreAmbient (cSubgroup S)) E) :
    ∃ SP : Sylow 2 Pstar,
      SectionTwo.Hypotheses Pstar ∧
      (SP : Subgroup Pstar).map Pstar.subtype = (S : Subgroup G) ∧
      SectionTwo.vSubgroup SP =
        Subgroup.normalClosure ((zSubgroup S).subgroupOf Pstar : Set Pstar) ∧
      zSubgroup S ≤ twoCoreAmbient (cSubgroup S) ∧
      twoCoreAmbient (cSubgroup S) ≤ (S : Subgroup G) := by
  obtain ⟨_, _, _, hevenE, SP, QE, hSP, hQmap, _, hQS, hZQ, _⟩ :=
    baumann_normal_supplement_data S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  have hevenPstar : Even (Nat.card Pstar) := even_iff_two_dvd.mpr
    (hevenE.two_dvd.trans (Subgroup.card_subgroup_dvd_card (E.subgroupOf Pstar)))
  have hsec : SectionTwo.Hypotheses Pstar := ⟨hsolv, hevenPstar, hchar⟩
  have hSlePstar : (S : Subgroup G) ≤ Pstar := hSP ▸ Subgroup.map_subtype_le _
  have hZPstar : zSubgroup S ≤ Pstar := fun z hz =>
    hSlePstar ((mem_omegaOneCenterAmbient_iff _ z).mp hz).1
  have hZmap : (SectionTwo.zSubgroup SP).map Pstar.subtype = zSubgroup S := by
    change (omegaOneCenterAmbient (SP : Subgroup Pstar)).map Pstar.subtype = zSubgroup S
    rw [← omegaOneCenterAmbient_map_injective Pstar.subtype Pstar.subtype_injective, hSP]
    rfl
  have hZnative : SectionTwo.zSubgroup SP = (zSubgroup S).subgroupOf Pstar := by
    apply Subgroup.map_injective Pstar.subtype_injective
    rw [hZmap, Subgroup.map_subgroupOf_eq_of_le hZPstar]
  have hVnative : SectionTwo.vSubgroup SP =
      Subgroup.normalClosure ((zSubgroup S).subgroupOf Pstar : Set Pstar) := by
    change Subgroup.normalClosure (SectionTwo.zSubgroup SP : Set Pstar) = _
    rw [hZnative]
  have hZQambient := Subgroup.map_mono (f := Pstar.subtype) hZQ
  rw [hZmap, hQmap] at hZQambient
  have hQSambient := Subgroup.map_mono (f := Pstar.subtype) hQS
  rw [hQmap, hSP] at hQSambient
  exact ⟨SP, hsec, hSP, hVnative, hZQambient, hQSambient⟩

/-- The native partner Sylow preserves the original Section Four module. -/
public theorem original_partner_sectionTwo_data
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (heven : Even (Nat.card G))
    (P Pstar E : Subgroup G) (hpair : (P, Pstar) ∈ Lambda S)
    (hPC : P ≤ cSubgroup S) (hEP : E ≤ Pstar)
    (hsolv : Group.IsSolvable Pstar) (hchar : IsCharacteristicTwoType Pstar)
    (hE : (E : Set G) = (twoResidualAmbient Pstar : Set G) *
      (twoCoreAmbient (cSubgroup S) : Set G))
    (hSyl : IsSylowSubgroupIn (twoCoreAmbient (cSubgroup S)) E) :
    ∃ SP : Sylow 2 Pstar,
      SectionTwo.Hypotheses Pstar ∧
      (SP : Subgroup Pstar).map Pstar.subtype = (S : Subgroup G) ∧
      SectionTwo.vSubgroup SP =
        Subgroup.normalClosure ((zSubgroup S).subgroupOf Pstar : Set Pstar) := by
  obtain ⟨SP, hsec, hSP, hV, _, _⟩ :=
    original_partner_data_with_center S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  exact ⟨SP, hsec, hSP, hV⟩

/-- The original partner-normal closure lies in the Baumann subgroup of `O₂(C)`. -/
public theorem original_v_le_baumann
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (heven : Even (Nat.card G))
    (P Pstar E : Subgroup G) (hpair : (P, Pstar) ∈ Lambda S)
    (hPC : P ≤ cSubgroup S) (hEP : E ≤ Pstar)
    (hsolv : Group.IsSolvable Pstar) (hchar : IsCharacteristicTwoType Pstar)
    (hE : (E : Set G) = (twoResidualAmbient Pstar : Set G) *
      (twoCoreAmbient (cSubgroup S) : Set G))
    (hSyl : IsSylowSubgroupIn (twoCoreAmbient (cSubgroup S)) E) :
    (Subgroup.normalClosure ((zSubgroup S).subgroupOf Pstar : Set Pstar)).map
      Pstar.subtype ≤ twoCoreAmbient (cSubgroup S) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (twoCoreAmbient (cSubgroup S))) : Set G) := by
  obtain ⟨SP, hsec, _hSP, hVnative, hZQ, hQS⟩ :=
    original_partner_data_with_center S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  let Q := twoCoreAmbient (cSubgroup S)
  let B := Q ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set G)
  let VN := Subgroup.normalClosure ((zSubgroup S).subgroupOf Pstar : Set Pstar)
  let V := VN.map Pstar.subtype
  let LN := Subgroup.normalClosure (B.subgroupOf Pstar : Set Pstar)
  let L := LN.map Pstar.subtype
  have hZB : zSubgroup S ≤ B := by
    refine le_inf hZQ ?_
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwJ : w ∈ elementaryAbelianMaxJ Q :=
      (mem_omegaOneCenterAmbient_iff _ w).mp hw |>.1
    have hJQ : elementaryAbelianMaxJ Q ≤ Q := sSup_le fun _ hA => hA.1
    have hwQ : w ∈ Q := hJQ hwJ
    exact (mem_omegaOneCenterAmbient_iff _ z).mp hz |>.2.2 w (hQS hwQ)
  have hVNLN : VN ≤ LN := by
    apply Subgroup.normalClosure_le_normal
    intro z hz
    exact Subgroup.le_normalClosure (hZB hz)
  have hVL : V ≤ L := Subgroup.map_mono hVNLN
  have hVPstar : V ≤ Pstar := Subgroup.map_subtype_le _
  have hLPstar : L ≤ Pstar := Subgroup.map_subtype_le _
  have hVNnormal : (V.subgroupOf Pstar).Normal := by
    rw [show V = VN.map Pstar.subtype from rfl, subgroupOf_map_subtype_eq]
    exact (inferInstance : VN.Normal)
  have hPnormV : Pstar ≤ Subgroup.normalizer V :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVPstar).mp hVNnormal
  let _ : (V.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVL).mpr (hLPstar.trans hPnormV)
  have hVNp : IsPGroup 2 VN := by
    change IsPGroup 2 (Subgroup.normalClosure ((zSubgroup S).subgroupOf Pstar : Set Pstar))
    rw [← hVnative]
    exact (SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian hsec SP).2.isPGroup
  have hVp : IsPGroup 2 V := hVNp.map Pstar.subtype
  have hVpL : IsPGroup 2 (V.subgroupOf L) :=
    hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVL).symm
  obtain ⟨TB, hTB⟩ :=
    baumann_isSylow_normalClosure S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  change (TB : Subgroup L).map L.subtype = B at hTB
  have hVleB : V ≤ B := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hVL, ← hTB]
    exact Subgroup.map_mono (hVpL.le_sylow_of_normal TB)
  exact hVleB

/-- The original module lies in the local core, via its Baumann subgroup. -/
public theorem original_v_le_c_core
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (heven : Even (Nat.card G))
    (P Pstar E : Subgroup G) (hpair : (P, Pstar) ∈ Lambda S)
    (hPC : P ≤ cSubgroup S) (hEP : E ≤ Pstar)
    (hsolv : Group.IsSolvable Pstar) (hchar : IsCharacteristicTwoType Pstar)
    (hE : (E : Set G) = (twoResidualAmbient Pstar : Set G) *
      (twoCoreAmbient (cSubgroup S) : Set G))
    (hSyl : IsSylowSubgroupIn (twoCoreAmbient (cSubgroup S)) E) :
    (Subgroup.normalClosure ((zSubgroup S).subgroupOf Pstar : Set Pstar)).map
      Pstar.subtype ≤ twoCoreAmbient (cSubgroup S) := by
  exact (original_v_le_baumann S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl).trans
    inf_le_left

end Stellmacher.SectionFour
