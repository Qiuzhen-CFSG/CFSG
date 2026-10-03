module
public import Stellmacher.SectionFour.PartnerCoreResidual
public import Stellmacher.SectionFour.PartnerThreeFixedFactor
public import Stellmacher.SectionFour.PartnerThreeCoreJoin
public import Stellmacher.SectionFour.CentralFactorTrivial
public import Theory.GroupTheory.CoprimeCentralizerNormalComplement
public import Stellmacher.SectionThree.SolvablePrimitiveTwoLocal.Residual

/-!
# Identification of the partner two-core in Stellmacher (4.6)

For the critical-partner Baumann configuration, the two-core of Pstar is
exactly the original module V=⟨Ω₁(Z(S))^Pstar⟩. The finite ambient group,
critical pair, residual-core product and its prescribed Sylow are retained.
This supplies the source's core identification before its automorphism and
Hall-orbit arguments.

Choose a native Sylow three-subgroup T. The proved factor-action result
makes V∩C(T) trivial; the source (3.3) argument makes O₂(Pstar)T normal.
The two-core Q centralizes V because its normal centralizer contains the
central involutions of the original native Sylow. Coprime action, together
with [Q,O²(Pstar)]≤V, gives Q=V∨C_Q(T).

Frattini's argument becomes Pstar=V N(T), so C_Q(T) is normal in Pstar.
Its commutator with O²(Pstar) lies in both V and C_Q(T), hence vanishes.
Mapping to the original ambient group, the critical central-factor theorem
with the residual supplement forces C_Q(T)=1. Thus Q=V. The normality step
is supplied by the independent coprime centralizer-complement theorem,
not inferred from the Frattini formula without its centrality hypothesis.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (4.6), p26,
Sylow-three paragraph; `refs/latex/stellmacher-n-group.tex`.
-/

open scoped Pointwise
namespace Stellmacher.SectionFour

private theorem sylow_three_le_residual
    {G : Type*} [Group G] [Finite G] (T : Sylow 3 G) :
    (T : Subgroup G) ≤ twoResidualAmbient (⊤ : Subgroup G) := by
  rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual]
  let R := BenderSuzuki.External.hktPResidual 2 G
  let _ : R.Normal := BenderSuzuki.External.hktPResidual_normal
  let q := QuotientGroup.mk' R
  have hquot : IsPGroup 2 (G ⧸ R) := BenderSuzuki.External.hktPResidual_quotient_isPGroup
  have himg : (T : Subgroup G).map q = ⊥ := disjoint_self.mp
    (IsPGroup.disjoint_of_ne 3 2 (by decide) _ _
      (T.isPGroup'.map q) (hquot.to_subgroup _))
  have hle := (Subgroup.map_eq_bot_iff (T : Subgroup G)).mp himg
  simpa only [q,QuotientGroup.ker_mk'] using hle

/-- The partner two-core is exactly the normal closure of the original central involutions. -/
public theorem partner_core_eq_v
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (heven : Even (Nat.card G))
    (P Pstar E : Subgroup G) (hpair : (P, Pstar) ∈ Lambda S)
    (hPC : P ≤ cSubgroup S) (hEP : E ≤ Pstar)
    (hsolv : Group.IsSolvable Pstar) (hchar : IsCharacteristicTwoType Pstar)
    (hE : (E : Set G) = (twoResidualAmbient Pstar : Set G) *
      (twoCoreAmbient (cSubgroup S) : Set G))
    (hSyl : IsSylowSubgroupIn (twoCoreAmbient (cSubgroup S)) E) :
    pCore 2 Pstar = Subgroup.normalClosure ((zSubgroup S).subgroupOf Pstar : Set Pstar) := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Group.IsSolvable Pstar := hsolv
  let T : Sylow 3 Pstar := Classical.choice Sylow.nonempty
  let Q := pCore 2 Pstar
  let V := Subgroup.normalClosure ((zSubgroup S).subgroupOf Pstar : Set Pstar)
  let R := twoResidualAmbient (⊤ : Subgroup Pstar)
  let _ : V.Normal := Subgroup.normalClosure_normal
  obtain ⟨SP,hsec,hSP,hV⟩ :=
    original_partner_sectionTwo_data S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  have hVQ : V ≤ Q := by
    change SectionTwo.vSubgroup SP = V at hV
    rw [← hV]
    exact (SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian hsec SP).1
  have hQS : Q ≤ (SP : Subgroup Pstar) := fitting_pCore_le_sylow SP
  have hVcent : V ≤ Subgroup.centralizer (Q : Set Pstar) := by
    change SectionTwo.vSubgroup SP = V at hV
    rw [← hV]
    apply Subgroup.normalClosure_le_normal
    intro z hz
    obtain ⟨zS,⟨zC,_hz,rfl⟩,rfl⟩ := hz
    change ((zC : SP) : Pstar) ∈ Subgroup.centralizer (Q : Set Pstar)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg (fun s : SP => (s : Pstar))
      ((Subgroup.mem_center_iff.mp zC.property) ⟨w,hQS hw⟩)
  have hcop : Nat.Coprime (Nat.card T) (Nat.card Q) := by
    obtain ⟨a,ha⟩ := T.isPGroup'.exists_card_eq
    obtain ⟨b,hb⟩ := (pCore_isPGroup (p := 2) (G := Pstar)).exists_card_eq
    rw [ha,hb]
    exact (show Nat.Coprime 3 2 by decide).pow a b
  have hQR : ⁅Q,R⁆ ≤ V :=
    partner_core_residual_le_v S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  obtain ⟨hQdecomp,hWnormal,hWcentR⟩ := Subgroup.coprime_centralizer_normal_complement
    T Q V R hVQ hVcent inferInstance hcop (partner_core_sup_sylow_three_normal S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl T) (sylow_three_le_residual T) hQR (partner_sylow_three_fixed_factor_eq_bot S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl T)
  let W := Q ⊓ Subgroup.centralizer (T : Set Pstar)
  let WA := W.map Pstar.subtype
  have hWA : WA ≤ Pstar := Subgroup.map_subtype_le _
  have hSPstar : (S : Subgroup G) ≤ Pstar := hSP ▸ Subgroup.map_subtype_le _
  have hWP : (WA.subgroupOf Pstar).Normal := by
    rw [show WA = W.map Pstar.subtype from rfl, subgroupOf_map_subtype_eq]
    exact hWnormal
  have hSW : (S : Subgroup G) ≤ Subgroup.normalizer (WA : Set G) := hSPstar.trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hWA).mp hWP)
  have hWS : WA ≤ (S : Subgroup G) := by
    rw [← hSP]
    exact Subgroup.map_mono (inf_le_left.trans hQS)
  have hRW : R.map Pstar.subtype ≤ Subgroup.centralizer (WA : Set G) := by
    rintro r ⟨r,hr,rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro w ⟨w,hw,rfl⟩
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp ((Subgroup.le_centralizer_iff.mp hWcentR) hr) w hw)
  have hgen : Pstar ≤ R.map Pstar.subtype ⊔ (S : Subgroup G) := by
    have hm := congrArg (Subgroup.map Pstar.subtype) (twoResidualAmbient_top_sup_sylow SP)
    rw [Subgroup.map_sup,hSP,← MonoidHom.range_eq_map,Subgroup.range_subtype] at hm
    exact hm.ge
  have hWAbot := critical_pair_central_factor_eq_bot S P Pstar (R.map Pstar.subtype) WA
    hpair hPC hWS hSW hRW hgen
  have hWbot : W = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective W Pstar.subtype_injective).mp hWAbot
  change Q = V
  change Q = V ⊔ W at hQdecomp
  simpa only [hWbot,sup_bot_eq] using hQdecomp

end Stellmacher.SectionFour
