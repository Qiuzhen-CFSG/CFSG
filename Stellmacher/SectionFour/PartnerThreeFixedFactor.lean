module
public import Stellmacher.SectionFour.BaumannFactorDecomposition
public import Stellmacher.SectionFour.BaumannFixedFactorTrivial

/-!
# Vanishing of the original module's Sylow-three fixed factor

For the critical-partner Baumann configuration, the original module
V=⟨Ω₁(Z(S))^Pstar⟩ has trivial intersection with the centralizer of every
Sylow three-subgroup of Pstar. The theorem preserves the supplied Sylow
and the original module, without choosing a new module from O₂(C).

The exact native partner Sylow identifies this V with its Section Two
module. The normal-supplement decomposition's companion retains the raw
one-seven factor action: a Sylow-three fixed vector is fixed by every
factor's derived C3, hence by each full SL₂(2) factor and by the L-image.
The quotient-conjugation computation then transports this vector into the
actual fixed factor V∩C_Pstar(L), already proved trivial by the critical pair.
Only factor generation and fixed-space control are used; no module product
cardinality or stronger independence assertion is required.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (4.6), p26,
Sylow-three paragraph; `refs/latex/stellmacher-n-group.tex`.
-/

open scoped Pointwise
namespace Stellmacher.SectionFour

private theorem actual_fixed_le_of_quotient_fixed_le
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (S : Sylow 2 G) (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = SectionTwo.cSubgroup S) (T : Sylow 3 G) (L : Subgroup G)
    (hfix : let _ := SectionTwo.quotientConjugationAction S q hq hker
      FixedPoints.subgroup (T.mapSurjective hq) (SectionTwo.vSubgroup S) ≤
        FixedPoints.subgroup (L.map q) (SectionTwo.vSubgroup S)) :
    SectionTwo.vSubgroup S ⊓ Subgroup.centralizer (T : Set G) ≤
      SectionTwo.vSubgroup S ⊓ Subgroup.centralizer (L : Set G) := by
  let _ := SectionTwo.quotientConjugationAction S q hq hker
  rintro x ⟨hxV,hxT⟩
  change x ∈ Subgroup.centralizer (T : Set G) at hxT
  let v : SectionTwo.vSubgroup S := ⟨x,hxV⟩
  have hv : v ∈ FixedPoints.subgroup (T.mapSurjective hq) (SectionTwo.vSubgroup S) := by
    rw [FixedPoints.mem_subgroup]
    intro tbar
    obtain ⟨t,ht,heq⟩ := tbar.property
    change (tbar : H) • v = v
    rw [← heq]
    apply Subtype.ext
    change ((q t • v : SectionTwo.vSubgroup S) : G) = x
    rw [SectionTwo.quotientConjugationAction_smul_coe S q hq hker]
    rw [Subgroup.mem_centralizer_iff] at hxT
    rw [hxT t ht, mul_inv_cancel_right]
  have hvL := hfix hv
  refine ⟨hxV,Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
  have hh := congrArg Subtype.val (hvL ⟨q l, Subgroup.mem_map_of_mem q hl⟩)
  change ((q l • v : SectionTwo.vSubgroup S) : G) = x at hh
  rw [SectionTwo.quotientConjugationAction_smul_coe S q hq hker] at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

/-- Every native Sylow-three subgroup has trivial fixed factor in the original V. -/
public theorem partner_sylow_three_fixed_factor_eq_bot
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (heven : Even (Nat.card G))
    (P Pstar E : Subgroup G) (hpair : (P, Pstar) ∈ Lambda S)
    (hPC : P ≤ cSubgroup S) (hEP : E ≤ Pstar)
    (hsolv : Group.IsSolvable Pstar) (hchar : IsCharacteristicTwoType Pstar)
    (hE : (E : Set G) = (twoResidualAmbient Pstar : Set G) *
      (twoCoreAmbient (cSubgroup S) : Set G))
    (hSyl : IsSylowSubgroupIn (twoCoreAmbient (cSubgroup S)) E)
    (T : Sylow 3 Pstar) :
    Subgroup.normalClosure ((zSubgroup S).subgroupOf Pstar : Set Pstar) ⊓
      Subgroup.centralizer (T : Set Pstar) = ⊥ := by
  obtain ⟨SP, hsec, hSPmap, hV⟩ :=
    original_partner_sectionTwo_data S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  obtain ⟨hEN, _, _, _, SP', Q, hSP'map, hQmap, hgen, _, _, hSN⟩ :=
    baumann_normal_supplement_data S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  let N := E.subgroupOf Pstar
  let _ : N.Normal := hEN
  let B := twoCoreAmbient (cSubgroup S) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (twoCoreAmbient (cSubgroup S))) : Set G)
  let L := Subgroup.normalClosure (B.subgroupOf Pstar : Set Pstar)
  let V := Subgroup.normalClosure ((zSubgroup S).subgroupOf Pstar : Set Pstar)
  let C := Subgroup.centralizer (V : Set Pstar)
  let _ : V.Normal := Subgroup.normalClosure_normal
  let _ : C.Normal := inferInstance
  let q : Pstar →* Pstar ⧸ C := QuotientGroup.mk' C
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective C
  have hker : q.ker = SectionTwo.cSubgroup SP := by
    rw [QuotientGroup.ker_mk']
    change Subgroup.centralizer (V : Set Pstar) =
      Subgroup.centralizer (SectionTwo.vSubgroup SP : Set Pstar)
    rw [hV]
  have hSP : (SP : Subgroup Pstar) = (SP' : Subgroup Pstar) := by
    apply Subgroup.map_injective Pstar.subtype_injective
    exact hSPmap.trans hSP'map.symm
  have hgen' : N ⊔ (SP : Subgroup Pstar) = ⊤ := by
    rw [hSP]
    exact hgen
  have hSN' : (SP : Subgroup Pstar) ≤
      Subgroup.normalizer (((Q : Subgroup N).map N.subtype : Subgroup Pstar) : Set Pstar) := by
    rw [hSP]
    exact hSN
  have hVQ : SectionTwo.vSubgroup SP ≤ (Q : Subgroup N).map N.subtype := by
    apply (Subgroup.map_le_map_iff_of_injective Pstar.subtype_injective).mp
    rw [hV, hQmap]
    exact original_v_le_c_core S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  let BN := (Q : Subgroup N).map N.subtype ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient
      (elementaryAbelianMaxJ ((Q : Subgroup N).map N.subtype)) : Set Pstar)
  have hBNmap : BN.map Pstar.subtype = B := by
    rw [baumann_map_injective Pstar.subtype Pstar.subtype_injective, hQmap]
  have hBP : B ≤ Pstar := by
    rw [← hBNmap]
    exact Subgroup.map_subtype_le _
  have hBsub : B.subgroupOf Pstar = BN := by
    apply Subgroup.map_injective Pstar.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hBP, hBNmap]
  have hdata := SectionTwo.normal_supplement_baumann_decomposition_with_three_fixed
    hsec SP q hq hker N Q hgen' hSN' hVQ
  have hfix := hdata.2 (T.mapSurjective hq)
  have hh := actual_fixed_le_of_quotient_fixed_le SP q hq hker T
    (Subgroup.normalClosure (BN : Set Pstar)) hfix
  rw [hV, ← hBsub] at hh
  have hfixed := baumann_fixed_factor_eq_bot S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  change V ⊓ Subgroup.centralizer (L : Set Pstar) = ⊥ at hfixed
  exact le_bot_iff.mp (hh.trans_eq hfixed)

end Stellmacher.SectionFour
