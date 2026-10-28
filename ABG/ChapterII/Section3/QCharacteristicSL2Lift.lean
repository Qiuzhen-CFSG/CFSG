module
public import ABG.ChapterII.Section3.QSylowGeometry
public import ABG.ChapterII.Section3.PSL2PreimageCoverData
public import ABG.ChapterII.Section3.SL2LiftCharacteristic
public import ABG.ChapterII.Section3.CoreFreeCentralQuotient
public import ABG.ChapterII.Section3.CentralSylowDihedralQuotient
public import GorensteinWalter.NormalPSL2CoreUniquenessGeneral
public import GorensteinWalter.NormalSL2ProjectiveImage
public import GorensteinWalter.CyclicCentralSL2Cover
public import Theory.GroupTheory.PGroup.NoPrimeIndexImage

/-!
# Characteristic SL₂ lifts in core-free Q-groups

For an enlarged Q-group with trivial odd core and central Sylow center, an
actual normal PSL₂ subgroup of the quotient by that center lifts to a
characteristic SL₂ subgroup. The field has odd prime-power cardinality; the
small parameters 3 and 9 are included.

The Q-group Sylow geometry supplies a cyclic nontrivial center, a dihedral
central quotient, and the four-subgroup intersection needed for nonsplitting.
The actual preimage is therefore a nonsplit cyclic central two-cover; the
all-field cover theorem gives SL₂, characteristic in its normal preimage.
Every ambient automorphic image has the same image in the fixed central
quotient by uniqueness of normal PSL₂ cores. Equal-image uniqueness for
subgroups with no normal subgroup of index two then gives characteristicity.
The central subgroup itself need not be assumed characteristic.

This supplies the lifting step in ABG, Chapter II, Section 3, Lemma 2
(article page 24), with the characteristic refinement needed by the
characteristic-power assembly. All enlarged Q-group cases are retained.
-/

namespace ABG
open GorensteinWalter BenderSuzuki.MatrixGroups
universe u

public theorem qGroup_characteristic_sl2_of_normal_psl2
    {G : Type u} [Group G] [Finite G] (hQ : IsQGroup G)
    (hcore : pPrimeCore 2 G = ⊥) (S : Sylow 2 G)
    (N : Subgroup G) [N.Normal] (hN : N = subgroupCenter (S : Subgroup G))
    (hcentral : N ≤ Subgroup.center G)
    (F : Type u) [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    (Lbar : Subgroup (G ⧸ N)) [Lbar.Normal] (eLbar : Lbar ≃* PSL2 F) :
    ∃ L : Subgroup G, L.Characteristic ∧
      Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hCcyc, hCne, hmodel⟩ := qGroup_sylow_center_quotient_geometry hQ S
  let : Nontrivial (Subgroup.center S) := hCne
  let eN : Subgroup.center S ≃* N :=
    ((Subgroup.center S).equivMapOfInjective (S : Subgroup G).subtype
      (S : Subgroup G).subtype_injective).trans (MulEquiv.subgroupCongr hN.symm)
  have hNcyc : IsCyclic N := eN.isCyclic.mp hCcyc
  have hNne : N ≠ ⊥ := by
    intro hbot
    have hn : Nontrivial N := eN.injective.nontrivial
    have hc : 1 < Nat.card N := Finite.one_lt_card_iff_nontrivial.mpr hn
    rw [hbot, Subgroup.card_bot] at hc
    omega
  have hNtwo : IsPGroup 2 N :=
    (S.isPGroup'.to_subgroup (Subgroup.center S)).of_equiv eN
  have hquotcore : pPrimeCore 2 (G ⧸ N) = ⊥ :=
    oddCore_quotient_eq_bot_of_central_two_subgroup N hcentral hNtwo hcore
  have hdih := hasDihedralSylowTwo_quotient_sylow_center_of_model S N hN hmodel
  have hFodd : Odd (Nat.card F) := by
    obtain ⟨p, n, _, hp, _, hcard⟩ := hF
    rw [hcard]
    exact hp.pow
  have hFtwo : (2 : F) ≠ 0 := two_ne_zero_of_odd_card F hFodd
  let H := Lbar.comap (QuotientGroup.mk' N)
  let Z := N.subgroupOf H
  obtain ⟨hHN, _, hZcyc, hZne, hZc, hZtwo, ⟨eH⟩, hHns⟩ :=
    psl2_preimage_central_cover_data_of_four S
      (qGroup_four_subgroup_inf_center_ne_bot hQ S)
      N hN hcentral hNcyc hNne F hF Lbar eLbar
  let : H.Normal := hHN
  obtain ⟨L0, hL0N, ⟨eL0⟩, hgen, _⟩ :=
    Matrix.ProjectiveSpecialLinearGroup.exists_sl2_of_nonsplit_cyclic_two_central_extension
      F hF Z hZne hZcyc hZtwo hZc eH hHns
  let : L0.Normal := hL0N
  let : L0.Characteristic := sl2_central_lift_characteristic Z L0 hZc hZtwo hgen hFtwo eL0
  let L := L0.map H.subtype
  have hLN : L.Normal := ConjAct.normal_of_characteristic_of_normal
  let : L.Normal := hLN
  let eL : L ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (L0.equivMapOfInjective H.subtype H.subtype_injective).symm.trans eL0
  obtain ⟨eLq⟩ := normal_sl2_projective_image S N L hcentral hN.symm.le F hF eL
  have hLqN : (L.map (QuotientGroup.mk' N)).Normal :=
    hLN.map _ (QuotientGroup.mk'_surjective N)
  refine ⟨L, Subgroup.characteristic_iff_map_eq.mpr ?_, ⟨eL⟩⟩
  intro a
  let M := L.map a.toMonoidHom
  have hMN : M.Normal := hLN.map a.toMonoidHom a.surjective
  let : M.Normal := hMN
  let eM : M ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (L.equivMapOfInjective a.toMonoidHom a.injective).symm.trans eL
  obtain ⟨eMq⟩ := normal_sl2_projective_image S N M hcentral hN.symm.le F hF eM
  have hMqN : (M.map (QuotientGroup.mk' N)).Normal :=
    hMN.map _ (QuotientGroup.mk'_surjective N)
  have himages := (unique_normal_psl2_core_of_dihedral hdih hquotcore
    F hF _ hLqN eLq F hF _ hMqN eMq).1
  have hqker : (QuotientGroup.mk' N).ker = N := QuotientGroup.ker_mk' N
  exact Subgroup.eq_of_map_eq_of_no_normal_index_prime (QuotientGroup.mk' N)
    (hNtwo.of_equiv (MulEquiv.subgroupCongr hqker).symm) M L
    (sl2_no_normal_index_two hFtwo eM) (sl2_no_normal_index_two hFtwo eL) himages

end ABG

