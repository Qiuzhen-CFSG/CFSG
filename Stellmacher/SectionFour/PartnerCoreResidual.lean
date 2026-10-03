module
public import Theory.GroupTheory.SylowImageIntersection
public import Stellmacher.SectionFour.BaumannClosureGeneration
public import Stellmacher.SectionFour.BaumannFactorDecomposition
public import Stellmacher.SectionFour.BaumannFixedFactorTrivial
public import Stellmacher.SectionFour.BaumannFactorCharacteristicObstruction
public import Stellmacher.SectionTwo.PrescribedModuleCoreBound
public import Stellmacher.UniqueMaximalContainingTransport

/-!
# The actual partner core-residual bound in Stellmacher (4.6)

Retain the critical-partner Baumann configuration and the original module
V=⟨Ω₁(Z(S))^Pstar⟩. The commutator [O₂(Pstar),O²(Pstar)] lies in V.
This supplies the containment needed before the source's Sylow-three
commutator equality and subsequent core factorization.

The literal Baumann subgroup B of O₂(C) is Sylow in its normal closure L,
contains V, and satisfies LS=Pstar. The quotient Pstar/C_Pstar(V) has the
proved factor decomposition for this same L and V. Its B-image is nontrivial:
otherwise L centralizes V, contradicting the vanishing fixed factor and
the nontriviality of the original Sylow's central involutions.

Injective subtype transport gives exact native Sylow witnesses, and the
partner's family membership gives native unique maximality above S.
The prescribed-module core bound chooses a generating SL₂(2) coordinate,
uses the critical pair's characteristic obstruction for that exact local
Sylow, applies the normal-module pushing-up bound there, and transfers it
through the Hall residual argument. No characteristic obstruction for the
whole Sylow in Pstar is assumed, and no newly defined module replaces V.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (4.6), p26,
application of (2.4); `refs/latex/stellmacher-n-group.tex`.
-/

open scoped Pointwise
namespace Stellmacher.SectionFour


private theorem native_sylow_of_ambient
    {G : Type*} [Group G] [Finite G]
    (P : Subgroup G) (L : Subgroup P) (B : Subgroup G)
    (hBP : B ≤ P) (h : IsSylowSubgroupIn B (L.map P.subtype)) :
    ∃ T : Sylow 2 L, T.map L.subtype = B.subgroupOf P := by
  obtain ⟨U, hU⟩ := h
  let e : L ≃* L.map P.subtype := L.equivMapOfInjective P.subtype P.subtype_injective
  let T := U.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  refine ⟨T, ?_⟩
  apply Subgroup.map_injective P.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hBP]
  change (((U : Subgroup (L.map P.subtype)).map e.symm.toMonoidHom).map
    L.subtype).map P.subtype = B
  rw [Subgroup.map_map, Subgroup.map_map]
  have hf : (P.subtype.comp L.subtype).comp e.symm.toMonoidHom = (L.map P.subtype).subtype := by
    ext x
    have he := Subgroup.coe_equivMapOfInjective_apply L P.subtype P.subtype_injective (e.symm x)
    change ((e (e.symm x) : L.map P.subtype) : G) = (((e.symm x : L) : P) : G) at he
    rw [e.apply_symm_apply] at he
    exact he.symm
  rw [hf]
  exact hU

private theorem zSubgroup_ne_bot
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (heven : Even (Nat.card G)) :
    zSubgroup S ≠ ⊥ := by
  have hSne : (S : Subgroup G) ≠ ⊥ :=
    S.ne_bot_of_dvd_card heven.two_dvd
  let : Nontrivial S :=
    (Subgroup.nontrivial_iff_ne_bot (S : Subgroup G)).2 hSne
  let : Nontrivial (Subgroup.center S) := S.isPGroup'.center_nontrivial
  have hcenterP : IsPGroup 2 (Subgroup.center S) :=
    S.isPGroup'.to_subgroup (Subgroup.center S)
  obtain ⟨n, hn, hcard⟩ := hcenterP.nontrivial_iff_card.mp inferInstance
  have hdvd : 2 ∣ Nat.card (Subgroup.center S) := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
  have hinner := omega₁_map_subtype_ne_bot
    (G := S) (Subgroup.center S) 2 hdvd
  intro hz
  apply hinner
  apply (Subgroup.map_eq_bot_iff_of_injective
    (H := (omega₁ (G := Subgroup.center S) (p := 2)).map
      (Subgroup.center S).subtype)
    (f := (S : Subgroup G).subtype) (S : Subgroup G).subtype_injective).mp
  simpa [zSubgroup, omegaOneCenterAmbient] using hz

/-- The partner two-core residual commutator lies in the original module V. -/
public theorem partner_core_residual_le_v
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (heven : Even (Nat.card G))
    (P Pstar E : Subgroup G) (hpair : (P, Pstar) ∈ Lambda S)
    (hPC : P ≤ cSubgroup S) (hEP : E ≤ Pstar)
    (hsolv : Group.IsSolvable Pstar) (hchar : IsCharacteristicTwoType Pstar)
    (hE : (E : Set G) = (twoResidualAmbient Pstar : Set G) *
      (twoCoreAmbient (cSubgroup S) : Set G))
    (hSyl : IsSylowSubgroupIn (twoCoreAmbient (cSubgroup S)) E) :
    ⁅pCore 2 Pstar, twoResidualAmbient (⊤ : Subgroup Pstar)⁆ ≤
      Subgroup.normalClosure ((zSubgroup S).subgroupOf Pstar : Set Pstar) := by
  obtain ⟨SP, hsec, hSP, hV⟩ :=
    original_partner_sectionTwo_data S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  let B := twoCoreAmbient (cSubgroup S) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (twoCoreAmbient (cSubgroup S))) : Set G)
  let BN := B.subgroupOf Pstar
  let L := Subgroup.normalClosure (BN : Set Pstar)
  let V := Subgroup.normalClosure ((zSubgroup S).subgroupOf Pstar : Set Pstar)
  let C := Subgroup.centralizer (V : Set Pstar)
  let _ : V.Normal := Subgroup.normalClosure_normal
  let _ : L.Normal := Subgroup.normalClosure_normal
  let _ : C.Normal := inferInstance
  let q : Pstar →* Pstar ⧸ C := QuotientGroup.mk' C
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective C
  have hker : q.ker = C := QuotientGroup.ker_mk' C
  have hSPstar : (S : Subgroup G) ≤ Pstar := hSP ▸ Subgroup.map_subtype_le _
  have hBS : B ≤ (S : Subgroup G) := by
    obtain ⟨_, _, _, _, SP', Q, hSP', hQ, _, hQS, _, _⟩ :=
      baumann_normal_supplement_data S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
    have hm := Subgroup.map_mono (f := Pstar.subtype) hQS
    rw [hQ, hSP'] at hm
    exact inf_le_left.trans hm
  have hBP : B ≤ Pstar := hBS.trans hSPstar
  have hBNmap : BN.map Pstar.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBP
  have hBNS : BN ≤ (SP : Subgroup Pstar) := by
    apply (Subgroup.map_le_map_iff_of_injective Pstar.subtype_injective).mp
    rw [hBNmap, hSP]
    exact hBS
  have hVB : V ≤ BN := by
    apply (Subgroup.map_le_map_iff_of_injective Pstar.subtype_injective).mp
    rw [hBNmap]
    exact original_v_le_baumann S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  have hVe : IsElementaryAbelian 2 V := by
    change SectionTwo.vSubgroup SP = V at hV
    rw [← hV]
    exact (SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian hsec SP).2
  obtain ⟨PL, hPL⟩ := native_sylow_of_ambient Pstar L B hBP
    (baumann_isSylow_normalClosure S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl)
  have hgen : L ⊔ (SP : Subgroup Pstar) = ⊤ := by
    apply Subgroup.map_injective Pstar.subtype_injective
    rw [Subgroup.map_sup, hSP, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact baumann_closure_sup_sylow S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  have hunique : IsUniqueMaximalContaining (SP : Subgroup Pstar) (⊤ : Subgroup Pstar) := by
    apply native_uniqueMaximalContaining
    rw [hSP]
    exact hpair.2.1.2
  have hBne : BN.map q ≠ ⊥ := by
    intro hbot
    have hLmap : L.map q = ⊥ := by
      rw [show L = Subgroup.normalClosure (BN : Set Pstar) from rfl,
        Subgroup.map_normalClosure _ q hq]
      change Subgroup.normalClosure (BN.map q : Set (Pstar ⧸ C)) = ⊥
      rw [hbot]
      simp
    have hLC : L ≤ C := (Subgroup.map_eq_bot_iff _).mp hLmap |>.trans_eq hker
    have hVC : V ≤ Subgroup.centralizer (L : Set Pstar) := Subgroup.le_centralizer_iff.mp hLC
    have hVbot : V = ⊥ := by
      have hfixed := baumann_fixed_factor_eq_bot S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
      change V ⊓ Subgroup.centralizer (L : Set Pstar) = ⊥ at hfixed
      rwa [inf_eq_left.mpr hVC] at hfixed
    have hZP : zSubgroup S ≤ Pstar := (Subgroup.map_subtype_le _).trans hSPstar
    have hZsub : (zSubgroup S).subgroupOf Pstar = ⊥ := by
      apply le_bot_iff.mp
      exact Subgroup.le_normalClosure.trans_eq hVbot
    apply zSubgroup_ne_bot S heven
    rw [← Subgroup.map_subgroupOf_eq_of_le hZP, hZsub, Subgroup.map_bot]
  have hdata := baumann_factor_module_decomposition S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  change SectionTwo.BaumannFactorModuleData V L q at hdata
  obtain ⟨n, D, _Vf, _hDgen, hprod, hSL, _hVf, _hVprod⟩ := hdata.factors
  exact SectionTwo.core_residual_le_prescribed_module hsolv SP V L BN hVe hVB hBNS
    PL hPL hgen hunique q hq hker hBne (Sylow.map_image_eq_inf SP L BN PL hPL hBNS q)
    D hprod hSL (fun K PK hPK hKgen =>
      baumann_factor_characteristic_obstruction S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
        K PK SP hSP hPK hKgen)

end Stellmacher.SectionFour
