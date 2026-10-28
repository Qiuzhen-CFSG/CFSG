module
public import Stellmacher.SectionFour.OriginalVContainment
public import Stellmacher.SectionTwo.NormalSupplementBaumannDecomposition
public import Stellmacher.BaumannMap

/-!
# The actual factor and module decomposition in Stellmacher (4.6)

For the critical-partner configuration, let B₀ be the Baumann subgroup of
O₂(C), let L be its normal closure inside Pstar, and retain the original
V=⟨Ω₁(Z(S))^Pstar⟩. The image of L in Pstar/C_Pstar(V) has a common finite
family of SL₂(2) factors and four-element commutator modules in V. Its fixed
complement is V∩C_Pstar(L). This is the ambient-image presentation of the
source quotient L/C_L(V).

The original-partner setup identifies V with the Section Two module for the
native Sylow whose image is the original S. The proved original-V containment
places it in O₂(C). The normal supplement E=O²(Pstar)O₂(C) supplies a native
Sylow with precisely that image and satisfies the hypotheses of the imported
normal-supplement decomposition. Injective Baumann transport identifies its
Baumann subgroup with the literal B₀. Applying that theorem and rewriting
these exact subgroup identities gives the stated original quotient and module.
No identification with a module newly defined from O₂(C) is made.

The shared data records the existing internal-product-family predicate;
no unrestricted module independence or product cardinality is inferred.
This result supplies displayed (i),(ii); eliminating the fixed factor and
completing the later core and Hall-orbit arguments remain separate results.

Source: Stellmacher, Journal of Algebra 190 (1997), (4.6), journal p26.
-/

open scoped Pointwise
namespace Stellmacher.SectionFour
universe u

/-- The source L-image and original V share the finite factor/module family of (4.6). -/
public theorem baumann_factor_module_decomposition
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (heven : Even (Nat.card G))
    (P Pstar E : Subgroup G) (hpair : (P, Pstar) ∈ Lambda S)
    (hPC : P ≤ cSubgroup S) (hEP : E ≤ Pstar)
    (hsolv : Group.IsSolvable Pstar) (hchar : IsCharacteristicTwoType Pstar)
    (hE : (E : Set G) = (twoResidualAmbient Pstar : Set G) *
      (twoCoreAmbient (cSubgroup S) : Set G))
    (hSyl : IsSylowSubgroupIn (twoCoreAmbient (cSubgroup S)) E) :
    let B := twoCoreAmbient (cSubgroup S) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (twoCoreAmbient (cSubgroup S))) : Set G)
    let L := Subgroup.normalClosure (B.subgroupOf Pstar : Set Pstar)
    let V := Subgroup.normalClosure ((zSubgroup S).subgroupOf Pstar : Set Pstar)
    let C := Subgroup.centralizer (V : Set Pstar)
    letI : V.Normal := Subgroup.normalClosure_normal
    letI : C.Normal := inferInstance
    SectionTwo.BaumannFactorModuleData V L (QuotientGroup.mk' C) := by
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
  have hdata := SectionTwo.normal_supplement_baumann_decomposition
    hsec SP q hq hker N Q hgen' hSN' hVQ
  change SectionTwo.BaumannFactorModuleData V L q
  change SectionTwo.BaumannFactorModuleData (SectionTwo.vSubgroup SP)
    (Subgroup.normalClosure (BN : Set Pstar)) q at hdata
  rw [hV, ← hBsub] at hdata
  exact hdata

end Stellmacher.SectionFour
