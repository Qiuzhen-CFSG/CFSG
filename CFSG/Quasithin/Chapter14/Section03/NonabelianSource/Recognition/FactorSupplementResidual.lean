module
public import Theory.GroupTheory.PResidual.AutomorphismCentralizer
public import Theory.GroupTheory.GeneralizedFitting.ResidualOvergroups
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.SpecificGroups.DihedralAut
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorFullAutomorphism
/-!
# Residual centralization of the strict-centralizer supplement

The actual supplement D = O2(H) intersect C_G(U) is normalized by H.
Under strict centralizer enlargement it is dihedral of order eight, so its
automorphism group is a two-group. Therefore O^2(H) centralizes D.
For each d in D, H intersect C_G(d) contains this residual and is subnormal
in H; its intersection with the original Sylow subgroup T is consequently
a Sylow subgroup. All subgroup inclusions and Sylow images are literal.

Source: Aschbacher–Smith 14.3.20, second paragraph, printed p.997.
This supplies the local Sylow input before the later global promotion in C_G(d).
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
theorem source_factor_residual_centralizes_supplement_of_strict_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (A:Subgroup G) [IsElementaryAbelian 2 A]
    (hAR:A≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hVA:rankTwoSeed T M≤A) (hAc:Nat.card A=16)
    (hc8:Nat.card (A⊓F.U:Subgroup G)=8)
    (hAN:F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G))
    (hlt:A<centralizer (A:Set G)) :
    (pResidual 2 F.H).map F.H.subtype ≤
      centralizer ((F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G) : Subgroup G) : Set G) := by
  let D := F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)
  obtain ⟨eD⟩ := source_factor_supplement_dihedral_of_strict_centralizer
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN hlt
  have hd : IsPGroup 2 (DihedralGroup 4) := IsPGroup.of_card (n := 3) (by
    rw [DihedralGroup.nat_card]; decide)
  have ha : IsPGroup 2 (MulAut D) :=
    (DihedralGroup.isPGroup_mulAut_of_two_lt (by decide : 2 < 4) hd).of_equiv
      (MulAut.congr eD).symm
  have hHQ : F.H ≤ normalizer (F.H.pCoreIn 2 : Set G) := F.H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))
  have hHU : F.H ≤ normalizer (F.U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hHD : F.H ≤ normalizer (D : Set G) :=
    (le_inf hHQ (hHU.trans (normalizer_le_normalizer_centralizer F.U))).trans
      inf_normalizer_le_normalizer_inf
  exact embedded_pResidual_le_centralizer_of_aut_isPGroup 2 F.H D hHD ha

theorem source_factor_supplement_local_centralizer_sylow_of_strict_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (A:Subgroup G) [IsElementaryAbelian 2 A]
    (hAR:A≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hVA:rankTwoSeed T M≤A) (hAc:Nat.card A=16)
    (hc8:Nat.card (A⊓F.U:Subgroup G)=8)
    (hAN:F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G))
    (hlt:A<centralizer (A:Set G))
    (d : G) (hd : d ∈ F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)) :
    let C := F.H ⊓ centralizer ({d} : Set G)
    ∃ S : Sylow 2 C, (S : Subgroup C).map C.subtype =
      (T : Subgroup G) ⊓ centralizer ({d} : Set G) := by
  intro C
  let CH := C.subgroupOf F.H
  have hTH : (T : Subgroup G) ≤ F.H := F.invariant 1
  have hC : (pResidual 2 F.H).map F.H.subtype ≤ centralizer ({d} : Set G) :=
    (source_factor_residual_centralizes_supplement_of_strict_centralizer
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN hlt).trans
      (centralizer_le (Set.singleton_subset_iff.mpr hd))
  have hCH : pResidual 2 F.H ≤ CH := by
    intro x hx
    exact ⟨x.property, hC (mem_map_of_mem F.H.subtype hx)⟩
  obtain ⟨S,hS⟩ := (T.subtype hTH).exists_subgroupOf_eq_of_subnormal CH
    (residual_overgroup_subnormal CH hCH)
  let eC : CH ≃* C := subgroupOfEquivOfLe (show C ≤ F.H from inf_le_left)
  refine ⟨S.mapSurjective (f := eC.toMonoidHom) eC.surjective, ?_⟩
  change ((S : Subgroup CH).map eC.toMonoidHom).map C.subtype = _
  rw [hS]
  ext x
  constructor
  · rintro ⟨y, ⟨z,hz,rfl⟩,rfl⟩
    exact ⟨hz,z.property.2⟩
  · rintro ⟨hxT,hxd⟩
    let c : C := ⟨x,hTH hxT,hxd⟩
    refine ⟨c,⟨eC.symm c,?_,eC.apply_symm_apply c⟩,rfl⟩
    exact hxT

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
