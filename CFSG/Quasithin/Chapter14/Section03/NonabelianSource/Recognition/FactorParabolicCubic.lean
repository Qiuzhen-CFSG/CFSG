module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ParabolicResidual
public import Mathlib.GroupTheory.FixedPointFree

/-! The actual parabolic residual supplies a cubic acting without fixed
points on the chosen elementary factor. Its commutator map generates the
whole factor, retaining the source actor and the literal normalizer action.
Source: Aschbacher–Smith 14.3.18(2), 14.3.19(4). -/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G:Type*} [Group G] [Finite G]

theorem factor_parabolic_cubic_of_full_orthogonal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (dg : ClosureGeometry F) (hZ : F.ZU=F.Vi 1) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hr : ChapterG.Section09.FittingRecognition.OrthogonalRealization F.terminalRepresentation ⊤)
    (A:Subgroup G) [IsElementaryAbelian 2 A]
    (hAR:A≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hAc:Nat.card A=16)
    (hIA:F.I₂ (sourceResidual M Mc)≤normalizer (A:Set G)) :
    A≤sourceResidual M Mc ∧ A=⁅A,sourceResidual M Mc⁆ ∧
    ∃t:MulAut A,t∈(A.normalizerMonoidHom.comp (inclusion hIA)).range ∧
      t^3=1 ∧ t≠1 ∧ ∀a:A,t a=a→a=1 := by
  obtain ⟨hL,_,hcore,c,hcL,hc3,hfixed⟩ := parabolic_residual_core_structure_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
  have hLI:sourceResidual M Mc≤F.I₂ (sourceResidual M Mc) :=
    hL.ge.trans (map_subtype_le _)
  have hAL:A≤sourceResidual M Mc :=
    hAR.trans (hcore ▸ pCoreIn_le 2 (sourceResidual M Mc))
  have hcN:c∈normalizer (A:Set G) := hIA (hLI hcL)
  let t:MulAut A := A.normalizerMonoidHom ⟨c,hcN⟩
  have hfree:MonoidHom.FixedPointFree t := by
    intro a ha
    apply Subtype.ext
    have hc:(a:G)∈centralizer ({c}:Set G) :=
      mem_centralizer_singleton_iff.mpr ((mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val ha)).symm)
    exact (show (a:G)∈(⊥:Subgroup G) from hfixed ▸ ⟨hAR a.property,hc⟩)
  have hcomm:A=⁅A,sourceResidual M Mc⁆ := by
    apply le_antisymm ?_ (le_normalizer_iff_commutator_le_left.mp (hLI.trans hIA))
    intro a ha
    obtain ⟨u,hu⟩ := hfree.commutatorMap_surjective (⟨a,ha⟩:A)
    have he:(u:G)/(c*(u:G)*c⁻¹)=a := congrArg Subtype.val hu
    rw [←he]
    have hh:=commutator_mem_commutator u.property hcL
    simpa only [commutatorElement_def,div_eq_mul_inv,mul_inv_rev,inv_inv,mul_assoc] using hh
  have ht3:t^3=1 := by
    change (A.normalizerMonoidHom ⟨c,hcN⟩)^3=1
    rw [←map_pow]
    have hc:(⟨c,hcN⟩:normalizer (A:Set G))^3=1 := by
      apply Subtype.ext
      change c^3=1
      rw [←hc3]
      exact pow_orderOf_eq_one c
    rw [hc,map_one]
  have htne:t≠1 := by
    let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by rw [hAc];decide)
    obtain ⟨a,ha⟩:=exists_ne (1:A)
    intro ht
    exact ha (hfree a (by rw [ht];rfl))
  exact ⟨hAL,hcomm,t,⟨⟨c,hLI hcL⟩,rfl⟩,ht3,htne,hfree⟩
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
