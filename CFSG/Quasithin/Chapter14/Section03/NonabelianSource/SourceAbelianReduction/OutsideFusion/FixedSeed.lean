module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.OutsideFusion.FixedSeed.Defs
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.OriginalSolvable
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ParabolicNormalizerIntersection
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.NormalSylowResidual
public import Theory.GroupTheory.PResidual.OddImageInvolutions
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# Returning the fixed seed to the conjugate two-core

Conjugation by y embeds C_{I₂}(t) into H = C_G(z), since t = y⁻¹ z y.
The full orthogonal action makes the two-residual of H/Q have order nine.
Consequently each involution in the embedded residual of C_{I₂}(t)
maps trivially to H/Q. Once the natural centralizer action supplies the
seed in that residual, the original marked point belongs to Q^y.

The residual-generation input remains explicit; this module does not yet
prove the fixed-seed case without that source input. No self-centralization
or collapse of the original two-core is used.

Source: Aschbacher--Smith, Quasithin Groups, 14.3.21(2), printed p.998.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Recognition
variable {G : Type*} [Group G] [Finite G]

private theorem fixedSeed_point_centralizer
    {T : Sylow 2 G} {V : Subgroup G} (F : InvariantFlag T V 2)
    (z : G) (hz : z ∈ F.Vi 1) (hzne : z ≠ 1) :
    F.H = centralizer ({z} : Set G) := by
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hz2 : orderOf z = 2 := by
    have hp : (⟨z,hz⟩ : F.Vi 1)^2 = 1 := by
      simpa [hc] using pow_card_eq_one' (x := (⟨z,hz⟩ : F.Vi 1))
    exact orderOf_eq_prime (congrArg Subtype.val hp) hzne
  have he : zpowers z = F.Vi 1 := eq_of_le_of_card_ge (zpowers_le.mpr hz)
    (by rw [Nat.card_zpowers,hz2,hc])
  change normalizer (F.Vi 1 : Set G) = _
  rw [← he]
  exact normalizer_zpowers_eq_centralizer_of_order_two z hz2

/-- The literal fixed-seed core return, conditional on its preceding
centralizer residual-generation step. -/
theorem source_fixed_seed_core_return_of_residual_generation
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
    (hres : FixedSeedResidualGeneration F (sourceResidual M Mc)) :
    FixedSeedCoreReturn F (sourceResidual M Mc) := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨_,_,hRP,hRN,hRc⟩ := parabolic_core_intersection_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
  have hRne : F.terminalDot R ≠ ⊥ := by
    intro hb
    rw [hb,Subgroup.card_bot] at hRc
    omega
  obtain ⟨_,hrescard,_⟩ :=
    ChapterG.Section09.FittingRecognition.Four.full_orthogonal_normal_sylow_residual
      F.terminalRepresentation hr P (F.terminalDot R) hRP hRN hRne
  have hodd : Odd (Nat.card (pResidual 2 F.TerminalHdot)) := by
    rw [hrescard]
    decide
  intro z hz hzne t htT ht2 htout htV y hy
  let C := F.I₂ (sourceResidual M Mc) ⊓ centralizer ({t} : Set G)
  have hseed : rankTwoSeed T M ≤ (pResidual 2 C).map C.subtype :=
    hres t htT ht2 htout htV
  have hz2 : z ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian (p:=2) z (F.le_seed 1 hz)
  have hty : (MulAut.conj y) t = z := by
    rw [←hy]
    change y * (y⁻¹*z*y) * y⁻¹ = z
    group
  let f : C →* F.H :=
    ((MulAut.conj y).toMonoidHom.comp C.subtype).codRestrict F.H (by
      intro a
      rw [fixedSeed_point_centralizer F z hz hzne]
      apply mem_centralizer_singleton_iff.mpr
      have hh := congrArg (MulAut.conj y)
        (mem_centralizer_singleton_iff.mp a.property.2)
      change (MulAut.conj y) (a:G) * z = z * (MulAut.conj y) (a:G)
      simpa only [map_mul, hty] using hh)
  obtain ⟨a,ha,haz⟩ := hseed (F.le_seed 1 hz)
  change (a:G) = z at haz
  have ha2 : a ^ 2 = 1 := Subtype.ext (by change (a:G)^2=1; rw [haz,hz2])
  have hqa : q (f a) = 1 :=
    map_eq_one_of_square_one_mem_twoResidual (q.comp f) hodd a ha ha2
  have haQ : f a ∈ pCore 2 F.H := by
    rw [←terminal_kernel_of_center_point F dg hZ]
    exact (QuotientGroup.eq_one_iff (f a)).mp hqa
  refine ⟨(f a:G), mem_map_of_mem F.H.subtype haQ, ?_⟩
  change y⁻¹ * (y * (a:G) * y⁻¹) * (y⁻¹)⁻¹ = z
  rw [haz]
  group

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
