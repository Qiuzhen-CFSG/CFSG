module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticKernelRadicals
public import Theory.GroupTheory.ConjugateSpanNormalizer
public import Theory.Frattini.InvolutorySupplement

/-!
# Canonical orbit support for the full quintic radius-two kernel

The opposite point lies in U, so C=C_H(U) centralizes that point. Its
conjugates of the actual critical module W consequently lie in the same
transported abelian Mc-span. The canonical orbit span R is elementary,
because its generators lie in conjugates of the elementary W. It is
normalized by C and W, and acts quadratically on the full C.

The original radical index gives |CW:C|=4. The involutory supplement W
also gives the exact embedded Frattini formula, retaining Phi(C) and
[C,W]. No normalization of W by C or rank bound on R is assumed.

Source: Aschbacher--Smith F.9.13--17, pp.322--324, and the original
quintic source14.2.21, p.988, in refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter13.Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab

/-- The canonical C-orbit span is an actual elementary quadratic support
for the full kernel. The order-four extension and Frattini factor retain
both the original kernel and the original critical module. -/
theorem source_quintic_full_kernel_orbit_support
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab H hH.1
    let C := H ⊓ centralizer (D.UH : Set G)
    ∀ i : h.CriticalEndpoint,
      let W := i.conjugate D.UH
      let R := conjugateSpanBy W C
      let S := C ⊔ W
      IsElementaryAbelian 2 R ∧
      W ≤ R ∧ R ≤ H ∧
      R ≤ i.conjugate (conjugateSpanBy (localModule T M) Mc) ∧
      S ≤ normalizer (R : Set G) ∧ S ≤ normalizer (C : Set G) ∧
      C ⊔ R = S ∧ IsPGroup 2 S ∧
      ⁅C,R⁆ ≤ C ⊓ R ∧ ⁅⁅C,R⁆,R⁆ = ⊥ ∧
      C.relIndex S = 4 ∧ Nat.card S = 4 * Nat.card C ∧
      (frattini S).map S.subtype = (frattini C).map C.subtype ⊔ ⁅C,W⁆ := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab H hH.1
  let C := H ⊓ centralizer (D.UH : Set G)
  let L := conjugateSpanBy (localModule T M) Mc
  let : IsMulCommutative L := hab
  let : IsElementaryAbelian 2 D.UH :=
    (Section02.SolvableAmalgam.source_index_five_closure_structure
      hG T hempty hM hu hmany hcard e H hH.1 hi).1
  obtain ⟨hb,_,_,_⟩ := source_quintic_reciprocal_core_hyperplanes
    hG T hempty hM hu hmany hcard e hab H hH hi
  obtain ⟨_,_,hMc,_⟩ := plane_ordering_and_overgroups
    hG T hempty hM hu hmany hcard h.point_card
  have hHMc : H ≤ Mc := h.H_centralizes.trans_eq hMc.symm
  have hUL : D.UH ≤ L := conjugateSpanBy_mono le_rfl hHMc
  have hCH : C ≤ H := inf_le_left
  have hHN : H ≤ normalizer (C : Set G) :=
    (le_inf H.le_normalizer ((le_normalizer_conjugateSpanBy _ _).trans
      (normalizer_le_normalizer_centralizer D.UH))).trans inf_normalizer_le_normalizer_inf
  have hCQ : C ≤ D.QH := by
    rw [←h.kernel_UH_eq_QH]
    intro c hc
    apply (h.mem_kernel_iff h.UH_le_H).mpr
    refine ⟨hc.1,fun u hu => ?_⟩
    have hz : ⁅u,c⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hc.2 u hu)
    exact hz ▸ D.V₁.one_mem
  have hCp : IsPGroup 2 C := (isPGroup_pCoreIn 2 H).to_le hCQ
  change ∀ i : h.CriticalEndpoint, _
  intro i
  let W := i.conjugate D.UH
  let R := conjugateSpanBy W C
  let S := C ⊔ W
  let Lg := i.conjugate L
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsMulCommutative Lg := Subgroup.map_isMulCommutative L _
  have hWH : W ≤ H := i.large_le hb
  have hWC : W ≤ normalizer (C : Set G) := hWH.trans hHN
  have hWR : W ≤ R := le_conjugateSpanBy _ _
  have hSN : S ≤ normalizer (C : Set G) := sup_le C.le_normalizer hWC
  have hSp : IsPGroup 2 S := hCp.to_sup_of_normal_left'
    (IsElementaryAbelian.isPGroup 2 W) hWC
  have hp := (source_quintic_hyperplane_point_actions
    hG T hempty hM hu hmany hcard e hab H hH hi i).1
  have hpointU : i.conjugate D.V₁ ≤ D.UH := by
    calc
      i.conjugate D.V₁ = ⁅D.UH ⊓ i.conjugate D.QH,W⁆ := hp.symm
      _ ≤ ⁅D.UH,W⁆ := commutator_mono inf_le_left le_rfl
      _ ≤ D.UH := (i.commutator hb).trans inf_le_left
  have hCCpoint : C ≤ centralizer (i.conjugate D.V₁ : Set G) :=
    inf_le_right.trans (centralizer_le hpointU)
  have hCMcg : C ≤ i.conjugate Mc := by
    intro c hc
    let a := MulAut.conj i.representative
    refine ⟨a.symm c,?_,a.apply_symm_apply c⟩
    apply hMc.ge
    intro z hz
    apply a.injective
    simpa only [map_mul,a.apply_symm_apply] using
      hCCpoint hc (a z) (mem_map_of_mem a.toMonoidHom hz)
  have hMcgL : i.conjugate Mc ≤ normalizer (Lg : Set G) := by
    have hn := map_mono (f := (MulAut.conj i.representative).toMonoidHom)
      (le_normalizer_conjugateSpanBy (localModule T M) Mc)
    rwa [map_equiv_normalizer_eq] at hn
  have hRL : R ≤ Lg := conjugateSpanBy_le (map_mono hUL) (hCMcg.trans hMcgL)
  let : IsMulCommutative R :=
    le_centralizer_iff_isMulCommutative.mp
      (hRL.trans ((le_centralizer Lg).trans (centralizer_le hRL)))
  have hRe : IsElementaryAbelian 2 R := conjugateSpanBy_elementary_of_commutative W C
  have hRH : R ≤ H := conjugateSpanBy_le hWH (hCH.trans H.le_normalizer)
  have hSR : S ≤ normalizer (R : Set G) := sup_le
    (le_normalizer_conjugateSpanBy W C)
    (normalizes_conjugateSpanBy W C W W.le_normalizer hWC)
  have hRS : R ≤ S := conjugateSpanBy_le le_sup_right (le_sup_left.trans S.le_normalizer)
  have hjoin : C ⊔ R = S := le_antisymm (sup_le le_sup_left hRS)
    (sup_le le_sup_left (hWR.trans le_sup_right))
  have hcomm : ⁅C,R⁆ ≤ C ⊓ R := le_inf
    (le_normalizer_iff_commutator_le_left.mp (hRS.trans hSN))
    (le_normalizer_iff_commutator_le_right.mp (le_sup_left.trans hSR))
  have hquad : ⁅⁅C,R⁆,R⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      ((hcomm.trans inf_le_right).trans (le_centralizer R))
  have hiW : C.relIndex W = 4 := by
    rw [←inf_relIndex_left W C,inf_comm W C]
    exact (source_quintic_full_kernel_radicals
      hG T hempty hM hu hmany hcard e hab H hH hi i).2.2.1
  let : (C.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer hSN
  have hiS : C.relIndex S = 4 := by
    have hh := relIndex_sup_left (W.subgroupOf S) (C.subgroupOf S)
    rw [←subgroupOf_sup (show C ≤ S from le_sup_left) (show W ≤ S from le_sup_right),
      relIndex_subgroupOf (show C ⊔ W ≤ S from le_rfl),
      relIndex_subgroupOf (show W ≤ S from le_sup_right)] at hh
    exact hh.trans hiW
  have hsize : Nat.card S = 4 * Nat.card C := by
    have hh := relIndex_mul_card_of_le (show C ≤ S from le_sup_left)
    rw [hiS] at hh
    exact hh.symm
  have hphi := frattini_map_eq_of_involutory_supplement S C W hSp hCp rfl hWC
    (fun w hw => elemPow_eq_one_of_isElementaryAbelian w hw)
  exact ⟨hRe,hWR,hRH,hRL,hSR,hSN,hjoin,hSp,hcomm,hquad,hiS,hsize,hphi⟩

end CFSG.Quasithin.Chapter14.Section06
