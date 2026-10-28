module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.OmegaStructure
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PResidual.PerfectCover
/-!
# The action kernel under Campbell's residual commutator bound

Let Q=O₂(H) and V=Campbell's natural commutator layer. If [O²(H),Q]
lies in V, the two-residual of C_H(V) acts on Q with vanishing second
commutator. Residual commutator idempotence makes this action trivial;
characteristic two then forces that residual to vanish. Consequently the
original action kernel is exactly Q, with no cover-kernel assumption.

This is the first block-recognition step in the one-noncentral-chief-factor
alternative of Campbell II.8, printed p.38, used in Aschbacher–Smith C.1.18.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H : Type*} [Group B] [Finite B] [Group H] [Finite H] {e : B →* H}

theorem kernel_eq_core_of_residual_commutator_le
    (h : InLocalClass e) (hB : IsBaumannFixed B)
    (hcomm : ⁅pResidual 2 H,pCore 2 H⁆ ≤ Campbell.V H) :
    localKernel e = pCore 2 H := by
  let C := localKernel e
  let R := (pResidual 2 C).map C.subtype
  have hpR : IsPPerfect 2 R := isPPerfect_embedded_pResidual 2 C
  have hRL : R ≤ pResidual 2 H := map_pResidual_le 2 C.subtype
  obtain ⟨n,hn,F,_,_,_,hF,⟨m⟩⟩ := h.natural
  have hVC : Campbell.V H ≤ localV e :=
    (h.campbellV_eq_moved hB m).le.trans (moved_le_localV e)
  have hRC : R ≤ centralizer (Campbell.V H : Set H) :=
    (map_subtype_le _).trans (centralizer_le hVC)
  have hQR : ⁅pCore 2 H,R⁆ ≤ Campbell.V H := by
    rw [commutator_comm]
    exact (commutator_mono hRL le_rfl).trans hcomm
  have hzero : ⁅pCore 2 H,R⁆ = ⊥ := by
    have hi := commutator_isPPerfect_idempotent R (pCore 2 H) hpR pCore_isPGroup
      (show R ≤ normalizer (pCore 2 H : Set H) by rw [normalizer_eq_top];exact le_top)
    rw [←hi]
    exact le_bot_iff.mp ((commutator_mono hQR le_rfl).trans_eq
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hRC)))
  have hRQ : R ≤ pCore 2 H :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)).trans
      h.core_selfCentralizing
  have hRbot : R=⊥ := by
    have ht := hpR.hom_eq_one_of_isPGroup pCore_isPGroup (inclusion hRQ)
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro x hx
    have hx1 := congrArg (fun f : R →* pCore 2 H => (f ⟨x,hx⟩ : H)) ht
    exact hx1
  have hres : pResidual 2 C=⊥ := by
    apply map_injective C.subtype_injective
    simpa only [Subgroup.map_bot] using hRbot
  have hpC : IsPGroup 2 C := by
    have hh := isPGroup_quotient_pResidual (G:=C) 2
    exact hh.of_equiv ((QuotientGroup.quotientMulEquivOfEq hres).trans
      QuotientGroup.quotientBot)
  exact le_antisymm (le_sSup ⟨inferInstance,hpC⟩) h.core_le_localKernel
end CFSG.Quasithin.ChapterC.GlaubermanNiles
