module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralPointAction
import Theory.GroupTheory.ConjugateSpanNormalizer

/-!
# The actual local closure configuration before the Mathieu branch

The full original U first generates R inside C_G(z). The local group is
the literal H=R L1 T, with L1=O²(C_K(z)); the smaller point closure is
W=<V1^R>. Normalization proves W=<V1^H> on these same subgroups.
G.2.1 therefore gives the Frattini and two-core conclusions for this W,
and the original failure U≤O₂(C_G(z)) forces nontrivial action on W/<z>.

Source: Aschbacher--Smith12.7.15(1), printed p.843.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original smaller closure, actual local group and nontrivial quotient
action are constructed without a closure-identification premise. -/
theorem original_tripleSix_central_closure_configuration
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2) :
    let C := centralizer ({(z:G)} : Set G)
    let J := (pResidual 2 (K ⊓ C : Subgroup G)).map (K ⊓ C).subtype
    let R := conjugateSpanBy U C
    let H := R ⊔ J ⊔ (T : Subgroup G)
    let V1 := tripleSixPoint D a z
    let W := conjugateSpanBy V1 R
    H ≤ C ∧ W = conjugateSpanBy V1 H ∧ W ≤ H.pCoreIn 2 ∧
      (frattini W).map W.subtype ≤ zpowers (z:G) ∧
      ⁅W,H.pCoreIn 2⁆ ≤ zpowers (z:G) ∧ ¬ U ≤ H.pCoreIn 2 ∧
      ¬ ⁅U,W⁆ ≤ zpowers (z:G) := by
  let C := centralizer ({(z:G)} : Set G)
  let J := (pResidual 2 (K ⊓ C : Subgroup G)).map (K ⊓ C).subtype
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let V1 := tripleSixPoint D a z
  let W := conjugateSpanBy V1 R
  change H ≤ C ∧ W = conjugateSpanBy V1 H ∧ W ≤ H.pCoreIn 2 ∧
    (frattini W).map W.subtype ≤ zpowers (z:G) ∧
    ⁅W,H.pCoreIn 2⁆ ≤ zpowers (z:G) ∧ ¬ U ≤ H.pCoreIn 2 ∧
    ¬ ⁅U,W⁆ ≤ zpowers (z:G)
  have hUC : U ≤ C := D.le_sylow.trans hzT
  have hUR : U ≤ R := le_conjugateSpanBy U C
  have hRC : R ≤ C := conjugateSpanBy_le_self hUC
  have hJC : J ≤ C := (map_subtype_le _).trans inf_le_right
  have hHC : H ≤ C := sup_le (sup_le hRC hJC) hzT
  have hTH : (T : Subgroup G) ≤ H := le_sup_right
  have hRH : R ≤ H := le_sup_left.trans le_sup_left
  have hCR : C ≤ normalizer (R : Set G) := le_normalizer_conjugateSpanBy U C
  have hp := tripleSixPoint_properties D a z hz
  have hVU : V1 ≤ U := hp.2.1
  have hJV : J ≤ normalizer (V1 : Set G) :=
    ((map_subtype_le _).trans hp.2.2.2.2).trans (Subgroup.centralizer_le_normalizer _)
  have hTV : (T : Subgroup G) ≤ normalizer (V1 : Set G) :=
    (original_tripleSix_central_point_g21 h D a z hz hzT).T_normalizes_V
  have hHW : H ≤ normalizer (W : Set G) := sup_le
    (sup_le (le_normalizer_conjugateSpanBy V1 R)
      (normalizes_conjugateSpanBy V1 R J hJV (hJC.trans hCR)))
    (normalizes_conjugateSpanBy V1 R (T : Subgroup G) hTV (hzT.trans hCR))
  have hW : W = conjugateSpanBy V1 H := le_antisymm
    (conjugateSpanBy_mono le_rfl hRH)
    (conjugateSpanBy_le (le_conjugateSpanBy V1 R) hHW)
  have hs := original_tripleSix_central_point_g21_at h D a z hz hzT H hTH hHC
  have hnotH : ¬ U ≤ H.pCoreIn 2 := by
    intro hu
    exact hnot (((le_inf hUR hu).trans (inf_pCoreIn_le_of_le 2 hRH)).trans
      (pCoreIn_mono_of_normalizes hRC hCR))
  refine ⟨hHC,hW,?_,?_,?_,hnotH,?_⟩
  · rw [hW]
    exact hs.U_le_core
  · rw [hW]
    exact hs.frattini_U_le_point
  · rw [hW]
    exact hs.commutator_U_core_le_point
  · rw [hW]
    exact original_tripleSix_central_point_action_nontrivial
      h structural D a z hz hzT H hTH hHC hnotH

end CFSG.Quasithin.Chapter12.Section07
