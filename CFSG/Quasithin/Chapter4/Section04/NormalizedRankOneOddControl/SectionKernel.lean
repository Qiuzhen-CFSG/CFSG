module
public import CFSG.Quasithin.Chapter4.Section01.Maximality
public import Theory.GroupTheory.NormalizerQuotientOuterPair
public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
import Mathlib.Tactic

/-!
# The section-centralizer clause in Remark 4.4.2

An element normalizing L and fixing the nontrivial commutator module acts
trivially on L/O₂(L). The induced module action has central kernel because
its domain is quasisimple. Maps from a perfect group agreeing modulo this
central kernel are equal. This retains arbitrary central covers.

Source: Aschbacher--Smith, Remark 4.4.2, printed p.619. The chosen-module
application is in NonFFSourceRankOneOddControl.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
variable {G : Type*} [Group G]

/-- Fixing the actual module kills the action on the original core quotient. -/
theorem relative_module_centralizer_le_sectionCentralizer
    (L W : Subgroup G) [IsQuasisimple (L ⧸ pCore 2 L)]
    (hLW : L ≤ normalizer (W : Set G))
    (hcore : L.pCoreIn 2 ≤ centralizer (W : Set G))
    (hW : W ≠ ⊥) (hcomm : W = ⁅W,L⁆) :
    normalizer (L : Set G) ⊓ centralizer (W : Set G) ≤
      sectionCentralizer L := by
  let f : L →* MulAut W := W.normalizerMonoidHom.comp (inclusion hLW)
  have hk : pCore 2 L ≤ f.ker := by
    intro l hl
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    change (l : G) * (w : G) * (l : G)⁻¹ = w
    exact mul_inv_eq_iff_eq_mul.mpr
      ((mem_centralizer_iff.mp (hcore (mem_map_of_mem L.subtype hl))) w w.property).symm
  let q := QuotientGroup.mk' (pCore 2 L)
  let fQ : (L ⧸ pCore 2 L) →* MulAut W := QuotientGroup.lift _ f hk
  have hf : fQ.ker ≤ center (L ⧸ pCore 2 L) := by
    rcases IsQuasisimple.normal_le_center_or_eq_top fQ.ker with hc | ht
    · exact hc
    · exfalso
      apply hW
      rw [hcomm]
      apply commutator_eq_bot_iff_le_centralizer.mpr
      apply le_centralizer_iff.mp
      intro l hl w hw
      have he := DFunLike.congr_fun (fQ.ker_eq_top_iff.mp ht) (q ⟨l,hl⟩)
      have hh := congrArg (fun a : MulAut W => ((a ⟨w,hw⟩ : W) : G)) he
      change l * w * l⁻¹ = w at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  apply (le_sectionCentralizer_iff _ L).mpr
  refine ⟨inf_le_left, commutator_le.mpr ?_⟩
  intro b hb l hl
  let bN : normalizer (L : Set G) := ⟨b,hb.1⟩
  let a := normalizerPCoreQuotientAction L bN
  have hfac : fQ.comp a.toMonoidHom = fQ.comp (MonoidHom.id _) := by
    apply MonoidHom.ext
    intro x
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
    apply MulEquiv.ext
    intro w
    change fQ (quotientAut (pCore 2 L) (L.normalizerMonoidHom bN) (q x)) w = fQ (q x) w
    rw [quotientAut_apply_mk]
    apply Subtype.ext
    change (b * (x : G) * b⁻¹) * (w : G) * (b * (x : G) * b⁻¹)⁻¹ =
      (x : G) * (w : G) * (x : G)⁻¹
    have hw := ((mem_centralizer_iff.mp hb.2) w w.property).symm
    have hxw : (x : G) * (w : G) * (x : G)⁻¹ ∈ W :=
      (hLW x.property w).mp w.property
    have hbw := ((mem_centralizer_iff.mp hb.2) _ hxw).symm
    calc
      _ = b * ((x : G) * (w : G) * (x : G)⁻¹) * b⁻¹ := by
        have hbw' : b⁻¹ * (w : G) * b = w := by
          rw [mul_assoc, ← hw, ← mul_assoc, inv_mul_cancel, one_mul]
        calc
          _ = b * (x : G) * (b⁻¹ * (w : G) * b) * (x : G)⁻¹ * b⁻¹ := by group
          _ = _ := by rw [hbw']; group
      _ = _ := mul_inv_eq_iff_eq_mul.mpr hbw
  have ha : a.toMonoidHom = MonoidHom.id _ :=
    PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq fQ hf _ _ hfac
  have he := DFunLike.congr_fun ha (q ⟨l,hl⟩)
  change quotientAut (pCore 2 L) (L.normalizerMonoidHom bN) (q ⟨l,hl⟩) = q ⟨l,hl⟩ at he
  rw [quotientAut_apply_mk] at he
  let c : L := L.normalizerMonoidHom bN ⟨l,hl⟩ * (⟨l,hl⟩ : L)⁻¹
  have hc : c ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff c).mp
    change q (L.normalizerMonoidHom bN ⟨l,hl⟩ * (⟨l,hl⟩ : L)⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  exact ⟨c,hc,rfl⟩

end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
