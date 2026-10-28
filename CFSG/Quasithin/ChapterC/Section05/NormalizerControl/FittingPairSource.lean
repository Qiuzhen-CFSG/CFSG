module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.FittingPairKernel
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.FullSpan
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreAction
/-!
# The original reduced source supplies the C.5.12 core commutator

The actual full Sylow normalizes K, so the ambient two-core normalizes K
and centralizes U(K). Block displacement bounds its commutator by U(K).
Since the reduced module contains U(K), the reverse containment follows
from [U(K),K]=U(K). Consequently the two-conjugate kernel and the original
small-span SQTK obstruction need no additional commutator or kernel premise.
The order-sixteen hypothesis remains explicit for the original four-space
application; no order bound is asserted for arbitrary central covers.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
theorem source_core_commutator_of_reduced (K V : Subgroup G) (hK : IsShort K)
    (S : Sylow 2 G) (hSK : (S : Subgroup G) ≤ normalizer (K : Set G))
    (hV : IsPReduced 2 V) (hUV : U K ≤ V) : ⁅pCore 2 G,K⁆ = U K := by
  have hQK : pCore 2 G ≤ normalizer (K : Set G) :=
    pCore_isPGroup.le_sylow_of_normal S |>.trans hSK
  have hQC : pCore 2 G ≤ centralizer (U K : Set G) :=
    hK.normalizing_twoGroup_centralizes_blockU pCore_isPGroup le_normalizer_of_normal hQK
  have hUK : ⁅U K,K⁆ = U K := by
    have hi := commutator_isPPerfect_idempotent K (pCoreIn 2 K)
      hK.twoPerfect (isPGroup_pCoreIn 2 K)
      (K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
    simpa only [U,pCoreIn,blockU,map_commutator,← MonoidHom.range_eq_map,range_subtype] using hi
  apply le_antisymm
  · rw [commutator_comm]
    exact block_fixer_displacement hK hQK hQC
  · exact hUK.symm.le.trans (commutator_mono (hUV.trans hV.le_pCore) le_rfl)
/-- The original reduced source eliminates nonquasisimple C-components of
its literal four-space pair section. -/
theorem pair_span_quasisimple_from_reduced
    {κ : GroupClass} (K V : Subgroup G) (hK : IsShort K)
    (S : Sylow 2 G) (hSK : (S : Subgroup G) ≤ normalizer (K : Set G))
    (hV : IsPReduced 2 V) (hUV : U K ≤ V)
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hU : Nat.card (U K) = 16) (g : G)
    (hD : IsSQTK κ (K ⊔ K.conjBy g : Subgroup G))
    (L : Subgroup ((K ⊔ K.conjBy g : Subgroup G) ⧸ pCore 2 (K ⊔ K.conjBy g : Subgroup G)))
    (hL : L.IsCComponent) : IsQuasisimple L := by
  let : V.Normal := hV.normal
  let : IsElementaryAbelian 2 V := hV.elementary
  have hUgV : (U K).conjBy g ≤ V := by
    have hm : V.map (MulAut.conj g).toMonoidHom = V := by
      exact (mem_normalizer_iff_map_conj_eq.mp (show g ∈ normalizer (V : Set G) from
        le_normalizer_of_normal (mem_top g)))
    exact (map_mono hUV).trans_eq hm
  have hWV : U K ⊔ (U K).conjBy g ≤ V := sup_le hUV hUgV
  let : IsElementaryAbelian 2 (U K ⊔ (U K).conjBy g : Subgroup G) := {
    toIsMulCommutative := IsMulCommutative.of_comm (fun a b =>
      Subtype.ext (congrArg V.subtype (mul_comm (⟨a,hWV a.property⟩ : V) ⟨b,hWV b.property⟩)))
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun w =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (w : G) (hWV w.property))) }

  exact pair_span_quasisimple_from_ambient_core K (U K) g hchar
    (source_core_commutator_of_reduced K V hK S hSK hV hUV) (map_subtype_le _) hU hD L hL
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
