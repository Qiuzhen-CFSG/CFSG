module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerLocalG2
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.NormalizedTwoGroups
public import Theory.GroupTheory.ConjugateCentralizerSupplement

/-!
# The first G₂ core factorization in source 3.3.28

Let U=U(L), Q=O₂(LT), X=O²(C_L(Ω₁Z(T))) and R=O₂(XT).
The original block hypotheses give Q≤R≤T and Q=C_R(U); the nonzero
chosen fixed subgroup makes R invariant under the Sylow normalizer.
The conjugate-centralizer order argument therefore proves Q=U C_Q(Uᵈ)
from the two literal moved-image inputs: C_R(Uᵈ)≤UᵈQ and the sharp
fixed-index bound on U. All conjugates use the source right-conjugation
convention, implemented by `MulAut.conj d⁻¹`.

These are the first product calculations in Aschbacher–Smith 3.3.28,
printed p.601. The G₂ model producer must supply the remaining two inputs;
the nonsplit-extension argument giving Q=U C_T(L), elementarity of Q,
and the maximum-elementary pair contradiction remain with the source
assembly owner. No NoEscape hypothesis or elementary-core assumption is used.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original G₂ core is supplemented by the fixed subgroup of its
moved intrinsic layer, from the sharp model calculation. -/
theorem g2Two_local_core_factorization_of_moved_fixed_index
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hb : ChapterC.IsG2TwoBlock L) {d : G} (hd : d ∈ normalizer (T : Set G))
    (hcover : blockLocalCore T L ⊓ centralizer
      (((ChapterC.blockU L).map L.subtype).map (MulAut.conj d⁻¹).toMonoidHom : Set G) ≤
        ((ChapterC.blockU L).map L.subtype).map (MulAut.conj d⁻¹).toMonoidHom ⊔
          (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hsharp : ((L ⊔ (T : Subgroup G)).pCoreIn 2).relIndex
      (((ChapterC.blockU L).map L.subtype).map (MulAut.conj d⁻¹).toMonoidHom) ≤
        (centralizer (((ChapterC.blockU L).map L.subtype).map
          (MulAut.conj d⁻¹).toMonoidHom : Set G)).relIndex ((ChapterC.blockU L).map L.subtype)) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 = (ChapterC.blockU L).map L.subtype ⊔
      ((L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer
        (((ChapterC.blockU L).map L.subtype).map (MulAut.conj d⁻¹).toMonoidHom : Set G)) := by
  let H := L ⊔ (T : Subgroup G)
  let Q := H.pCoreIn 2
  let X := blockLocalResidual T L
  let R := blockLocalCore T L
  let U := (ChapterC.blockU L).map L.subtype
  let : IsElementaryAbelian 2 U := hb.short.elementary.map L.subtype
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Q, H, Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow H (T.subtype le_sup_right)
  have hXL : X ≤ L := (map_subtype_le _).trans inf_le_left
  have hRT : R ≤ (T : Subgroup G) := by
    simpa only [R, blockLocalCore, X, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (X ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hHN : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hQR : Q ≤ R := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H)
    (hQT.trans le_sup_right) ((sup_le (hXL.trans le_sup_left) le_sup_right).trans hHN)
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) :=
    D.sylow_normalizes_component.trans
      (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L))
  have hUQ : U ≤ Q :=
    (map_mono ChapterC.blockU_le_core).trans
      (pCoreIn_mono_of_normalizes le_sup_left
        (sup_le L.le_normalizer D.sylow_normalizes_component))
  have hself : Q = R ⊓ centralizer (U : Set G) := by
    have hTself := hb.short.sylow_centralizer_blockU_eq_pCoreIn D.sylow_normalizes_component
    apply le_antisymm (le_inf hQR (hTself.symm.le.trans inf_le_right))
    exact (inf_le_inf_right _ hRT).trans hTself.le
  have hinv : R.map (MulAut.conj d⁻¹).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp
      (((blockLocalInvariance_of_g2Two h D hfixed hb).1 (Or.inr hb)).2
        ((normalizer (T : Set G)).inv_mem hd))
  exact centralizer_supplement_of_conjugate_sharp_index R Q U (MulAut.conj d⁻¹)
    hUQ (hRT.trans hTU) hself hinv hcover hsharp

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
