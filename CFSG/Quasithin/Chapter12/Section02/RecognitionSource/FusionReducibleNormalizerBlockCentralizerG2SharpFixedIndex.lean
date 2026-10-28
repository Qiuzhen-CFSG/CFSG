module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerG2Factorization
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.G2JoinFixedIndex

/-!
# The sharp moved fixed-index input in source 3.3.28

A Sylow-normalizer conjugate of the intrinsic elementary layer U(L) lies
in T. Its full G₂ actor therefore supplies the sharp fixed-index bound
needed by the first core factorization. The actual consumer below removes
that premise and retains only the separate moved-centralizer cover.

Source: Aschbacher–Smith 3.3.28, printed p.601. The central kernel of the
intrinsic natural quotient is retained throughout.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The conjugate intrinsic layer satisfies the sharp bound solely from
the block and Sylow-normalizer hypotheses. -/
theorem g2Two_moved_sharp_fixed_index
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsG2TwoBlock L) {d : G} (hd : d ∈ normalizer (T : Set G)) :
    ((L ⊔ (T : Subgroup G)).pCoreIn 2).relIndex
      (((ChapterC.blockU L).map L.subtype).map (MulAut.conj d⁻¹).toMonoidHom) ≤
        (centralizer (((ChapterC.blockU L).map L.subtype).map
          (MulAut.conj d⁻¹).toMonoidHom : Set G)).relIndex ((ChapterC.blockU L).map L.subtype) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let U := (ChapterC.blockU L).map L.subtype
  let B := U.map (MulAut.conj d⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 U := hb.short.elementary.map L.subtype
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Q, Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hUQ : U ≤ Q := (map_mono ChapterC.blockU_le_core).trans
    (pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer hTL))
  have hBT : B ≤ (T : Subgroup G) := by
    have hm := map_mono (f := (MulAut.conj d⁻¹).toMonoidHom) (hUQ.trans hQT)
    have he : (T : Subgroup G).map (MulAut.conj d⁻¹).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (T : Set G)).inv_mem hd)
    exact hm.trans he.le
  exact ChapterC.G2BlockAction.elementary_actor_sharp_fixed_index hTL hb B
    (hBT.trans le_sup_right)

/-- The first source core factorization no longer requires a supplied
sharp fixed-index bound; only the independent moved-cover premise remains. -/
theorem g2Two_local_core_factorization_of_moved_cover
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hb : ChapterC.IsG2TwoBlock L) {d : G} (hd : d ∈ normalizer (T : Set G))
    (hcover : blockLocalCore T L ⊓ centralizer
      (((ChapterC.blockU L).map L.subtype).map (MulAut.conj d⁻¹).toMonoidHom : Set G) ≤
        ((ChapterC.blockU L).map L.subtype).map (MulAut.conj d⁻¹).toMonoidHom ⊔
          (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 = (ChapterC.blockU L).map L.subtype ⊔
      ((L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer
        (((ChapterC.blockU L).map L.subtype).map (MulAut.conj d⁻¹).toMonoidHom : Set G)) :=
  g2Two_local_core_factorization_of_moved_fixed_index h D hfixed hb hd hcover
    (g2Two_moved_sharp_fixed_index D.sylow_normalizes_component hb hd)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
