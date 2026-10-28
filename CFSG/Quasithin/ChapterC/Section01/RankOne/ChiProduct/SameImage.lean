module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.CentralizerKernel
public import CFSG.Quasithin.ChapterC.Section01.BlockBasics

public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Equality in the original C.1.27 groups

The ambient two-core normalizes a locally subnormal two-perfect seed.
Equality of centralizer-quotient images then expresses the lifted block as
the seed times its two-core. The seed is normal in this product, and
 two-perfection eliminates the two-group quotient. Thus the equality
alternative in B.1.13 gives equality of the original groups.

Source: Aschbacher--Smith C.1.27, printed pp.132--133.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The ambient two-core normalizes a locally subnormal two-perfect seed. -/
theorem local_twoPerfect_normalized_by_core
    (K H : Subgroup G) (hKH : K ≤ H) (hQH : pCore 2 G ≤ H)
    (hs : (K.subgroupOf H).IsSubnormal) (hp : IsPPerfect 2 K) :
    pCore 2 G ≤ normalizer K := by
  let A := K.subgroupOf H
  let P := (pCore 2 G).subgroupOf H
  have hpA : IsPPerfect 2 A := hp.of_surjective
    (subgroupOfEquivOfLe hKH).symm.toMonoidHom (subgroupOfEquivOfLe hKH).symm.surjective
  have hn := le_normalizer_of_isSubnormal_isPPerfect A P hs hpA
    (pCore_isPGroup (p := 2) (G := G)).comap_subtype le_normalizer_of_normal
  have hm := (map_mono (f := H.subtype) hn).trans (A.le_normalizer_map H.subtype)
  rwa [map_subgroupOf_eq_of_le hQH, map_subgroupOf_eq_of_le hKH] at hm

/-- Equality of the actual centralizer-quotient images gives equality of the
original two-perfect groups; no core extension is lost. -/
theorem eq_of_same_centralizer_image
    (V H K L : Subgroup G) [V.Normal]
    (hKH : K ≤ H) (hQH : pCore 2 G ≤ H)
    (hs : (K.subgroupOf H).IsSubnormal) (hpK : IsPPerfect 2 K)
    (hKL : K ≤ L) (hL : IsBlock L) (hU : (blockU L).map L.subtype ≤ V)
    (hQC : pCore 2 G ≤ centralizer (V : Set G))
    (he : K.map (QuotientGroup.mk' (centralizer (V : Set G))) =
      L.map (QuotientGroup.mk' (centralizer (V : Set G)))) : K = L := by
  let q := QuotientGroup.mk' (centralizer (V : Set G))
  let f := q.subgroupMap L
  let A := K.subgroupOf L
  have hf : A.map f = ⊤ := by
    apply map_injective (L.map q).subtype_injective
    have hh : (L.map q).subtype.comp f = q.comp L.subtype := rfl
    rw [map_map,hh,← map_map,map_subgroupOf_eq_of_le hKL,
      ← MonoidHom.range_eq_map,range_subtype]
    exact he
  have hker : f.ker = pCore 2 L :=
    core_eq_centralizer_quotient_kernel V L hL.subnormal hL.short.fitting hU hQC
  have hsup : A ⊔ pCore 2 L = ⊤ := by
    rw [← hker, ← comap_map_eq, hf, comap_top]
  have hLN : L ≤ normalizer K := by
    have hm := congrArg (map L.subtype) hsup
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hKL,← MonoidHom.range_eq_map,range_subtype] at hm
    rw [← hm]
    exact sup_le K.le_normalizer
      ((pCoreIn_le_of_subnormal 2 hL.subnormal).trans
        (local_twoPerfect_normalized_by_core K H hKH hQH hs hpK))
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer hKL).mpr hLN
  have ht : (⊤ : Subgroup L) ≤ A := by
    have hh : pResidual 2 L ≤ A := sInf_le ⟨inferInstance,
      isPGroup_quotient_of_sup_eq_top A (pCore 2 L) pCore_isPGroup hsup⟩
    rwa [(pResidual_eq_top_iff 2 L).mpr hL.short.twoPerfect] at hh
  have hm := congrArg (map L.subtype) (top_unique ht)
  rwa [map_subgroupOf_eq_of_le hKL,← MonoidHom.range_eq_map,range_subtype] at hm

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct
