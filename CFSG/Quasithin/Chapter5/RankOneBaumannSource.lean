module

public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Theory.GroupTheory.ReducedNormal.QuasisimpleKernel
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Stellmacher.BaumannNormalizer
public import Theory.GroupTheory.NormalClosureCentralizerCore
public import Theory.ElementaryAbelian.Injective

/-!
# The centralizing branch and normalizer obstruction in source 5.1.7

A reduced noncentral module detects the two-core of the rank-one Sylow
join. When the Thompson subgroup centralizes that module, Baumann heredity
makes Baum(T) normal in the join, and source 1.2.7 controls its normalizer.
The same uniqueness supplies the C.6.2 and E.2.3 obstruction on every
nontrivial subgroup of Baum(T) normal in LT.

These prove the centralizing branch and prepare the other two branches;
they do not assert the full normalizer bound without case analysis.
Source: Aschbacher--Smith 5.1.1--2 and 5.1.7(1), pp.630,633--634.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter5.RankOneBaumannSource
open ChapterB Stellmacher
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G}

theorem unique_sylow_join
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : L ∈ Chapter1.LStar G (T : Subgroup G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N →
      N = normalizer (L : Set G) := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple hG T hL
  have he : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl hTL)
      (le_componentOrbit L T)
  simpa only [he] using hu.normalizer_unique

omit [Finite G] in
theorem reduced_sylow_centralizer
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hW : W ≤ L ⊔ (T : Subgroup G))
    (hr : IsPReduced 2 (W.subgroupOf (L ⊔ (T : Subgroup G))))
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hm : ⁅W,L⁆ ≠ ⊥) :
    (T : Subgroup G) ⊓ centralizer (W : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let J := L ⊔ (T : Subgroup G)
  let K := L.subgroupOf J
  let U := W.subgroupOf J
  have hUW : U.map J.subtype = W := map_subgroupOf_eq_of_le hW
  let : U.Normal := hr.normal
  let : K.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hTL)
  let e : K ≃* L := subgroupOfEquivOfLe le_sup_left
  let eqv : (K ⧸ pCore 2 K) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv eqv.symm
  have hzK : center (K ⧸ pCore 2 K) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact eqv.map_eq_one_iff.mp (hz.le ((centerCongr eqv) ⟨x,hx⟩).property)
  have hmK : ⁅U,K⁆ ≠ ⊥ := by
    intro he
    apply hm
    have hh := congrArg (map J.subtype) he
    simpa only [K, map_commutator, hUW,
      map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left), Subgroup.map_bot] using hh
  have hgen : K ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup (show L ≤ J from le_sup_left) le_sup_right, subgroupOf_self]
  have hc := reduced_quasisimple_centralizer_eq_pCore U K hr hzK hmK
    (isPGroup_quotient_of_sup_eq_top K ((T : Subgroup G).subgroupOf J)
      T.isPGroup'.comap_subtype hgen)
  have he : J ⊓ centralizer (W : Set G) = J.pCoreIn 2 := by
    have hh := congrArg (map J.subtype) hc
    simpa only [map_centralizer_subtype, hUW, pCoreIn] using hh
  have hQT : J.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow J (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  exact le_antisymm ((inf_le_inf_right _ le_sup_right).trans_eq he)
    (le_inf hQT (he.symm.le.trans inf_le_right))

theorem baumann_normalizer_of_thompson_centralizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : L ∈ Chapter1.LStar G (T : Subgroup G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hW : W ≤ L ⊔ (T : Subgroup G))
    (hr : IsPReduced 2 (W.subgroupOf (L ⊔ (T : Subgroup G))))
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hm : ⁅W,L⁆ ≠ ⊥)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G)) :
    normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  let J := L ⊔ (T : Subgroup G)
  have hWT : W ≤ (T : Subgroup G) := by
    have hh := map_mono (f := J.subtype) hr.le_pCore
    rw [map_subgroupOf_eq_of_le hW] at hh
    exact hh.trans ((pCoreIn_le_sylow J (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right))
  have hWe : IsElementaryAbelian 2 W := by
    let := hr.elementary
    exact IsElementaryAbelian.of_injective (subgroupOfEquivOfLe hW).symm.toMonoidHom
      (subgroupOfEquivOfLe hW).symm.injective
  let := hWe
  have he : baumann (T : Subgroup G) = baumann (J.pCoreIn 2) := by
    rw [lemma_B_2_3_5 (T : Subgroup G) W hWT hJ,
      reduced_sylow_centralizer hTL hW hr hz hm]
  have hn : J ≤ normalizer (baumann (T : Subgroup G) : Set G) := by
    rw [he]
    exact (J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J))).trans
        (normalizer_le_normalizer_baumann _)
  have hWB : W ≤ baumann (T : Subgroup G) :=
    le_inf hWT ((le_centralizer_iff.mp hJ).trans
      (centralizer_le (map_subtype_le _)))
  apply normalizer_le_of_unique_maximalTwoLocal (unique_sylow_join hG hL hTL)
    (T.isPGroup'.to_le inf_le_left) _ hn
  intro hb
  have hWb : W = ⊥ := bot_unique (hWB.trans_eq hb)
  exact hm (by rw [hWb, commutator_bot_left])

theorem normalizer_obstruction_of_baumann_escape
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : L ∈ Chapter1.LStar G (T : Subgroup G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (Q : Subgroup G) (hne : Q ≠ ⊥) (hQB : Q ≤ baumann (T : Subgroup G))
    (hn : L ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G)) :
    ¬ normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (Q : Set G) := by
  intro hN
  exact hout (hN.trans (normalizer_le_of_unique_maximalTwoLocal
    (unique_sylow_join hG hL hTL) (T.isPGroup'.to_le (hQB.trans inf_le_left)) hne hn))

theorem characteristic_baumann_eq_bot_of_escape
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : L ∈ Chapter1.LStar G (T : Subgroup G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (D : Subgroup (baumann (T : Subgroup G))) (hD : D.Characteristic)
    (hn : ((D.map (baumann (T : Subgroup G)).subtype).subgroupOf
      (L ⊔ (T : Subgroup G))).Normal) : D = ⊥ := by
  let := hD
  by_contra hne
  exact normalizer_obstruction_of_baumann_escape hG hL hTL hout _
    (fun he => hne ((D.map_eq_bot_iff_of_injective
      (baumann (T : Subgroup G)).subtype_injective).mp he)) (map_subtype_le _)
    ((normal_subgroupOf_iff_le_normalizer
      ((map_subtype_le D).trans (inf_le_left.trans le_sup_right))).mp hn)
    (normalizer_le_normalizer_characteristic_image _ D)

end CFSG.Quasithin.Chapter5.RankOneBaumannSource
