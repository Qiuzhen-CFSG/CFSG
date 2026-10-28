module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.Cases
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.Reductions
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.SymmetricEight.Permutation
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.SymmetricEight.Transport

/-!
# The symmetric-eight transposition contradiction

This proves case (II) of the order-two argument. In the contrary order-four
branch, the actual action identifies R with the full residual centralizer.
The two-perfect residual fixes the two unused points of the marked
triple transposition, so their transposition lifts to an outer involution
s in R. A three-cycle in the residual of its centralizer does not commute
with the original actor, contradicting the earlier residual transfer.

The residual is transported through L/Z(L) with its central two-group
kernel retained. Neither a transposition witness nor the noncommutation
calculation is an additional premise. The cardinality-four hypothesis alone
suffices; the accompanying elementary-abelian hypothesis is unnecessary here.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
Lemma 16.4.9(1), printed p.1189, case (II).
-/

@[expose] public section

open Subgroup Theory.GroupTheory Equiv Equiv.Perm
namespace CFSG.Quasithin.Chapter16.Intersections.OrderTwo
open OuterResidual
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
namespace SymmetricEight
open Transport
abbrev S8 := Perm (Fin 8)

omit [Finite G] in
private theorem actionImage_sup_le_component :
    actionImage L (centralizer (L : Set G) ⊔ L) ≤ actionImage L L := by
  have hC : actionImage L (centralizer (L : Set G)) ≤ (⊥ : Subgroup (ActionQuotient L)) := by
    rintro _ ⟨a, ha, rfl⟩
    have ha1 : quotientMap L a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
    simp [ha1]
  rw [actionImage, Subgroup.subgroupOf_sup (centralizer_le_normalizer _) le_normalizer,
    Subgroup.map_sup]
  exact sup_le (by simpa only [actionImage] using hC.trans bot_le) le_rfl

private theorem actionElement_mem_full
    (h : IntersectionSetup T z L g R) {s : G} (hs : s ∈ R) :
    actionElement L s (h.sylow_normalizes (h.le_sylow hs)) ∈
      actionImage L (L ⊔ (T : Subgroup G)) :=
  mem_actionImage (h.sylow_normalizes (h.le_sylow hs))
    ((le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)) (h.le_sylow hs))

private theorem normalized_tailSwap_mem
    (h : IntersectionSetup T z L g R) (f : B L T ≃* S8)
    {r : G} (hr : r ∈ R) (hfr : elementMark h f hr = Permutation.triple) :
    (f.symm Permutation.tailSwap : ActionQuotient L) ∈ residualCentralizer L r := by
  let D := involutionResidual L r
  let φ := residualMark f r
  have hp : IsPPerfect 2 φ.range :=
    (isPPerfect_embedded_pResidual 2 (ComponentTransfer.centralizerIn L r)).of_surjective
      φ.rangeRestrict φ.rangeRestrict_surjective
  have hP : φ.range ≤ centralizer ({Permutation.triple} : Set S8) := by
    rintro _ ⟨x, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    rw [← hfr]
    exact residualMark_commutes h f hr x
  have htail := Permutation.tailSwap_centralizes_twoPerfect φ.range hp hP
  apply mem_centralizer_iff.mpr
  rintro _ ⟨x, hx, rfl⟩
  let d : D := ⟨x, hx⟩
  have hdN := (involutionResidual_le L r hx).1
  let dStar : B L T := ⟨quotientMap L x,
    mem_actionImage x.property
      ((le_sup_left : L ≤ L ⊔ (T : Subgroup G)) hdN)⟩
  have he := mem_centralizer_iff.mp htail (φ d) ⟨d, rfl⟩
  change f dStar * Permutation.tailSwap = Permutation.tailSwap * f dStar at he
  have he' : dStar * f.symm Permutation.tailSwap = f.symm Permutation.tailSwap * dStar := by
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using he
  exact congrArg Subtype.val he'

/-- The S₈ branch of 16.4.9(1), from the actual marking and residual transfer. -/
theorem card_two
    {𝒦 : GroupClass} (hG : Hypothesis1611 𝒦 G)
    (h : IntersectionSetup T z L g R) {r : G}
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hrout : r ∉ centralizer (L : Set G) ⊔ L)
    (htransfer : OuterResidualTransfer L g R)
    (hcase : SymmetricEightCase T L r)
    (hc : Nat.card (residualCentralizer L r) = 4) : Nat.card R = 2 := by
  have hres := htransfer r hr hr2 hrout
  rcases card_two_or_four_of_residualCentralizer_card_four h hr hr2 hres hc with htwo | hfour
  · exact htwo
  exfalso
  obtain ⟨e, he, hrN, rStar, hrStar, hcycle⟩ := hcase
  let q := Permutation.triple
  have hconj : IsConj (e rStar) q := by
    apply isConj_iff_cycleType_eq.mpr
    exact hcycle.trans Theory.SpecificGroups.SymmetricEight.Involutions.threePairs_cycleType.symm
  obtain ⟨c, hce⟩ := isConj_iff.mp hconj
  let f := e.trans (MulAut.conj c)
  have hfq : f rStar = q := hce
  have hfr : elementMark h f hr = q := by
    change f _ = q
    rw [← hfq]
    exact congrArg f (Subtype.ext hrStar.symm)
  have hfEven : ((actionImage L L).subgroupOf
      (actionImage L (L ⊔ (T : Subgroup G)))).map f.toMonoidHom =
        alternatingGroup (Fin 8) := by
    change ((actionImage L L).subgroupOf
      (actionImage L (L ⊔ (T : Subgroup G)))).map
        ((MulAut.conj c).toMonoidHom.comp e.toMonoidHom) = _
    rw [← map_map, he]
    exact Subgroup.Normal.map_conj_eq _ c
  let sStar := f.symm Permutation.tailSwap
  have hfs : f sStar = Permutation.tailSwap := f.apply_symm_apply _
  let E := residualCentralizerEquiv h hres (hfour.trans hc.symm)
  have hsCmem : sStar.val ∈ residualCentralizer L r := normalized_tailSwap_mem h f hr hfr
  let sC : residualCentralizer L r := ⟨sStar.val, hsCmem⟩
  let sR := E.symm sC
  let s : G := sR.val
  have hs : s ∈ R := sR.property
  have hEs : E sR = sC := E.apply_symm_apply _
  have hsAction : actionElement L s
      (h.sylow_normalizes (h.le_sylow hs)) = sStar.val := by
    exact congrArg Subtype.val hEs
  have hsMarked : elementMark h f hs = Permutation.tailSwap := by
    change f _ = _
    rw [← hfs]
    exact congrArg f (Subtype.ext hsAction)
  have hs2 : orderOf s = 2 := by
    have horderStar : orderOf sStar = 2 := by
      have horderF : orderOf (f sStar) = 2 := by
        rw [hfs]
        exact Permutation.tailSwap_order
      exact (f.orderOf_eq sStar).symm.trans horderF
    have horderE : orderOf (E sR) = 2 := by
      rw [hEs]
      have horderC : orderOf sC = orderOf sStar := by
        calc
          orderOf sC = orderOf (sC : ActionQuotient L) :=
            (Subgroup.orderOf_coe sC).symm
          _ = orderOf (sStar : ActionQuotient L) := rfl
          _ = orderOf sStar := Subgroup.orderOf_coe sStar
      exact horderC.trans horderStar
    have horderSR : orderOf sR = 2 := (E.orderOf_eq sR).symm.trans horderE
    exact (Subgroup.orderOf_coe sR).trans horderSR
  have hsout : s ∉ centralizer (L : Set G) ⊔ L := by
    intro hsin
    have hi : actionElement L s (h.sylow_normalizes (h.le_sylow hs)) ∈ actionImage L L :=
      actionImage_sup_le_component (mem_actionImage (h.sylow_normalizes (h.le_sylow hs)) hsin)
    have hm : Permutation.tailSwap ∈ alternatingGroup (Fin 8) := by
      rw [← hfEven]
      exact ⟨⟨actionElement L s (h.sylow_normalizes (h.le_sylow hs)),
        actionElement_mem_full h hs⟩, hi, hsMarked⟩
    exact Permutation.tailSwap_not_even hm
  have hsres := htransfer s hs hs2 hsout
  have hcomm : Permutation.cubic * elementMark h f hs =
      elementMark h f hs * Permutation.cubic := by
    rw [hsMarked]
    exact Permutation.cubic_commutes_tailSwap
  obtain ⟨d, hd⟩ := exists_residual_preimage hG h f hfEven hs
    Permutation.cubic Permutation.cubic_even hcomm
    (by rw [Permutation.cubic_order]; decide)
  have hrC : actionElement L r (h.sylow_normalizes (h.le_sylow hr)) ∈
      residualCentralizer L s :=
    actionMap_mem_residualCentralizer (h.le_sylow.trans h.sylow_normalizes)
      (centralizes_residual h hsres) ⟨r, hr⟩
  have hdL := (involutionResidual_le L s d.property).1
  let dStar : B L T := ⟨actionElement L d (le_normalizer hdL),
    mem_actionImage (le_normalizer hdL)
      ((le_sup_left : L ≤ L ⊔ (T : Subgroup G)) hdL)⟩
  have hrd : dStar * rStar = rStar * dStar := by
    apply Subtype.ext
    change dStar.val * rStar.val = rStar.val * dStar.val
    have hcc := mem_centralizer_iff.mp hrC dStar.val
      (mem_actionImage (le_normalizer hdL) d.property)
    simpa only [hrStar] using hcc
  have hm := congrArg f hrd
  have hfd : f dStar = Permutation.cubic := hd
  have hbad : Permutation.cubic * q = q * Permutation.cubic := by
    simpa only [map_mul, hfq, hfd] using hm
  exact Permutation.cubic_not_commutes_triple hbad

end SymmetricEight
end CFSG.Quasithin.Chapter16.Intersections.OrderTwo
