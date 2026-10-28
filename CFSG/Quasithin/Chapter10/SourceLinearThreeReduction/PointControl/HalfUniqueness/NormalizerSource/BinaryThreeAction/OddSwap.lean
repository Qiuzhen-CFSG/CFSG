module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddFull

/-!
# The original exchanger on the normal-closure quotient

Choose the moving element supplied by the original swapped-component input.
Multiplication of the two actual quotient factors gives product coordinates;
conjugation by this element carries the first factor to the second. The
centerless quasisimple product automorphism theorem therefore identifies
this same conjugation as a factor-exchanging automorphism. It preserves
the image of R = N_T(L) ∩ K because T normalizes its index-two stabilizer.

This retains the actual exchanger, factor inclusions and quotient maps
needed by the odd-prime index-two argument in Aschbacher--Smith 10.2.5,
printed p.748.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H P I : Subgroup G}

/-- The actual quotient image of R is preserved by a genuine factor exchange. -/
theorem Data.swapped_quotient_intersection (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G)) :
    ∃ (e : XiQuotient (enlargedResidual T L H) ≃* XiQuotient I × XiQuotient I)
      (a b : MulAut (XiQuotient I)),
      ((quotientImage (enlargedResidual T L H) (stabilizerIntersection T L H)).map
        e.toMonoidHom).map
          (a.prodCongr b * (MulEquiv.prodComm : MulAut (XiQuotient I × XiQuotient I))).toMonoidHom =
        (quotientImage (enlargedResidual T L H) (stabilizerIntersection T L H)).map e.toMonoidHom := by
  let hA := fun (Y : Type _) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremA_knownSimple (G := Y)
  let hC := fun (Y : Type _) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremC_knownSimple (G := Y)
  obtain ⟨hindex,hmodel⟩ := SwappedSylow.nonnormal_model_of_theoremsAC hA hC hs.toSwappedInput
  have hsimple := SwappedFactorsProof.quotient_simple hs.toSwappedInput hmodel
  let : IsQuasisimple (XiQuotient I) := hs.quasisimple
  have hz : center (XiQuotient I) = ⊥ := by
    let : IsSimpleGroup (XiQuotient I) := hsimple
    rcases (inferInstance : (center (XiQuotient I)).Normal).eq_bot_or_eq_top with hh | hh
    · exact hh
    · exact (Group.IsPerfect.not_isMulCommutative (XiQuotient I) (center_eq_top_iff.mp hh)).elim
  obtain ⟨t,ht,htn⟩ := hs.toSwappedInput.exists_swap
  obtain ⟨ec,hec⟩ := SwappedFactorsProof.quotient_product_coordinates
    ChapterA.Section03.CComponentCommutation.universal_A_3_7 hs.toSwappedInput
      hindex hsimple ht.1 htn
  have hc : ∃ e : quotientImage (enlargedResidual T L H) I ×
      quotientImage (enlargedResidual T L H) (I.conjBy t) ≃* XiQuotient (enlargedResidual T L H),
      ∀ a b, e (a,b) = (a : XiQuotient (enlargedResidual T L H)) * b :=
    hK.symm ▸ ⟨ec,hec⟩
  obtain ⟨c,hc⟩ := hc
  have ha : Nonempty (XiQuotient I ≃* quotientImage (enlargedResidual T L H) I) :=
    hK.symm ▸ ⟨SwappedFactorsProof.componentImageEquiv hs.toSwappedInput hs.component
      (le_componentOrbit I (T : Subgroup G))⟩
  obtain ⟨a⟩ := ha
  let ci : I ≃* I.conjBy t := equivMapOfInjective I (MulAut.conj t).toMonoidHom
    (MulAut.conj t).injective
  let cq : XiQuotient I ≃* XiQuotient (I.conjBy t) :=
    QuotientGroup.congr _ _ ci (pCore_map_iso 2 ci)
  have hb : Nonempty (XiQuotient I ≃* quotientImage (enlargedResidual T L H) (I.conjBy t)) :=
    hK.symm ▸ ⟨cq.trans (SwappedFactorsProof.componentImageEquiv hs.toSwappedInput
      (SwappedFactorsProof.conjugate_component hs.component ((le_sup_right.trans hs.overgroup) ht.1))
      (le_iSup (fun s : (T : Subgroup G) => I.conjBy s) ⟨t,ht.1⟩))⟩
  obtain ⟨b⟩ := hb
  let e : XiQuotient (enlargedResidual T L H) ≃* XiQuotient I × XiQuotient I :=
    c.symm.trans (a.symm.prodCongr b.symm)
  let tn : normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) :=
    ⟨t,stabilizer_normalized D hn ht.1⟩
  let f := quotientAction T L H tn
  let g : MulAut (XiQuotient I × XiQuotient I) := (MulAut.congr e) f
  have hmove : ∀ x ∈ quotientImage (enlargedResidual T L H) I,
      f x ∈ quotientImage (enlargedResidual T L H) (I.conjBy t) := by
    rintro x ⟨z,hz,rfl⟩
    rw [show f (QuotientGroup.mk' (pCore 2 (enlargedResidual T L H)) z) =
      QuotientGroup.mk' (pCore 2 (enlargedResidual T L H))
        ((enlargedResidual T L H).normalizerMonoidHom
          ⟨t,h.normalizer_normalizes_enlargedResidual tn.property⟩ z) from
      pCoreNormalizerAction_mk 2 _ _ _]
    exact mem_map_of_mem _ ⟨z,hz,rfl⟩
  have hfirst (x : XiQuotient I) : (g (x,1)).1 = 1 := by
    have he : e.symm (x,1) = (a x : XiQuotient (enlargedResidual T L H)) := by
      change c (a x,b 1) = _
      rw [map_one,hc]
      simp
    have hm := hmove _ (he.symm ▸ (a x).property)
    have he' : e (f (e.symm (x,1))) = e ((⟨_,hm⟩ : quotientImage (enlargedResidual T L H) (I.conjBy t)) :
        XiQuotient (enlargedResidual T L H)) := rfl
    have hcoord : e ((⟨_,hm⟩ : quotientImage (enlargedResidual T L H) (I.conjBy t)) :
        XiQuotient (enlargedResidual T L H)) = (1,b.symm ⟨_,hm⟩) := by
      apply e.symm.injective
      simp only [MulEquiv.symm_apply_apply]
      change _ = c (a 1,b (b.symm ⟨_,hm⟩))
      rw [map_one,MulEquiv.apply_symm_apply,hc]
      simp
    exact congrArg Prod.fst (he'.trans hcoord)
  obtain ⟨u,v,hg⟩ : ∃ u v : MulAut (XiQuotient I),
      g = u.prodCongr v * (MulEquiv.prodComm : MulAut (XiQuotient I × XiQuotient I)) := by
    rcases AutomorphismSquare.normal_form hz g with ⟨u,v,huv⟩ | hh
    · obtain ⟨x,hx⟩ := exists_ne (1 : XiQuotient I)
      have hh := hfirst x
      rw [huv] at hh
      exact (hx (u.injective (hh.trans u.map_one.symm))).elim
    · exact hh
  refine ⟨e,u,v,?_⟩
  rw [←hg,Subgroup.map_map]
  have heq : g.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp f.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change e (f (e.symm (e x))) = e (f x)
    rw [e.symm_apply_apply]
  rw [heq,←Subgroup.map_map,h.quotientAction_preserves_intersection tn]

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
