module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallFull
public import Theory.SpecificGroups.PSL2.SmallSylowRadical

/-!
# The radical in the final small-congruence enlargement

An actual T-invariant subgroup descends through the same quotient and the
same component exchanger. Applied to O₂(X), its commutator generation by
the original cubic complement gives either a trivial image or the full
quotient Sylow. In the latter case the normalizer has order 144 and equals
the original parabolic intersection image. Its two-residual is the image
of X, so preservation lifts to the original residual.

Source: Aschbacher--Smith 10.2.5, printed p.748. The radical-collapse case
is retained explicitly; its exclusion and final source assembly remain
with qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt is the only external
source input, finally discharged by qt-d-10-nona5-point-control.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H P I : Subgroup G}

/-- Every original T-invariant subgroup is preserved by the same genuine factor exchange. -/
theorem Data.swapped_quotient_subgroup (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    (A : Subgroup G) (hTA : (T : Subgroup G) ≤ normalizer (A : Set G)) :
    ∃ (e : XiQuotient (enlargedResidual T L H) ≃* XiQuotient I × XiQuotient I)
      (a b : MulAut (XiQuotient I)),
      ((quotientImage (enlargedResidual T L H) A).map
        e.toMonoidHom).map
          (a.prodCongr b * (MulEquiv.prodComm : MulAut (XiQuotient I × XiQuotient I))).toMonoidHom =
        (quotientImage (enlargedResidual T L H) A).map e.toMonoidHom := by
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
  have hfix : (quotientImage (enlargedResidual T L H) A).map f.toMonoidHom =
      quotientImage (enlargedResidual T L H) A :=
    pCoreNormalizerAction_preserves_image 2 _ _ _ (hTA ht.1)
  rw [heq,←Subgroup.map_map,hfix]

/-- The original core commutator identity descends through the literal K/O₂(K). -/
theorem Data.quotient_core_commutator (h : Data D H)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H)) :
    ⁅quotientImage (enlargedResidual T L H) ((residual H).pCoreIn 2),
      quotientImage (enlargedResidual T L H) P⁆ =
      quotientImage (enlargedResidual T L H) ((residual H).pCoreIn 2) := by
  let K := enlargedResidual T L H
  let C := (residual H).pCoreIn 2
  have hCK : C ≤ K := (pCoreIn_le 2 _).trans h.residual_le_enlargedResidual
  have hPK : P ≤ K := hi.complement_le.trans h.residual_le_enlargedResidual
  have hc : ⁅C.subgroupOf K,P.subgroupOf K⁆ = C.subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hCK,map_subgroupOf_eq_of_le hPK]
    exact hi.core_commutator.symm
  change ⁅(C.subgroupOf K).map _,(P.subgroupOf K).map _⁆ = (C.subgroupOf K).map _
  rw [←map_commutator,hc]

/-- The actual exchanged radical is either killed by O₂(K) or fills the
entire quotient Sylow. No positive-radical source premise is assumed. -/
theorem Data.quotient_core_eq_bot_or_sylow (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 8 = 3 ∨ p % 8 = 5) :
    quotientImage (enlargedResidual T L H) ((residual H).pCoreIn 2) = ⊥ ∨
      quotientImage (enlargedResidual T L H) ((residual H).pCoreIn 2) =
        quotientImage (enlargedResidual T L H) (T : Subgroup G) := by
  have hTC : (T : Subgroup G) ≤ normalizer ((residual H).pCoreIn 2 : Set G) :=
    hs.invariant.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  obtain ⟨e,a,b,hswap⟩ := h.swapped_quotient_subgroup hn hs hK ((residual H).pCoreIn 2) hTC
  obtain ⟨S,hS⟩ := h.quotient_sylow
  have hpc := hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))
  have hep : Nonempty (P ≃* quotientImage (enlargedResidual T L H) P) := by
    change Nonempty (P ≃* (P.subgroupOf (enlargedResidual T L H)).map _)
    rw [hK]
    exact ⟨SwappedSylow.quotientComplementEquiv hs.toSwappedInput⟩
  obtain ⟨ep⟩ := hep
  have hcard : Nat.card (quotientImage (enlargedResidual T L H) P) = 9 :=
    (Nat.card_congr ep.toEquiv).symm.trans hpc.2
  have hUS : quotientImage (enlargedResidual T L H) ((residual H).pCoreIn 2) ≤
      (S : Subgroup (XiQuotient (enlargedResidual T L H))) := by
    rw [hS]
    exact map_mono (subgroupOf_mono _ hs.toLocalInput.core_le_two_group)
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p,1,hp,ho,by decide,by simpa using hF⟩
  have h8 := Theory.PSL2.not_eight_dvd_card_of_small_mod_eight (hF ▸ ho) (hF ▸ hmod)
  have hh := Theory.PSL2.small_pair_radical_eq_or_bot eF e hodd h8 S
    (quotientImage (enlargedResidual T L H) ((residual H).pCoreIn 2))
    (quotientImage (enlargedResidual T L H) P) hUS
    (hs.odd_complement.isPGroup.of_equiv ep) hcard (h.quotient_core_commutator hs.toLocalInput)
    (SylowNormalizerAction.projection_card_eq_of_swapped _ a b hswap)
  rwa [hS] at hh

/-- Once the original radical survives, the small-congruence full-intersection
normalizer preserves the original O²(H). The remaining zero-image case is explicit. -/
theorem Data.normalizes_residual_of_odd_small_full_positive (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 8 = 3 ∨ p % 8 = 5)
    (hR : stabilizerIntersection T L H = (T : Subgroup G) ⊓ enlargedResidual T L H)
    (hpos : quotientImage (enlargedResidual T L H) ((residual H).pCoreIn 2) ≠ ⊥) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H : Set G) := by
  have hfull := (h.quotient_core_eq_bot_or_sylow hn hs hK hp ho hm hmod).resolve_left hpos
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  obtain ⟨S,hS⟩ := h.quotient_sylow
  let A := quotientImage (enlargedResidual T L H) P
  have hpc := hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))
  have hep : Nonempty (P ≃* A) := by
    change Nonempty (P ≃* (P.subgroupOf (enlargedResidual T L H)).map _)
    rw [hK]
    exact ⟨SwappedSylow.quotientComplementEquiv hs.toSwappedInput⟩
  obtain ⟨ep⟩ := hep
  have hcard : Nat.card A = 9 := (Nat.card_congr ep.toEquiv).symm.trans hpc.2
  have hcomm := h.quotient_core_commutator hs.toLocalInput
  rw [hfull,←hS] at hcomm
  have hAN : A ≤ normalizer (S : Set (XiQuotient (enlargedResidual T L H))) :=
    le_normalizer_iff_commutator_le_left.mpr hcomm.le
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p,1,hp,ho,by decide,by simpa using hF⟩
  have h8 := Theory.PSL2.not_eight_dvd_card_of_small_mod_eight (hF ▸ ho) (hF ▸ hmod)
  have hnormal := Theory.PSL2.small_pair_normalizer_eq_join (e.trans (eF.prodCongr eF))
    hodd h8 S A (hs.odd_complement.isPGroup.of_equiv ep) hcard hAN
  have hres : (pResidual 2 (normalizer (S : Set (XiQuotient (enlargedResidual T L H))))).map
      (normalizer (S : Set (XiQuotient (enlargedResidual T L H)))).subtype =
        quotientImage (enlargedResidual T L H) (residual H) := by
    rw [hnormal,hS]
    change (pResidual 2 (quotientImage _ P ⊔ quotientImage _ (T : Subgroup G) :
      Subgroup (XiQuotient (enlargedResidual T L H)))).map _ = _
    rw [h.quotient_complement_join hs.toLocalInput]
    exact h.quotient_parabolic_residual
  have hRS : quotientImage (enlargedResidual T L H) (stabilizerIntersection T L H) =
      (S : Subgroup (XiQuotient (enlargedResidual T L H))) := by
    rw [hS]
    unfold quotientImage
    rw [hR,inf_subgroupOf_right]
  apply h.normalizes_residual_of_quotientAction
  intro g
  have hfix := h.quotientAction_preserves_intersection g
  rw [hRS] at hfix
  have hnmap : (normalizer (S : Set (XiQuotient (enlargedResidual T L H)))).map
      (quotientAction T L H g).toMonoidHom =
      normalizer (S : Set (XiQuotient (enlargedResidual T L H))) := by
    have hh := map_equiv_normalizer_eq
      (S : Subgroup (XiQuotient (enlargedResidual T L H))) (quotientAction T L H g)
    rw [hfix] at hh
    exact hh
  rw [←hres,map_embedded_pResidual,hnmap]

/-- Triviality of the radical image means containment in the actual O₂(K),
not vanishing of the original radical. -/
theorem Data.quotient_core_eq_bot_iff (h : Data D H) :
    quotientImage (enlargedResidual T L H) ((residual H).pCoreIn 2) = ⊥ ↔
      (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2 := by
  let K := enlargedResidual T L H
  let C := (residual H).pCoreIn 2
  have hCK : C ≤ K := (pCoreIn_le 2 _).trans h.residual_le_enlargedResidual
  change (C.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) = ⊥ ↔ C ≤ K.pCoreIn 2
  rw [Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  constructor
  · intro hh x hx
    exact ⟨⟨x,hCK hx⟩,hh hx,rfl⟩
  · intro hh x hx
    obtain ⟨y,hy,he⟩ := hh hx
    have he' : y = x := Subtype.ext he
    exact he' ▸ hy

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
