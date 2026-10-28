module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Swapped.Binary
public import Theory.SpecificGroups.PSL2.SwappedSylowNormalizer
public import Theory.SpecificGroups.PSL2.SmallSylowNormalizer
public import Theory.SpecificGroups.SL2.SmallOddComparisons

/-!
# Odd-prime normalizer actions on the actual swapped component orbit

An element of the original Sylow exchanging the components induces a
literal exchange on their quotient product. It preserves every subgroup
normalized by T, in particular the marked point-Sylow image. Its index
at most two forces both coordinate projections to be full Sylows.
For p congruent to one or seven modulo eight, their self-normalization
makes the original interval-normalizer action a two-group. The same holds
for a proper half-Sylow in the other congruences. The ambient Sylow T
induces the entire action image and already normalizes X. Perfect residual
lifting therefore recovers normalization of X in the original group.

The actual source application leaves only p congruent to three or five
modulo eight and full quotient Sylow intersection. It retains the original
MS fixed-subgroup premise; `qt-rank-two-ms93` supplies its ambient source
specialization, with earlier inputs from `qt-d-double-natural-centralizers`.
The remaining swapped case and final pure fusion/closure stay with this task.
The coordinate proof adapts BinaryThreeAction/OddSmallRadical and the
normalizer calculation adapts OddLarge and OddSmallHalf, with H and U
now the original pure-point overgroup and point Sylow.
Source: Aschbacher--Smith 12.1.4, pp.790--791; the intrinsic two-factor
normalizer arguments also occur in 10.2.5, p.748.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
open Chapter1 Chapter1.XiEmbedding InvariantThree
variable {G : Type*} [Group G] [Finite G]

/-- An original Sylow-invariant subgroup is preserved by a genuine exchange
of the two factors in the literal component-orbit quotient. -/
theorem swapped_quotient_subgroup (T : Sylow 2 G) {X A H I : Subgroup G}
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X A H I)
    (U : Subgroup G) (hTU : (T : Subgroup G) ≤ normalizer (U : Set G)) :
    ∃ (e : XiQuotient (componentOrbit I (T : Subgroup G)) ≃* XiQuotient I × XiQuotient I)
      (a b : MulAut (XiQuotient I)),
      ((quotientImage (componentOrbit I (T : Subgroup G)) U).map e.toMonoidHom).map
        (a.prodCongr b * (MulEquiv.prodComm : MulAut (XiQuotient I × XiQuotient I))).toMonoidHom =
      (quotientImage (componentOrbit I (T : Subgroup G)) U).map e.toMonoidHom := by
  let K := componentOrbit I (T : Subgroup G)
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
  have hc : ∃ e : quotientImage K I ×
      quotientImage K (I.conjBy t) ≃* XiQuotient K,
      ∀ a b, e (a,b) = (a : XiQuotient K) * b :=
    ⟨ec,hec⟩
  obtain ⟨c,hc⟩ := hc
  have ha : Nonempty (XiQuotient I ≃* quotientImage K I) :=
    ⟨SwappedFactorsProof.componentImageEquiv hs.toSwappedInput hs.component
      (le_componentOrbit I (T : Subgroup G))⟩
  obtain ⟨a⟩ := ha
  let ci : I ≃* I.conjBy t := equivMapOfInjective I (MulAut.conj t).toMonoidHom
    (MulAut.conj t).injective
  let cq : XiQuotient I ≃* XiQuotient (I.conjBy t) :=
    QuotientGroup.congr _ _ ci (pCore_map_iso 2 ci)
  have hb : Nonempty (XiQuotient I ≃* quotientImage K (I.conjBy t)) :=
    ⟨cq.trans (SwappedFactorsProof.componentImageEquiv hs.toSwappedInput
      (SwappedFactorsProof.conjugate_component hs.component ((le_sup_right.trans hs.overgroup) ht.1))
      (le_iSup (fun s : (T : Subgroup G) => I.conjBy s) ⟨t,ht.1⟩))⟩
  obtain ⟨b⟩ := hb
  let e : XiQuotient K ≃* XiQuotient I × XiQuotient I :=
    c.symm.trans (a.symm.prodCongr b.symm)
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hs.overgroup
  have hKH : K ≤ H := SwappedSylow.orbit_le_overgroup hs.toSwappedInput
  have hHK : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp hs.orbit_normal
  let tn : normalizer (K : Set G) := ⟨t,hHK (hTH ht.1)⟩
  let f := pCoreNormalizerAction 2 K tn
  let g : MulAut (XiQuotient I × XiQuotient I) := (MulAut.congr e) f
  have hmove : ∀ x ∈ quotientImage K I,
      f x ∈ quotientImage K (I.conjBy t) := by
    rintro x ⟨z,hz,rfl⟩
    rw [show f (QuotientGroup.mk' (pCore 2 K) z) =
      QuotientGroup.mk' (pCore 2 K)
        (K.normalizerMonoidHom
          tn z) from
      pCoreNormalizerAction_mk 2 _ _ _]
    exact mem_map_of_mem _ ⟨z,hz,rfl⟩
  have hfirst (x : XiQuotient I) : (g (x,1)).1 = 1 := by
    have he : e.symm (x,1) = (a x : XiQuotient K) := by
      change c (a x,b 1) = _
      rw [map_one,hc]
      simp
    have hm := hmove _ (he.symm ▸ (a x).property)
    have he' : e (f (e.symm (x,1))) = e ((⟨_,hm⟩ : quotientImage K (I.conjBy t)) :
        XiQuotient K) := rfl
    have hcoord : e ((⟨_,hm⟩ : quotientImage K (I.conjBy t)) :
        XiQuotient K) = (1,b.symm ⟨_,hm⟩) := by
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
  have hfix : (quotientImage K U).map f.toMonoidHom =
      quotientImage K U :=
    pCoreNormalizerAction_preserves_image 2 _ _ _ (hTU ht.1)
  rw [heq,←Subgroup.map_map,hfix]


/-- The original interval normalizer preserves the residual in the large
odd congruences, and in both small congruences when its quotient index is two. -/
theorem normalizes_of_odd_swapped_interval (T : Sylow 2 G) {X A H I U : Subgroup G}
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X A H I)
    (hUT : U ≤ (T : Subgroup G)) (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hi : U.relIndex (T : Subgroup G) ≤ 2)
    (hcore : (X ⊔ (T : Subgroup G)).pCoreIn 2 ≤ U)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hcase : (p % 8 = 1 ∨ p % 8 = 7) ∨
      quotientImage (componentOrbit I (T : Subgroup G)) U ≠
        quotientImage (componentOrbit I (T : Subgroup G)) (T : Subgroup G)) :
    H ⊓ normalizer (U : Set G) ≤ normalizer (X : Set G) := by
  let K := componentOrbit I (T : Subgroup G)
  have hKH : K ≤ H := SwappedSylow.orbit_le_overgroup hs.toSwappedInput
  have hHK : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp hs.orbit_normal
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hs.overgroup
  have hXK : X ≤ K := hs.toLocalInput.le_of_complement_le hs.complement_le_orbit hHK
  have hcT : K.pCoreIn 2 ≤ (T : Subgroup G) :=
    (SwappedSylow.orbit_core_le_two hs).trans inf_le_left
  have hKU : K.pCoreIn 2 ≤ U := by
    apply le_trans _ hcore
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K) (hcT.trans le_sup_right)
      ((hs.overgroup.trans hHK).trans
        (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  obtain ⟨S,hS⟩ := component_quotient_sylow hs.sylow_two hKH hs.orbit_normal
  let R := quotientImage K U
  have hRS : R ≤ (S : Subgroup (XiQuotient K)) := by
    rw [hS]
    exact map_mono (comap_mono hUT)
  have hiR : R.relIndex (S : Subgroup (XiQuotient K)) ≤ 2 := by
    have hQU : pCore 2 K ≤ U.subgroupOf K := fun x hx => hKU (mem_map_of_mem K.subtype hx)
    have hQT : pCore 2 K ≤ (T : Subgroup G).subgroupOf K := hQU.trans (comap_mono hUT)
    rw [hS]
    change ((U.subgroupOf K).map _).relIndex (((T : Subgroup G).subgroupOf K).map _) ≤ 2
    rw [relIndex_map_map,QuotientGroup.ker_mk',sup_of_le_left hQU,sup_of_le_left hQT]
    change (U.comap K.subtype).relIndex ((T : Subgroup G).subgroupOf K) ≤ 2
    rw [relIndex_comap,subgroupOf_map_subtype]
    exact (relIndex_le_of_le_right inf_le_left
      (U.subgroupOf (T : Subgroup G)).index_ne_zero_of_finite).trans hi
  obtain ⟨e,a,b,hswap⟩ := swapped_quotient_subgroup T hs U hTU
  let N := H ⊓ normalizer (U : Set G)
  have hTN : (T : Subgroup G) ≤ N := le_inf hTH hTU
  let f : N →* MulAut (XiQuotient K) :=
    (pCoreNormalizerAction 2 K).comp (inclusion (inf_le_left.trans hHK))
  have hfix (g : N) : R.map (f g).toMonoidHom = R :=
    pCoreNormalizerAction_preserves_image 2 K U _ g.property.2
  let : Fact p.Prime := ⟨hp⟩
  let : IsQuasisimple (XiQuotient I) := hs.quasisimple
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  have hlarge : 3 < p := by
    by_contra hle
    have hp3 : p = 3 := by have htwo := hp.two_le; obtain ⟨k,hk⟩ := ho; omega
    have hperfect := Group.IsPerfect.ofSurjective (f := eF.toMonoidHom) eF.surjective
    exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three (hF.trans hp3) hperfect
  have htwo : IsPGroup 2 f.range := by
    by_cases h8 : 8 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    · exact Theory.PSL2.prime_pair_intersection_action ho hlarge hF h8 eF e S R hRS hiR a b
        hswap f hfix
    · have hmod := Theory.PSL2.mod_eight_of_not_eight_dvd_card (hF ▸ ho) h8
      rw [hF] at hmod
      have hne : R ≠ (S : Subgroup (XiQuotient K)) := by
        rcases hcase with hh | hh
        · omega
        · rwa [hS]
      have hi2 : R.relIndex (S : Subgroup (XiQuotient K)) = 2 := by
        have hz : R.relIndex (S : Subgroup (XiQuotient K)) ≠ 0 := index_ne_zero_of_finite
        have h1 : R.relIndex (S : Subgroup (XiQuotient K)) ≠ 1 :=
          fun he => hne (le_antisymm hRS (relIndex_eq_one.mp he))
        omega
      exact Theory.PSL2.prime_pair_half_action ho hlarge hF h8 eF e S R hRS hi2 a b hswap f hfix
  intro g hg
  obtain ⟨t,ht,he⟩ := SylowNormalizerAction.action_detected_on_sylow (T.subtype hTN) f htwo ⟨g,hg⟩
  have htx : (t : G) ∈ normalizer (X : Set G) := hs.invariant ht
  have himage : (quotientImage K X).map (f ⟨g,hg⟩).toMonoidHom = quotientImage K X := by
    rw [←he]
    exact pCoreNormalizerAction_preserves_image 2 K X _ htx
  exact mem_normalizer_of_pCoreNormalizerAction_preserves_image K X hXK hs.perfect
    (hcT.trans hs.invariant) ⟨g,hHK hg.1⟩ himage
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The only remaining swapped obstruction has an odd-prime PSL₂ factor
in a small mod-eight congruence and the full quotient Sylow intersection. -/
theorem doubleNatural_four_pure_small_odd_swapped_of_many_of_omega_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) ≠ ⊥ →
      let X := PureFourXi.residual T L
      ∃ P : Sylow 2 G, B.pointSylow w < (P : Subgroup G) ∧
        (P : Subgroup G) ≤ B.pointCentralizer w ∧
        (P : Subgroup G) ⊓ normalizer (L : Set G) = B.pointSylow w ∧
        (P : Subgroup G) ≤ normalizer (B.pointSylow w : Set G) ∧
        (B.pointSylow w).relIndex (T : Subgroup G) = 2 ∧
        let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
        H ∈ HOver G ((X ⊔ (T : Subgroup G) : Subgroup G) : Set G) ∧
        H ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
        ¬ H ≤ normalizer (L : Set G) ∧
        ∃ A : Sylow 3 X, ∃ K : Subgroup G,
          SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X
            ((A : Subgroup X).map X.subtype) H K ∧
          conjugateSpanBy X H = componentOrbit K (T : Subgroup G) ∧
          X < componentOrbit K (T : Subgroup G) ∧
          (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient K) 2 p ∧
            (p % 8 = 3 ∨ p % 8 = 5)) ∧
          quotientImage (componentOrbit K (T : Subgroup G)) (B.pointSylow w) =
            quotientImage (componentOrbit K (T : Subgroup G)) (T : Subgroup G) ∧
          ¬ ClassicalGroup.IsPSL (XiQuotient K) 2 4 ∧
          K ∈ Chapter1.LStar G (T : Subgroup G) ∧
          K ∈ MainForward.faithfulLocalComponents T ∧
          Nonempty (Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T K) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf hne
  obtain ⟨P,hlt,hPC,hPM,hPN,hiT,hH,hHN,hout,A,K,hs,he,hstrict,hodd,hA5,hmax,hfaith,hFS⟩ :=
    D.doubleNatural_four_pure_odd_swapped_of_many_of_omega_fixed h hmany B S w hw hp hfix hf hne
  let X := PureFourXi.residual T L
  let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
  have hc : (X ⊔ (T : Subgroup G)).pCoreIn 2 ≤ B.pointSylow w := by
    rw [(D.doubleNatural_four_pure_xi_of_many h hmany B S w hw hp hfix hf).2.1]
    exact D.doubleNatural_four_pure_normalizer_core_le_of_many h hmany B S w hw hp hfix hf
  have hTU : (T : Subgroup G) ≤ normalizer (B.pointSylow w : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show B.pointSylow w ≤ (T : Subgroup G) from
      inf_le_left)).mp (normal_of_index_eq_two hiT)
  obtain ⟨p,hp',ho,hm⟩ := hodd
  have hbad (hcase : (p % 8 = 1 ∨ p % 8 = 7) ∨
      quotientImage (componentOrbit K (T : Subgroup G)) (B.pointSylow w) ≠
        quotientImage (componentOrbit K (T : Subgroup G)) (T : Subgroup G)) : False := by
    have hNX := PureFourXi.normalizes_of_odd_swapped_interval T hs inf_le_left hTU hiT.le hc
      hp' ho hm hcase
    have hHX : H ≤ normalizer (X : Set G) :=
      sup_le ((le_inf le_sup_left hPN).trans hNX)
        (sup_le X.le_normalizer hs.invariant)
    exact hstrict.not_ge (he ▸ conjugateSpanBy_le le_rfl hHX)
  have hmod : p % 8 = 3 ∨ p % 8 = 5 := by
    have hn : ¬ (p % 8 = 1 ∨ p % 8 = 7) := fun hh => hbad (Or.inl hh)
    obtain ⟨k,hk⟩ := ho
    omega
  have hfull : quotientImage (componentOrbit K (T : Subgroup G)) (B.pointSylow w) =
      quotientImage (componentOrbit K (T : Subgroup G)) (T : Subgroup G) := by
    by_contra hn
    exact hbad (Or.inr hn)
  exact ⟨P,hlt,hPC,hPM,hPN,hiT,hH,hHN,hout,A,K,hs,he,hstrict,⟨p,hp',ho,hm,hmod⟩,
    hfull,hA5,hmax,hfaith,hFS⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
