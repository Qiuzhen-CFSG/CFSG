module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.SingleProduct
public import Theory.GroupTheory.PResidual.PrimeSection
public import Theory.GroupTheory.NormalCubicSylowSupplement

/-!
# The cubic lift lies in the original component normalizer

Extend the original Borel-core argument to the image of O²(X) in a common
Borel overgroup's literal O₃′ quotient. A moving solvable minimal outside
X cannot have a three-group residual image there.

Apply this to the selected cubic lift D. Its permuting Sylow join has index
three and contains the original nontrivial normal two-core. If D escapes
N_G(L), that join is another minimal outside overgroup. Its residual image
lies in the original normal cubic, so the preceding argument forces D to
centralize the whole omega-center.

The oriented Borel residual lifts into the normal component K through the
3′ kernel, giving J = KH. The index-three supplement theorem gives
J = KDT. As K and T centralize the omega-center and H does not, D must
move it. Thus D lies in N_G(L), without first choosing a different lift
permuting with the Borel residual. All maps refer to the original quotient.

This proves the cubic-normalizer step of Aschbacher--Smith 13.2.7,
printed pp.883--884. The subsequent quotient-action and normal-closure
contradiction, the nonsolvable generation bound, and source assembly remain.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- A three-group residual image puts its two-core in the original Borel core. -/
theorem residual_core_le_borel_core_of_three_image
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (J : Subgroup G) (hHJ : H ≤ J) (hPJ : borelResidual T L ⊔ (T : Subgroup G) ≤ J)
    (hthree : IsPGroup 3 (((pResidual 2 H).map (inclusion hHJ)).map
      (QuotientGroup.mk' (pPrimeCore 3 J)))) :
    ((pResidual 2 H).map H.subtype).pCoreIn 2 ≤
      (borelResidual T L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let P := borelResidual T L ⊔ (T : Subgroup G)
  let R := pResidual 2 H
  let f := inclusion hHJ
  let q := QuotientGroup.mk' (pPrimeCore 3 J)
  let C := (R.pCoreIn 2).map f
  have hz : C.map q = ⊥ := by
    rw [show C = (R.pCoreIn 2).map f from rfl,map_map]
    let W := (R.pCoreIn 2).map (q.comp f)
    have hWtwo : IsPGroup 2 W := (isPGroup_pCoreIn 2 R).map _
    have hWthree : IsPGroup 3 W := hthree.to_le (by
      rw [map_map]
      exact map_mono (pCoreIn_le 2 R))
    simpa only [inf_idem] using (IsPGroup.disjoint_of_ne 2 3 (by decide) W W hWtwo hWthree).eq_bot
  have hCX : C ≤ pPrimeCore 3 J := by
    have hh : C ≤ q.ker := map_le_iff_le_comap.mp hz.le
    simpa only [q,QuotientGroup.ker_mk'] using hh
  let : (R.pCoreIn 2).Normal := inferInstanceAs ((pCore 2 R).map R.subtype).Normal
  have hRC : R.pCoreIn 2 ≤ pCore 2 H :=
    le_sSup ⟨inferInstance,isPGroup_pCoreIn 2 R⟩
  have hCP : C ≤ P.subgroupOf J := by
    rintro x ⟨y,hy,rfl⟩
    exact (show (T : Subgroup G) ≤ P from le_sup_right)
      ((pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2)) (hRC hy))
  obtain ⟨e⟩ := borel_sylow_core_quotient d hH hZ
  let eP := subgroupOfEquivOfLe hPJ
  let eQ := (QuotientGroup.congr _ _ eP (pCore_map_iso 2 eP)).trans e
  have hCC : C ≤ (P.subgroupOf J).pCoreIn 2 :=
    (le_inf hCP hCX).trans (inf_primeToThreeCore_le_twoCore (P.subgroupOf J) eQ)
  have hm := map_mono (f := J.subtype) hCC
  rw [map_pCoreIn_of_injective 2 _ J.subtype J.subtype_injective,
    map_subgroupOf_eq_of_le hPJ] at hm
  change ((R.pCoreIn 2).map f).map J.subtype ≤ P.pCoreIn 2 at hm
  rw [map_map] at hm
  change (R.pCoreIn 2).map H.subtype ≤ P.pCoreIn 2 at hm
  rwa [map_pCoreIn_of_injective 2 R H.subtype H.subtype_injective] at hm

/-- The precise Sylow conclusion in the first sentence of 13.2.13. -/
theorem borel_core_sylow_of_three_image
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (J : Subgroup G) (hHJ : H ≤ J) (hPJ : borelResidual T L ⊔ (T : Subgroup G) ≤ J)
    (hthree : IsPGroup 3 (((pResidual 2 H).map (inclusion hHJ)).map
      (QuotientGroup.mk' (pPrimeCore 3 J)))) :
    let R₁ := (borelResidual T L ⊔ (T : Subgroup G)).pCoreIn 2
    Chapter1.IsSylowIn 2 R₁ ((pResidual 2 H).map H.subtype ⊔ R₁) := by
  let P := borelResidual T L ⊔ (T : Subgroup G)
  let R₁ := P.pCoreIn 2
  let R := (pResidual 2 H).map H.subtype
  have hR₁T : R₁ ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow P (T.subtype (show (T : Subgroup G) ≤ P from le_sup_right))
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ P from le_sup_right)] at hh
  have hn : R₁ ≤ normalizer (R : Set G) :=
    hR₁T.trans (hH.1.1.2.trans (le_normalizer_embedded_pResidual 2 H))
  let e := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let eQ := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let := source_residual_core_quotient_elementary d hH hB hZ hs
  have hr : IsPGroup 3 (R ⧸ pCore 2 R) :=
    (IsElementaryAbelian.isPGroup 3 _).of_equiv eQ
  have hi : ¬ 2 ∣ (pCore 2 R).index := by
    rw [index_eq_card]
    obtain ⟨n,hn⟩ := hr.exists_card_eq
    rw [hn]
    intro hd
    have hh := ((by decide : Nat.Coprime 2 3).pow_right n).of_dvd_right hd
    norm_num at hh
  exact (isPGroup_pCoreIn 2 P).exists_sylow_sup_of_coprime_index R R₁ hn
    (pCore 2 R) hi (residual_core_le_borel_core_of_three_image d hH hZ J hHJ hPJ hthree)


/-- The actual residual of a moving outside group cannot have three-group
image in a common Borel overgroup's prime-to-three quotient. -/
theorem not_three_residual_image
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (J : Subgroup G) (hHJ : H ≤ J) (hPJ : borelResidual T L ⊔ (T : Subgroup G) ≤ J) :
    ¬ IsPGroup 3 (((pResidual 2 H).map (inclusion hHJ)).map
      (QuotientGroup.mk' (pPrimeCore 3 J))) := by
  intro hthree
  apply local_core_baumann_not_sylow d hH
  have hh := borel_core_baumann_sylow d hH hB hZ hs
    (borel_core_sylow_of_three_image d hH hB hZ hs J hHJ hPJ hthree)
  simpa only [(borel_core_thompson_baumann d).2] using hh

omit d in
private theorem cubic_join_index (S : Sylow 2 G) (Y : Subgroup G)
    (hc : Nat.card Y = 3)
    (hp : (Y : Set G) * (S : Set G) = (S : Set G) * (Y : Set G)) :
    (S : Subgroup G).relIndex (Y ⊔ S) = 3 := by
  have hcop : Nat.Coprime (Nat.card Y) (Nat.card (S : Subgroup G)) := by
    obtain ⟨n,hn⟩ := S.isPGroup'.exists_card_eq
    rw [hc,hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hd := disjoint_of_coprime_natCard hcop
  have hh := card_set_mul_mul_card_inf Y (S : Subgroup G)
  rw [hd.eq_bot,card_bot,mul_one,←coe_sup_of_set_mul_comm Y S hp] at hh
  change Nat.card (Y ⊔ S : Subgroup G) = _ at hh
  have hi := ((S : Subgroup G).subgroupOf (Y ⊔ S)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (show (S : Subgroup G) ≤ Y ⊔ S from le_sup_right)).toEquiv] at hi
  rw [hh,hc,mul_comm 3] at hi
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hi

omit d [Finite G] in
private theorem index_three_HStar (S : Sylow 2 G) (M X : Subgroup G)
    (hSM : (S : Subgroup G) ≤ M) (hSX : (S : Subgroup G) ≤ X)
    (hc : X.pCoreIn 2 ≠ ⊥) (hi : (S : Subgroup G).relIndex X = 3)
    (hout : ¬ X ≤ M) : X ∈ Chapter3.HStar (S : Subgroup G) M := by
  refine ⟨⟨⟨hc,hSX⟩,hout⟩,?_⟩
  intro U hU hUX
  have hm := relIndex_mul_relIndex (S : Subgroup G) U X hU.1.2 hUX
  rw [hi] at hm
  have hp : ((S : Subgroup G).relIndex U * U.relIndex X).Prime := hm ▸ Nat.prime_three
  rcases Nat.prime_mul_iff.mp hp with ⟨_,h⟩ | ⟨_,h⟩
  · exact relIndex_eq_one.mp h
  · exact (hU.2 ((relIndex_eq_one.mp h).trans hSM)).elim

/-- In the original single-factor quotient, the prescribed cubic lift
centralizes the whole omega-center whenever it escapes the component normalizer.
The original quotient, rather than a quotient of the cubic Sylow join, controls
its residual image. -/
theorem single_cubic_normalizes_or_centralizes
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hg : let J := H ⊔ borelResidual T L
      ChapterF.IsGoldschmidtTriple
        ((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J) (H.subgroupOf J))
    (c : SingleQuotientProduct T L H) :
    c.cubic_lift.map (H ⊔ borelResidual T L).subtype ≤ normalizer (L : Set G) ∨
    c.cubic_lift.map (H ⊔ borelResidual T L).subtype ≤
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  classical
  let J := H ⊔ borelResidual T L
  let Y := c.cubic_lift.map J.subtype
  let X := Y ⊔ (T : Subgroup G)
  have hTJ : (T : Subgroup G) ≤ J := hH.1.1.2.trans (show H ≤ J from le_sup_left)
  have hYJ : Y ≤ J := map_subtype_le _
  have hXJ : X ≤ J := sup_le hYJ hTJ
  have hcY : Nat.card Y = 3 :=
    (card_map_of_injective J.subtype_injective).trans c.cubic_card
  have hperm : (Y : Set G) * (T : Set G) = (T : Set G) * (Y : Set G) := by
    have hm := congrArg (Set.image J.subtype) c.cubic_permutes.symm
    rw [Set.image_mul,Set.image_mul] at hm
    change (Y : Set G) *
      (((T : Subgroup G).subgroupOf J).map J.subtype : Set G) =
      (((T : Subgroup G).subgroupOf J).map J.subtype : Set G) * (Y : Set G) at hm
    simpa only [map_subgroupOf_eq_of_le hTJ,Sylow.coe_coe] using hm
  have hi := cubic_join_index T Y hcY hperm
  by_cases hYM : Y ≤ normalizer (L : Set G)
  · exact Or.inl hYM
  right
  by_contra hYZ
  have hXZ : ¬ X ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) :=
    fun h => hYZ (le_sup_left.trans h)
  have hXM : ¬ X ≤ normalizer (L : Set G) := fun h => hYM (le_sup_left.trans h)
  have hJcore : J.pCoreIn 2 ≠ ⊥ := by
    let eH : H.subgroupOf J ≃* H := subgroupOfEquivOfLe le_sup_left
    have he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) :=
      ⟨(QuotientGroup.congr _ _ eH (pCore_map_iso 2 eH)).symm.trans hg.quotient_right.some⟩
    exact single_borel_join_core_ne_bot d hH hB hZ he
  have hJcoreT : J.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTJ] using
      pCoreIn_le_sylow J (T.subtype hTJ)
  have hXcore : X.pCoreIn 2 ≠ ⊥ := by
    intro he
    apply hJcore
    apply bot_unique
    rw [←he]
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 J)
      (hJcoreT.trans le_sup_right)
      ((hXJ.trans J.le_normalizer).trans
        (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  have hX := index_three_HStar T (normalizer (L : Set G)) X
    d.normalizes_L le_sup_right hXcore hi hXM
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  have hSnot : ¬ (S : Subgroup X).Normal := by
    intro hn
    have hXT : X ≤ normalizer (T : Set G) := by
      intro x hx
      apply mem_normalizer_iff.mpr
      intro t
      constructor
      · intro ht
        exact hn.conj_mem ⟨t,mem_sup_right ht⟩ ht ⟨x,hx⟩
      · intro ht
        have hh := hn.conj_mem ⟨x * t * x⁻¹,mem_sup_right ht⟩ ht (⟨x,hx⟩ : X)⁻¹
        change x⁻¹ * (x * t * x⁻¹) * x⁻¹⁻¹ ∈ (T : Subgroup G) at hh
        simpa [mul_assoc] using hh
    have hnB : normalizer (T : Set G) ≤
        normalizer (ChapterB.baumann (T : Subgroup G) : Set G) :=
      normalizer_le_normalizer_baumann _
    exact hXM (hXT.trans (hnB.trans hB))
  have heX := sylow_index_three_core_quotient S hi
    (lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal S)
      (fun he => hSnot (he ▸ inferInstance)))
  have hsX : Group.IsSolvable X := SymmetricThreeTwoCore.solvable heX.some
  apply not_three_residual_image d hX hB hXZ hsX J hXJ
    (sup_le le_sup_right hTJ)
  let q := QuotientGroup.mk' (pPrimeCore 3 J)
  let D := pResidual 2 (J ⧸ pPrimeCore 3 J) ⊓ centralizer (c.selected.component : Set _)
  let P := ((T : Subgroup G).subgroupOf J).map q
  let R := ((pResidual 2 X).map (inclusion hXJ)).map q
  let : D.Normal := c.second_normal
  have hRperfect : IsPPerfect 2 R := by
    have h := (isPPerfect_pResidual (G := X) 2).of_surjective
      ((inclusion hXJ).subgroupMap (pResidual 2 X))
      ((inclusion hXJ).subgroupMap_surjective _)
    exact h.of_surjective (q.subgroupMap _) (q.subgroupMap_surjective _)
  have hR : R ≤ D ⊔ P := by
    have hle : (pResidual 2 X).map (inclusion hXJ) ≤ X.subgroupOf J := by
      rintro x ⟨a,ha,rfl⟩
      exact a.property
    have hm := map_mono (f := q) hle
    have hXim : (X.subgroupOf J).map q = D ⊔ P := by
      rw [show X = Y ⊔ (T : Subgroup G) from rfl,subgroupOf_sup hYJ hTJ,Subgroup.map_sup]
      have hY : Y.subgroupOf J = c.cubic_lift :=
        comap_map_eq_self_of_injective J.subtype_injective _
      rw [hY,c.cubic_image]
    exact hm.trans_eq hXim
  have hRP : R ≤ D := le_normal_of_isPPerfect_of_le_sup_pGroup R D P
    hRperfect ((T.subtype hTJ).isPGroup'.map q) hR
  exact (IsPGroup.of_card (p := 3) (G := D) (n := 1) (by
    change Nat.card D = 3
    exact c.second_card)).to_le hRP

omit d [Group G] [Finite G] in
private theorem residual_le_of_coprime_image
    {M : Type*} [Group M] [Finite M]
    (N K B : Subgroup M) [N.Normal] [K.Normal]
    (hN : Nat.Coprime 3 (Nat.card N))
    (hB : pResidual 2 B = primeToResidual 3 B)
    (hm : ((pResidual 2 B).map B.subtype).map (QuotientGroup.mk' N) ≤
      K.map (QuotientGroup.mk' N)) :
    (pResidual 2 B).map B.subtype ≤ K := by
  rw [hB] at hm ⊢
  let X := (primeToResidual 3 B).map B.subtype
  let U := K ⊔ N
  have hX : X ≤ U := by
    have hh := comap_mono (f := QuotientGroup.mk' N) hm
    rw [comap_map_eq,comap_map_eq,QuotientGroup.ker_mk'] at hh
    exact le_sup_left.trans hh
  have hself : (primeToResidual 3 X).map X.subtype = X := by
    dsimp only [X]
    rw [←map_embedded_primeToResidual_of_hom,
      embedded_primeToResidual_eq_of_normal 3 (primeToResidual 3 B) le_rfl]
  have hindex : Nat.Coprime 3 (K.subgroupOf U).index := by
    change Nat.Coprime 3 (K.relIndex (K ⊔ N))
    rw [relIndex_sup_left]
    exact hN.coprime_dvd_right (relIndex_dvd_card _ _)
  have hc := map_mono (f := U.subtype) (primeToResidual_le (K.subgroupOf U) hindex)
  rw [map_subgroupOf_eq_of_le (show K ≤ U from le_sup_left)] at hc
  have hh := embedded_primeToResidual_mono 3 hX
  rw [hself] at hh
  exact hh.trans hc


omit d in
/-- The original Borel vertex and normal component lift generate the
whole join with H. Coprime residual lifting retains O₃′(J). -/
theorem single_component_sup_H
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hg : let J := H ⊔ borelResidual T L
      ChapterF.IsGoldschmidtTriple
        ((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J) (H.subgroupOf J))
    (c : SingleQuotientProduct T L H) :
    c.lift ⊔ H.subgroupOf (H ⊔ borelResidual T L) = ⊤ := by
  let J := H ⊔ borelResidual T L
  let A := (borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J
  let B := H.subgroupOf J
  let : c.lift.Normal := c.lift_normal
  have hr : (pResidual 2 A).map A.subtype ≤ c.lift := by
    apply residual_le_of_coprime_image (pPrimeCore 3 J) c.lift A pPrimeCore_coprime_card
      (SymmetricThreeTwoCore.twoResidual_eq_primeToThree hg.quotient_left.some)
    rw [map_embedded_pResidual,c.lift_image]
    exact c.selected.left_contains
  have hBJ : borelResidual T L ≤ J := le_sup_right
  have hp : IsPPerfect 2 ((borelResidual T L).subgroupOf J) := by
    let e := subgroupOfEquivOfLe hBJ
    exact borelResidual_twoPerfect.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hleft : (borelResidual T L).subgroupOf J ≤ c.lift := by
    have hle : (borelResidual T L).subgroupOf J ≤ A := comap_mono le_sup_left
    have he := le_pResidual_of_isPPerfect
      (((borelResidual T L).subgroupOf J).subgroupOf A)
      (hp.of_surjective (subgroupOfEquivOfLe hle).symm.toMonoidHom
        (subgroupOfEquivOfLe hle).symm.surjective)
    have hm := map_mono (f := A.subtype) he
    rw [map_subgroupOf_eq_of_le hle] at hm
    exact hm.trans hr
  apply top_unique
  rw [←hg.generated]
  apply sup_le ?_ le_sup_right
  have hTJ : (T : Subgroup G) ≤ J := hH.1.1.2.trans (show H ≤ J from le_sup_left)
  rw [subgroupOf_sup hBJ hTJ]
  exact sup_le (hleft.trans le_sup_left) ((comap_mono hH.1.1.2).trans le_sup_right)

omit d in
/-- The chosen order-three lift moves the whole Sylow omega-center:
its product with the Sylow supplements the centralizing component lift. -/
theorem single_cubic_moves_omega
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hg : let J := H ⊔ borelResidual T L
      ChapterF.IsGoldschmidtTriple
        ((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J) (H.subgroupOf J))
    (c : SingleQuotientProduct T L H) :
    ¬ c.cubic_lift.map (H ⊔ borelResidual T L).subtype ≤
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  let J := H ⊔ borelResidual T L
  let B := H.subgroupOf J
  let S := T.subtype (hH.1.1.2.trans (show H ≤ J from le_sup_left))
  let : c.lift.Normal := c.lift_normal
  have hSB : (S : Subgroup J) ≤ B := fun x hx => hH.1.1.2 hx
  have hi : (S : Subgroup J).relIndex B = 3 := by
    let SB := S.subtype hSB
    exact SymmetricThreeTwoCore.sylow_index_three hg.quotient_right.some SB
  let q := QuotientGroup.mk' (pPrimeCore 3 J)
  have hd : Disjoint c.cubic_lift c.lift := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    have hqx : q x = 1 := by
      apply mem_bot.mp
      apply (disjoint_iff.mp c.disjoint).le
      refine ⟨?_,?_⟩
      · rw [←c.lift_image]
        exact mem_map_of_mem q hx.2
      · rw [←c.cubic_image]
        exact mem_map_of_mem q hx.1
    have hk : x ∈ pPrimeCore 3 J := (QuotientGroup.eq_one_iff x).mp hqx
    have hcop : Nat.Coprime (Nat.card c.cubic_lift) (Nat.card (pPrimeCore 3 J)) := by
      rw [c.cubic_card]
      exact pPrimeCore_coprime_card
    exact (disjoint_iff.mp (disjoint_of_coprime_natCard hcop)).le ⟨hx.1,hk⟩
  have hgen := normal_cubic_sylow_supplement c.lift B c.cubic_lift S
    (single_component_sup_H hH hg c) hSB hi c.cubic_card hd c.cubic_permutes.symm
  intro hy
  have hT : (T : Subgroup G) ≤
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) :=
    le_centralizer_iff.mp (fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2)
  have hm := congrArg (map J.subtype) hgen
  rw [Subgroup.map_sup,Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,
    show (S : Subgroup J) = (T : Subgroup G).subgroupOf J from rfl,
    map_subgroupOf_eq_of_le
      (hH.1.1.2.trans (show H ≤ J from le_sup_left))] at hm
  exact hZ ((show H ≤ J from le_sup_left).trans
    (hm.ge.trans (sup_le c.lift_centralizes (sup_le hy hT))))

/-- The selected cubic lift in the original single-factor product lies
in the original component normalizer. No Borel-permutability assumption
or change of quotient is needed. -/
theorem single_cubic_le_normalizer
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hg : let J := H ⊔ borelResidual T L
      ChapterF.IsGoldschmidtTriple
        ((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J) (H.subgroupOf J))
    (c : SingleQuotientProduct T L H) :
    c.cubic_lift.map (H ⊔ borelResidual T L).subtype ≤ normalizer (L : Set G) :=
  (single_cubic_normalizes_or_centralizes d hH hB hZ hg c).resolve_right
    (single_cubic_moves_omega hH hZ hg c)

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
