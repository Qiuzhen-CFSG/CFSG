module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2CoreNormal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryMaximal
public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.GroupTheory.CComponent.SevenCoverTheta
public import Theory.GroupTheory.SimpleSubgroupSmallIndex
public import Theory.Quasithin.NormalTwoRank

/-!
# Field-four overcomponents and complete G₂ right maximality

Characteristic two makes the action of J/O₂(J) on O₂(J)/Φ(O₂(J))
faithful. For the field-four G₂ and normal-core unitary cases this quotient
has order 2⁸. Its automorphism order excludes J₁, PSL₂(25) and the
exceptional-prime PSL₂ rows from the actual A.3.14 shortlist.

In the G₂ case the original cubic is fixed-point-free on the entire core.
Every perfect overcomponent centralizes its elementary center of order four.
On the other hand, the three-rank bound in N_G(J) makes a normal component
with quotient A₇ or its triple cover contain every cubic. These two facts
contradict the same cubic actor, completing right maximality also at field
four. The normalizer and relative componenthood are constructed here; they
are not extra hypotheses.

For unitary comparisons the nonnormal-core branch remains explicit; in the
normal branch only the actual A₇ and triple-cover quotients survive. The
whole original overlap, source S and both compatible orientations are kept.
The companion applies these results to the literal Chapter12 pair. Unitary,
Ree and U₅ maximality, exhaustive comparison and ambient recognition remain
separate source obligations, with original uniqueness still explicit.

Source: Aschbacher–Smith 5.2.8, printed pp.652–653, using 1.2.7 and A.3.18
(`refs/quasithin.pdf`). The imported G₂ calculations retain the attribution
in LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

private theorem core_frattini_action (h : HasCharacteristicTwo G) :
    ∃ f : (G ⧸ pCore 2 G) →* MulAut (pCore 2 G ⧸ frattini (pCore 2 G)),
      Function.Injective f ∧
      ∀ (g : G) (x : pCore 2 G),
        f (QuotientGroup.mk' (pCore 2 G) g) (QuotientGroup.mk' _ x) =
          QuotientGroup.mk' _ (MulAut.conjNormal g x) := by
  let a := (quotientAut (frattini (pCore 2 G))).comp
    (MulAut.conjNormal : G →* MulAut (pCore 2 G))
  have hk : a.ker = pCore 2 G := pCore_frattini_action_kernel 2 h
  let f := QuotientGroup.lift (pCore 2 G) a hk.ge
  refine ⟨f,(QuotientGroup.injective_lift_iff _ _ _).mpr hk.symm,?_⟩
  intro g x
  exact quotientAut_apply_mk _ _ _

private theorem quotient_order_dvd_GL8 (h : HasCharacteristicTwo G)
    (hc : Nat.card (pCore 2 G ⧸ frattini (pCore 2 G)) = 2^8) :
    Nat.card (G ⧸ pCore 2 G) ∣ 5348063769211699200 := by
  obtain ⟨f,hf,_⟩ := core_frattini_action h
  have hd := card_dvd_of_injective f hf
  let : Fact (IsPGroup 2 (pCore 2 G)) := ⟨pCore_isPGroup⟩
  let : IsElementaryAbelian 2 (pCore 2 G ⧸ frattini (pCore 2 G)) :=
    isElementaryAbelian_quotient_frattini (p := 2)
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ 8 hc] at hd
  norm_num [Fin.prod_univ_succ] at hd ⊢
  exact hd

omit [Finite G] in
private theorem shortlist_of_GL8_divisor
    (hm : ChapterA.Section03.SourceEmbeddings.AlternatingFive.Shortlist G)
    (hd : Nat.card G ∣ 5348063769211699200) :
    Chapter1.Section02.LocalModels.IsAlternating G 7 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover G 7 := by
  rcases hm with hm | hm | hm | hm | ⟨p,hp,hm⟩
  · exact .inl hm
  · exact .inr hm
  · obtain ⟨e⟩ := hm
    rw [Nat.card_congr e.toEquiv,Janko1.card_model] at hd
    norm_num at hd
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
      (F := F) (hF ▸ (by decide : Odd 25))
    rw [hF,←Nat.card_congr e.toEquiv] at hc
    have he : Nat.card G = 7800 := by omega
    rw [he] at hd
    norm_num at hd
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
      (F := F) (hF ▸ hp.2.1)
    rw [hF,←Nat.card_congr e.toEquiv] at hc
    have hd' : p ∣ 2 * 5348063769211699200 := by
      have hh := Nat.mul_dvd_mul_left 2 hd
      rw [Nat.mul_comm 2 (Nat.card G),hc] at hh
      exact (dvd_mul_right p (p^2-1)).trans hh
    have hh : p ∣ 2^29 * 3^5 * 5^2 * 7^2 * 17 * 31 * 127 := by
      convert hd' using 1
      norm_num
    simp only [hp.1.dvd_mul] at hh
    have hps : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 17 ∨ p = 31 ∨ p = 127 := by
      rcases hh with (((((h | h) | h) | h) | h) | h) | h
      all_goals try replace h := hp.1.dvd_of_dvd_pow h
      all_goals have he := (Nat.prime_dvd_prime_iff_eq hp.1 (by norm_num)).mp h
      all_goals omega
    rcases hps with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [Chapter1.Section02.A312ExceptionalPrime] at hp


private def core_equiv_of_ambient_eq {K J : Subgroup G}
    (hc : J.pCoreIn 2 = K.pCoreIn 2) : pCore 2 J ≃* pCore 2 K :=
  ((pCore 2 J).equivMapOfInjective J.subtype J.subtype_injective).trans
    ((MulEquiv.subgroupCongr hc).trans
      ((pCore 2 K).equivMapOfInjective K.subtype K.subtype_injective).symm)

private theorem frattini_quotient_card_of_special
    {Q : Type*} [Group Q] [Finite Q]
    (hc : Nat.card Q = 4^5) (hf : Nat.card (frattini Q) = 4) :
    Nat.card (Q ⧸ frattini Q) = 2^8 := by
  have hh := (frattini Q).index_mul_card
  rw [index_eq_card,hc,hf] at hh
  omega

open Atlas.G2 Atlas.G2.LieParabolicSetup
omit [Finite G] in
private theorem g2_core_frattini_card
    {K : Subgroup G} (F : Type) [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) (a : K ≃* local₁ (F := F)) :
    Nat.card (pCore 2 K ⧸ frattini (pCore 2 K)) = 2^8 := by
  let e := ((a.subgroupMap (pCore 2 K)).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 a))).trans
      (((pCore 2 (local₁ (F := F))).equivMapOfInjective
        (local₁ (F := F)).subtype (local₁ (F := F)).subtype_injective).trans
          (MulEquiv.subgroupCongr local₁_pCore))
  rw [Nat.card_congr (QuotientGroup.congr _ _ e (frattini_map_equiv e)).toEquiv]
  apply frattini_quotient_card_of_special
  · rw [card_radical₁,hF]
  · rw [radical₁_frattini_eq_center,card_center_radical₁,hF]

/-- At field four the actual maximal G₂ overcomponent has an eight-dimensional
Frattini quotient and the canonical faithful conjugation action on it. -/
theorem Preparation.g2_four_overcomponent_frattini_action
    {T : Sylow 2 G} {L W H A B J : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse))
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : residual H ≤ J) :
    Nat.card (pCore 2 J ⧸ frattini (pCore 2 J)) = 2^8 ∧
    ∃ f : (J ⧸ pCore 2 J) →* MulAut (pCore 2 J ⧸ frattini (pCore 2 J)),
      Function.Injective f ∧
      ∀ (g : J) (x : pCore 2 J),
        f (QuotientGroup.mk' (pCore 2 J) g) (QuotientGroup.mk' _ x) =
          QuotientGroup.mk' _ (MulAut.conjNormal g x) := by
  obtain ⟨_,_,⟨a⟩,_,_⟩ := d.g2_local_structure h hH.1.1.2 hp F he
  have hc := (d.g2_maximal_overcomponent_core h hH hp F he hJ hKJ).1
  let e := core_equiv_of_ambient_eq hc
  refine ⟨?_,core_frattini_action
    (Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T (h.qtke.evenCharacteristic T) hJ.1)⟩
  rw [Nat.card_congr (QuotientGroup.congr _ _ e (frattini_map_equiv e)).toEquiv]
  exact g2_core_frattini_card F hF a

open scoped commutatorElement
/-- Only A₇ and its triple cover survive the field-four G₂ overcomponent
case. The cubic remains the same element of the original whole overlap. -/
theorem Preparation.g2_maximal_or_four_alternating
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) ∨
      n = 2 ∧ Nat.card F = 4 ∧ ∃ J ∈ Chapter1.LStar G (T : Subgroup G),
        residual H < J ∧ J.pCoreIn 2 = (residual H).pCoreIn 2 ∧
          (Chapter1.Section02.LocalModels.IsAlternating (J ⧸ pCore 2 J) 7 ∨
            Chapter1.Section02.LocalModels.IsAlternatingCover (J ⧸ pCore 2 J) 7) ∧
          ∃ x : G, x ∈ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
              ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 ∧
            orderOf x = 3 ∧ x ∈ normalizer (J : Set G) ∧
            (∀ k ∈ residual H, ⁅x,k⁆ ∈ (residual H).pCoreIn 2) ∧
            (∀ q ∈ J.pCoreIn 2, Commute x q → q = 1) ∧
            ⁅J.pCoreIn 2,zpowers x⁆ = J.pCoreIn 2 := by
  rcases d.g2_maximal_or_four_shortlist h hH hp F he with hm | ⟨hn,hF,J,hJ,hKJ,hc,hs,hx⟩
  · exact .inl hm
  have hdim := (d.g2_four_overcomponent_frattini_action h hH hp F hF he hJ hKJ.le).1
  have hchar := Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T
    (h.qtke.evenCharacteristic T) hJ.1
  exact .inr ⟨hn,hF,J,hJ,hKJ,hc,shortlist_of_GL8_divisor hs
    (quotient_order_dvd_GL8 hchar hdim),hx⟩


open ChapterF.GreenBook.LieModels.UnitaryFour
section Unitary
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
  (he : (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse)) ∨
    (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)))
include d h hH hp m hm he

/-- A proper unitary overcomponent with normal original core has the actual
rank-eight Frattini action. This includes both degree-two extensions. -/
theorem Preparation.unitary_overcomponent_frattini_action_of_normal
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H < J)
    (hn : J ≤ normalizer ((residual H).pCoreIn 2 : Set G)) :
    m = 2 ∧ n = 4 ∧ Nat.card (pCore 2 J ⧸ frattini (pCore 2 J)) = 2^8 ∧
    ∃ f : (J ⧸ pCore 2 J) →* MulAut (pCore 2 J ⧸ frattini (pCore 2 J)),
      Function.Injective f ∧
      ∀ (g : J) (x : pCore 2 J),
        f (QuotientGroup.mk' (pCore 2 J) g) (QuotientGroup.mk' _ x) =
          QuotientGroup.mk' _ (MulAut.conjNormal g x) := by
  obtain ⟨hm2,hn4,hc,_⟩ := d.unitary_overcomponent_parameter_of_normal h hH hp m hm he hJ hKJ hn
  obtain ⟨_,_,_,_,hcard,hz,_,hfrat,_,_⟩ := d.unitary_core_structure h hH.1.1.2 hp m hm he
  let e := core_equiv_of_ambient_eq hc
  refine ⟨hm2,hn4,?_,core_frattini_action
    (Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T (h.qtke.evenCharacteristic T) hJ.1)⟩
  rw [Nat.card_congr (QuotientGroup.congr _ _ e (frattini_map_equiv e)).toEquiv]
  apply frattini_quotient_card_of_special
  · simpa only [hm2, Nat.reducePow] using hcard
  · rw [←hfrat,hz,hm2]
    norm_num

/-- The unitary obstruction retains nonnormal cores explicitly. In the normal
branch only the actual A₇ and triple-cover quotients remain. -/
theorem Preparation.unitary_maximal_or_alternating_obstruction :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) ∨
      ∃ J ∈ Chapter1.LStar G (T : Subgroup G), residual H < J ∧
        (¬ J ≤ normalizer ((residual H).pCoreIn 2 : Set G) ∨
          m = 2 ∧ n = 4 ∧ J.pCoreIn 2 = (residual H).pCoreIn 2 ∧
            (Chapter1.Section02.LocalModels.IsAlternating (J ⧸ pCore 2 J) 7 ∨
              Chapter1.Section02.LocalModels.IsAlternatingCover (J ⧸ pCore 2 J) 7)) := by
  rcases d.unitary_maximal_or_obstruction h hH hp m hm he with hmax | ⟨J,hJ,hKJ,hn | ⟨hm2,hn4,hc,hs⟩⟩
  · exact .inl hmax
  · exact .inr ⟨J,hJ,hKJ,.inl hn⟩
  · have hn : J ≤ normalizer ((residual H).pCoreIn 2 : Set G) :=
      hc ▸ J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
    have hdim := (d.unitary_overcomponent_frattini_action_of_normal h hH hp m hm he hJ hKJ hn).2.2.1
    have hchar := Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T
      (h.qtke.evenCharacteristic T) hJ.1
    exact .inr ⟨J,hJ,hKJ,.inr ⟨hm2,hn4,hc,
      shortlist_of_GL8_divisor hs (quotient_order_dvd_GL8 hchar hdim)⟩⟩

end Unitary

private theorem perfect_centralizes_core_center
    [Group.IsPerfect G] [IsElementaryAbelian 2 (center (pCore 2 G))]
    (hz : Nat.card (center (pCore 2 G)) = 4)
    (j : G) (z : center (pCore 2 G)) :
    Commute j ((z : pCore 2 G) : G) := by
  let a := (MulAut.characteristic (center (pCore 2 G))).comp
    (MulAut.conjNormal : G →* MulAut (pCore 2 G))
  have hAut : Nat.card (MulAut (center (pCore 2 G))) = 6 := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ 2 (by simpa using hz)]
    decide
  let : Group.IsSolvable (MulAut (center (pCore 2 G))) :=
    Group.isSolvable_of_card_le_six hAut.le
  let : Group.IsPerfect a.range := Group.IsPerfect.range a
  have hs : Subsingleton a.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable a.range inferInstance
  have ha : a j = 1 := congrArg a.range.subtype
    (hs.elim (⟨a j,⟨j,rfl⟩⟩ : a.range) 1)
  have he := congrArg (fun f : MulAut (center (pCore 2 G)) =>
    (((f z : center (pCore 2 G)) : pCore 2 G) : G)) ha
  change j * ((z : pCore 2 G) : G) * j⁻¹ = ((z : pCore 2 G) : G) at he
  exact (mul_inv_eq_iff_eq_mul).mp he

private theorem relative_seven_cubic_mem
    {N J : Subgroup G} (hJN : J ≤ N) [(J.subgroupOf N).Normal]
    (hJ : (J.subgroupOf N).IsCComponent)
    (hm : Chapter1.Section02.LocalModels.IsAlternating (J ⧸ pCore 2 J) 7 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover (J ⧸ pCore 2 J) 7)
    (hr : primeRank 3 N ≤ 2) {x : G} (hxN : x ∈ N) (hx : orderOf x = 3) : x ∈ J := by
  let B := J.subgroupOf N
  let e : (B ⧸ pCore 2 B) ≃* (J ⧸ pCore 2 J) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hJN) (pCore_map_iso 2 _)
  have hx' : orderOf (⟨x,hxN⟩ : N) = 3 := (orderOf_coe _).symm.trans hx
  rcases hm with hm | ⟨hq,hz,⟨a⟩⟩
  · let a := hm.some
    let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv (e.trans a).symm
    exact SevenCComponentTheta.order_three_mem_of_quotient_seven B hJ (e.trans a) hr hx'
  · let := hq
    let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv e.symm
    exact SevenCComponentTheta.order_three_mem_of_central_quotient_seven B hJ
      ((QuotientGroup.congr _ _ e (by
        apply le_antisymm
        · rintro _ ⟨z,hz,rfl⟩
          exact ((centerCongr e) ⟨z,hz⟩).property
        · intro z hz
          exact ⟨e.symm z, ((centerCongr e).symm ⟨z,hz⟩).property, e.apply_symm_apply z⟩)).trans a) hr hx'

omit [Finite G] in
private theorem g2_core_center_four
    {K : Subgroup G} (F : Type) [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) (a : K ≃* local₁ (F := F)) :
    Nat.card (center (pCore 2 K)) = 4 ∧ IsElementaryAbelian 2 (center (pCore 2 K)) := by
  let e := ((a.subgroupMap (pCore 2 K)).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 a))).trans
      (((pCore 2 (local₁ (F := F))).equivMapOfInjective
        (local₁ (F := F)).subtype (local₁ (F := F)).subtype_injective).trans
          (MulEquiv.subgroupCongr local₁_pCore))
  let := radical₁_center_elementary (F := F)
  refine ⟨?_,IsElementaryAbelian.of_injective (centerCongr e).toMonoidHom
    (centerCongr e).injective⟩
  rw [Nat.card_congr (centerCongr e).toEquiv,card_center_radical₁,hF]

/-- The prepared G₂ right factor is maximal also at field four. -/
theorem Preparation.g2_right_maximal_all
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) := by
  rcases d.g2_maximal_or_four_alternating h hH hp F he with hm |
    ⟨_,hF,J,hJ,hKJ,hc,hm,x,_,hx,hxN,_,hfix,_⟩
  · exact hm
  exfalso
  obtain ⟨_,_,⟨a⟩,_,_⟩ := d.g2_local_structure h hH.1.1.2 hp F he
  obtain ⟨hzK,heK⟩ := g2_core_center_four F hF a
  let e := core_equiv_of_ambient_eq hc
  let := heK
  let : IsElementaryAbelian 2 (center (pCore 2 J)) :=
    IsElementaryAbelian.of_injective (centerCongr e).toMonoidHom (centerCongr e).injective
  have hz : Nat.card (center (pCore 2 J)) = 4 := (Nat.card_congr (centerCongr e).toEquiv).trans hzK
  let : Nontrivial (center (pCore 2 J)) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨z,hz1⟩ := exists_ne (1 : center (pCore 2 J))
  let Q := J.pCoreIn 2
  let N := normalizer (J : Set G)
  have hQN : Q ≤ N := (map_subtype_le _).trans J.le_normalizer
  have hNQ : N ≤ normalizer (Q : Set G) := normalizer_le_normalizer_characteristic_image J (pCore 2 J)
  have hQne : Q ≠ ⊥ := by
    intro hb
    have hh : (((z : pCore 2 J) : J) : G) = 1 := mem_bot.mp
      (hb ▸ (mem_map_of_mem J.subtype (z : pCore 2 J).property))
    exact hz1 (Subtype.ext (Subtype.ext (Subtype.ext hh)))
  have hN : N ∈ Chapter1.H G := by
    intro hb
    exact hQne (le_antisymm (hb ▸ le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 J) hQN hNQ) bot_le)
  have hTN : (T : Subgroup G) ≤ N :=
    (hH.1.1.2.trans (le_normalizer_residual H)).trans
      (d.g2_maximal_overcomponent_core h hH hp F he hJ hKJ.le).2
  have hcomp := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T hJ).component
    N ⟨hN,sup_le J.le_normalizer hTN⟩
  let : (Q.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hNQ
  have hQr : Q.subgroupOf N ≠ ⊥ := by
    intro hb
    exact hQne (by simpa only [map_subgroupOf_eq_of_le hQN,Subgroup.map_bot]
      using congrArg (Subgroup.map N.subtype) hb)
  have hr : primeRank 3 N ≤ 2 :=
    Theory.Quasithin.primeRank_subgroup_le_two_of_normal_two_subgroup h.qtke.quasithin
      N (Q.subgroupOf N) hQr ((isPGroup_pCoreIn 2 J).of_injective
        (subgroupOfEquivOfLe hQN).toMonoidHom (subgroupOfEquivOfLe hQN).injective)
      3 Nat.prime_three (by decide)
  let : (J.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have hxJ := relative_seven_cubic_mem J.le_normalizer hcomp hm hr hxN hx
  let := Chapter1.mem_L_isPerfect hJ.1
  have hcomm := perfect_centralizes_core_center hz (⟨x,hxJ⟩ : J) z
  have heq : (((z : pCore 2 J) : J) : G) = 1 :=
    hfix _ (mem_map_of_mem J.subtype (z : pCore 2 J).property) (hcomm.map J.subtype)
  exact hz1 (Subtype.ext (Subtype.ext (Subtype.ext heq)))

/-- In a maximal local overcomponent with A₇ or triple-cover quotient and
elementary core center of order four, every cubic in its normalizer fixes
that center. The normalizer is a proper two-local group, so quasithinness
supplies the three-rank bound used by the component argument. -/
theorem maximal_seven_cubic_centralizes_core_center
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {J : Subgroup G}
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hTN : (T : Subgroup G) ≤ normalizer (J : Set G))
    [IsElementaryAbelian 2 (center (pCore 2 J))]
    (hz : Nat.card (center (pCore 2 J)) = 4)
    (hm : Chapter1.Section02.LocalModels.IsAlternating (J ⧸ pCore 2 J) 7 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover (J ⧸ pCore 2 J) 7)
    {x : G} (hxN : x ∈ normalizer (J : Set G)) (hx : orderOf x = 3) :
    ∀ z ∈ centerIn (J.pCoreIn 2), Commute x z := by
  let Q := J.pCoreIn 2
  let N := normalizer (J : Set G)
  have hQN : Q ≤ N := (map_subtype_le _).trans J.le_normalizer
  have hNQ : N ≤ normalizer (Q : Set G) := normalizer_le_normalizer_characteristic_image J (pCore 2 J)
  have hQne : Q ≠ ⊥ := by
    intro hb
    have hbot : pCore 2 J = ⊥ := (map_eq_bot_iff_of_injective _ J.subtype_injective).mp hb
    have hc : Nat.card (pCore 2 J) = 1 := by rw [hbot,card_bot]
    have hh := Nat.card_le_card_of_injective _ (center (pCore 2 J)).subtype_injective
    omega
  have hN : N ∈ Chapter1.H G := by
    intro hb
    exact hQne (le_antisymm (hb ▸ le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 J) hQN hNQ) bot_le)
  have hcomp := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple hG T hJ).component
    N ⟨hN,sup_le J.le_normalizer hTN⟩
  let : (Q.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hNQ
  have hQr : Q.subgroupOf N ≠ ⊥ := by
    intro hb
    exact hQne (by simpa only [map_subgroupOf_eq_of_le hQN,Subgroup.map_bot]
      using congrArg (Subgroup.map N.subtype) hb)
  have hr : primeRank 3 N ≤ 2 :=
    Theory.Quasithin.primeRank_subgroup_le_two_of_normal_two_subgroup hG.quasithin
      N (Q.subgroupOf N) hQr ((isPGroup_pCoreIn 2 J).of_injective
        (subgroupOfEquivOfLe hQN).toMonoidHom (subgroupOfEquivOfLe hQN).injective)
      3 Nat.prime_three (by decide)
  let : (J.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have hxJ := relative_seven_cubic_mem J.le_normalizer hcomp hm hr hxN hx
  let := Chapter1.mem_L_isPerfect hJ.1
  intro z hzQ
  obtain ⟨q,hq,hqz⟩ := hzQ.1
  change q.val = z at hqz
  have hqc : (⟨q,hq⟩ : pCore 2 J) ∈ center (pCore 2 J) := by
    rw [mem_center_iff]
    intro r
    apply Subtype.ext
    apply Subtype.ext
    change r.val.val * q.val = q.val * r.val.val
    rw [hqz]
    exact hzQ.2 r.val.val (mem_map_of_mem J.subtype r.property)
  exact hqz ▸ (perfect_centralizes_core_center hz (⟨x,hxJ⟩ : J) ⟨⟨q,hq⟩,hqc⟩).map J.subtype

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
