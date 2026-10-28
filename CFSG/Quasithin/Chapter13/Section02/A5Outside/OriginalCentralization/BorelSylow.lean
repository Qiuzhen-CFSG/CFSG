module
public import Theory.GroupTheory.ResidualThreeCoreContainment
public import Theory.GroupTheory.SylowNormalizedEnlargement
public import CFSG.Quasithin.Chapter3.Section01.CommonNormalKnownSimple
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.BorelHeredity

/-!
# The first and last steps of the original Borel-join quotient exclusion

If O²(H₀/O₃′(H₀)) is a three-group, the two-core of O²(H) maps trivially
to that quotient. The literal Borel supplement L₁T has S3 two-core quotient,
so intersection with O₃′(H₀) puts the residual core in O₂(L₁T). Since the
residual has odd two-core quotient, O₂(L₁T) is Sylow in its join with O²(H).

At the other end of the source argument, Baum(O₂(LT)) cannot be Sylow in
its join with O²(H): Sylow enlargement and the proved common-normal theorem
contradict uniqueness over LT. The Thompson/Baumann identities and failure
of residual normalization are supplied by BorelHeredity. The middle Sylow
transfer is explicit at this interface and is discharged in BorelQuotient
using Stellmacher's normal-supplement theorem. SourceAssembly/BorelSylow
applies that complete quotient exclusion to the universal terminal consumer.

Source: Aschbacher--Smith 13.2.13, printed p.883.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- The first containment of source 13.2.13, with the actual residual core. -/
theorem residual_core_le_borel_core_of_three_quotient
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hthree : let J := H ⊔ borelResidual T L
      IsPGroup 3 (pResidual 2 (J ⧸ pPrimeCore 3 J))) :
    ((pResidual 2 H).map H.subtype).pCoreIn 2 ≤
      (borelResidual T L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let J := H ⊔ borelResidual T L
  let P := borelResidual T L ⊔ (T : Subgroup G)
  let R := pResidual 2 H
  have hHJ : H ≤ J := le_sup_left
  have hPJ : P ≤ J := sup_le le_sup_right (hH.1.1.2.trans hHJ)
  let f := inclusion hHJ
  let q := QuotientGroup.mk' (pPrimeCore 3 J)
  let C := (R.pCoreIn 2).map f
  have hz : C.map q = ⊥ := by
    rw [show C = (R.pCoreIn 2).map f from rfl,map_map]
    exact residual_twoCore_map_eq_bot_of_three_residual (q.comp f) hthree
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
theorem borel_core_sylow_of_three_quotient
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hthree : let J := H ⊔ borelResidual T L
      IsPGroup 3 (pResidual 2 (J ⧸ pPrimeCore 3 J))) :
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
    (pCore 2 R) hi (residual_core_le_borel_core_of_three_quotient d hH hZ hthree)

/-- The common-normal contradiction in 13.2.13 uses the Baumann subgroup
of the original local core, independently of the outside Baumann bound. -/
theorem local_core_baumann_not_sylow
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
    ¬ Chapter1.IsSylowIn 2 (ChapterB.baumann Q)
      ((pResidual 2 H).map H.subtype ⊔ ChapterB.baumann Q) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let R := (pResidual 2 H).map H.subtype
  change ¬ Chapter1.IsSylowIn 2 (ChapterB.baumann Q) (R ⊔ ChapterB.baumann Q)
  intro hS
  obtain ⟨P,hP⟩ := hS
  have hQT : Q ≤ (T : Subgroup G) := by
    rw [show Q = (L ⊔ (T : Subgroup G)).pCoreIn 2 from rfl,
      ←d.sylow_centralizer d.normalizes_L]
    exact inf_le_left
  have hn : Q ≤ normalizer (R : Set G) :=
    hQT.trans (hH.1.1.2.trans (le_normalizer_embedded_pResidual 2 H))
  have hQS : Chapter1.IsSylowIn 2 Q (R ⊔ Q) :=
    (isPGroup_pCoreIn 2 _).exists_sylow_sup_of_smaller_sylow R
      (ChapterB.baumann Q) Q inf_le_left hn P hP
  have hne : Q ≠ ⊥ := by
    intro he
    exact d.chosen.ne_bot (bot_unique (d.chosen.le_core.trans_eq he))
  exact (qrc_hypotheses d hH).not_residual_sylow
    (Chapter3.source_common_normal_knownSimple d.hypothesis.qtke T)
    hne d.unique_maximal_overgroup hQS

/-- Source 13.2.13 with only its middle Baumann-Sylow transfer left explicit.
The quotient containment, Borel-core Sylow calculation, and final common-normal
contradiction are all discharged on the original groups. -/
theorem not_three_borel_quotient_of_baumann_transfer
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (htransfer : let R := (pResidual 2 H).map H.subtype
      let R₁ := (borelResidual T L ⊔ (T : Subgroup G)).pCoreIn 2
      ¬ R ≤ normalizer (elementaryAbelianMaxJ R₁ : Set G) →
      Chapter1.IsSylowIn 2 R₁ (R ⊔ R₁) →
        Chapter1.IsSylowIn 2 (ChapterB.baumann R₁) (R ⊔ ChapterB.baumann R₁)) :
    let J := H ⊔ borelResidual T L
    ¬ IsPGroup 3 (pResidual 2 (J ⧸ pPrimeCore 3 J)) := by
  dsimp only
  intro hthree
  apply local_core_baumann_not_sylow d hH
  have hh := htransfer (residual_not_normalizes_borel_core_thompson d hH)
    (borel_core_sylow_of_three_quotient d hH hB hZ hs hthree)
  simpa only [(borel_core_thompson_baumann d).2] using hh

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
