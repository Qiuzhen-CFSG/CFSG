module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.BorelSylow
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.NormalSupplement

/-!
# The original Borel-join quotient exclusion

The two-core R₁ of the original Borel supplement L₁T is normalized by T
and contains Ω₁Z(T). When R₁ is Sylow in O²(H)R₁, the normal-supplement
Baumann theorem applies inside the original minimal parabolic H. Its
native omega orbit is precisely U_H, whose centralizer is O₂(H) by the
proved original 13.2.9. The failure of O²(H) to normalize J(R₁) then gives
Baum(R₁) Sylow in O²(H)Baum(R₁).

Combining this transfer with BorelSylow's quotient calculation and final
common-normal contradiction proves 13.2.13 from the original Context,
outside movement, earlier Baumann normalizer bound and solvability.
No Sylow-transfer or quotient-exclusion premise remains. The independent
Baumann bound and solvability discharge remain with qt-d-1367-assembly;
SourceAssembly/BorelSylow applies the result in the terminal argument.

Source: Aschbacher--Smith 13.2.13, printed p.883, and Stellmacher (2.3),
Journal of Algebra 190 (1997), pp.20,26.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- The middle transfer of 13.2.13 on the literal original Borel core. -/
theorem borel_core_baumann_sylow
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hSyl : let R₁ := (borelResidual T L ⊔ (T : Subgroup G)).pCoreIn 2
      Chapter1.IsSylowIn 2 R₁ ((pResidual 2 H).map H.subtype ⊔ R₁)) :
    let R₁ := (borelResidual T L ⊔ (T : Subgroup G)).pCoreIn 2
    Chapter1.IsSylowIn 2 (ChapterB.baumann R₁)
      ((pResidual 2 H).map H.subtype ⊔ ChapterB.baumann R₁) := by
  let P := borelResidual T L ⊔ (T : Subgroup G)
  let K := L ⊔ (T : Subgroup G)
  let R₁ := P.pCoreIn 2
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hRT : R₁ ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow P (T.subtype (show (T : Subgroup G) ≤ P from le_sup_right))
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ P from le_sup_right)] at hh
  have hTR : (T : Subgroup G) ≤ normalizer (R₁ : Set G) :=
    ((le_sup_right : (T : Subgroup G) ≤ P).trans P.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have hQT : K.pCoreIn 2 ≤ (T : Subgroup G) :=
    (d.sylow_centralizer d.normalizes_L).ge.trans inf_le_left
  have hAL : borelResidual T L ≤ L := by
    rw [borelResidual_eq_point_residual d]
    exact Section05.A5Source.ThirdSpace.residual_le_centralizer.trans inf_le_left
  have hPK : P ≤ K := sup_le_sup hAL le_rfl
  have hQR : K.pCoreIn 2 ≤ R₁ := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 K) (hQT.trans le_sup_right)
    ((hPK.trans K.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  have hZQ : omegaOneCenterAmbient (T : Subgroup G) ≤ K.pCoreIn 2 := by
    rw [show K = L ⊔ (T : Subgroup G) from rfl,←d.sylow_centralizer d.normalizes_L]
    intro z hz
    have hh := (mem_omegaOneCenterAmbient_iff _ _).mp hz
    exact ⟨hh.1, fun v hv => hh.2.2 v (d.chosen.le_sylow hv)⟩
  have hZR : omegaOneCenterAmbient (T : Subgroup G) ≤ R₁ := hZQ.trans hQR
  let S := T.subtype hTH
  let R := R₁.subgroupOf H
  have hRm : R.map H.subtype = R₁ := map_subgroupOf_eq_of_le (hRT.trans hTH)
  have hZTH : omegaOneCenterAmbient (T : Subgroup G) ≤ H :=
    fun _ hz => hTH ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hz : omegaOneCenterAmbient (S : Subgroup H) =
      (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hZTH]
    congr 1
    exact map_subgroupOf_eq_of_le hTH
  have hv : Stellmacher.SectionTwo.vSubgroup S = (omegaOrbit T H).subgroupOf H := by
    change normalClosure (omegaOneCenterAmbient (S : Subgroup H) : Set H) = _
    rw [hz,normalClosure_subgroupOf_eq_conjugateSpanBy _ H hZTH]
  have hc : pCore 2 H = (S : Subgroup H) ⊓
      centralizer (Stellmacher.SectionTwo.vSubgroup S : Set H) := by
    rw [hv,source_omega_centralizer_eq_twoCore d hH hB hZ hs,
      inf_eq_right.mpr (pCore_isPGroup.le_sylow_of_normal S)]
  have heven : Even (Nat.card H) := by
    have hne : pCore 2 H ≠ ⊥ := by
      intro he
      apply hH.1.1.1
      change (pCore 2 H).map H.subtype = ⊥
      rw [he,Subgroup.map_bot]
    rcases (pCore_isPGroup (p := 2) (G := H)).card_eq_or_dvd with he | he
    · exact (hne (card_eq_one.mp he)).elim
    · exact even_iff_two_dvd.mpr (he.trans (pCore 2 H).card_subgroup_dvd_card)
  have hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
      (d.hypothesis.qtke.evenCharacteristic T) hH.1.1)
  have hn : ¬ pResidual 2 H ≤ normalizer (elementaryAbelianMaxJ R : Set H) := by
    intro hn
    apply residual_not_normalizes_borel_core_thompson d hH
    have hm := (map_mono (f := H.subtype) hn).trans (le_normalizer_map H.subtype)
    rwa [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hRm] at hm
  have hsyl : Chapter1.IsSylowIn 2 R (pResidual 2 H ⊔ R) := by
    apply (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).mp
    simpa only [Subgroup.map_sup,hRm] using hSyl
  have hh := ChapterB.RankOneBaumann.normal_supplement_baumann_sylow
    ⟨hs,heven,hchar⟩ S (e23_hypotheses d.hypothesis.qtke T d.normalizes_L hH hB hZ).2.2.1 R
    (show R ≤ (S : Subgroup H) from comap_mono hRT)
    ((comap_mono hTR).trans (le_normalizer_comap H.subtype))
    (show omegaOneCenterAmbient (S : Subgroup H) ≤ R by rw [hz]; exact comap_mono hZR)
    hn hsyl hc
  have hBm : (ChapterB.baumann R).map H.subtype = ChapterB.baumann R₁ := by
    change (R ⊓ centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ R) : Set H)).map
      H.subtype = _
    rw [baumann_map_injective H.subtype H.subtype_injective,hRm]
    rfl
  have hm := (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).mpr hh
  simpa only [Subgroup.map_sup,hBm] using hm

/-- Original 13.2.13, retaining only the genuine earlier Baumann and
solvability inputs. -/
theorem not_three_borel_quotient
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) :
    let J := H ⊔ borelResidual T L
    ¬ IsPGroup 3 (pResidual 2 (J ⧸ pPrimeCore 3 J)) := by
  apply not_three_borel_quotient_of_baumann_transfer d hH hB hZ hs
  dsimp only
  intro _ hsyl
  exact borel_core_baumann_sylow d hH hB hZ hs hsyl

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
