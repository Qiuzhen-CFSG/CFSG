module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentCoveredRadical
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFiveExclusion

/-!
# Excluding the selected A₅ component in both original covering rows

The genuine earlier A₅ module clause marks the entire moved omega-orbit.
The reciprocal radical theorem identifies the original R=O₂(L₁T) inside
KR=K R(T∩K). The marked point theorem there gives J(R)=J(O₂(KR)) and
Baum(R)=Baum(O₂(KR)). Thus K normalizes Baum(R), contradicting the original
covered normalizer bound. No containment L₁≤K, shortness, or additional
whole-module marking is assumed.

Combining this with the checked ordinary A₅ exclusion removes the original
covering-row hypothesis. Only the ordinary branch uses LargeDistanceInput,
whose producer is qt-e-ms-small-a6-exhaustion-large-distance. Earlier source
premises retain their producers and final discharge with
qt-d-1341-fixed-core-source. The remaining component rows, comparison,
commutator and graph arguments stay with qt-d-1341-nonsolvable-source;
universal nonsolvability at both escaping weights is still required.
Source: Aschbacher–Smith 13.4.10(1), printed p.908.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

private theorem nine_not_dvd_five
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) : ¬ 9 ∣ Nat.card K := by
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
  have he : Nat.card K = 60 * 2^n := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 K),
      Nat.card_congr eK.toEquiv,nat_card_alternatingGroup,hn]
    norm_num [Nat.factorial]
  rw [he]
  intro hd
  exact (by decide : ¬ 9 ∣ 60)
    (((by decide : Nat.Coprime 9 2).pow_right n).dvd_mul_right.mp hd)

private theorem component_sylow_in_original
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    ∃ S : Sylow 2 K, (S : Subgroup K).map K.subtype ≤ (T : Subgroup G) := by
  let X := K ⊔ (T : Subgroup G)
  let N := K.subgroupOf X
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  obtain ⟨Q,hQ⟩ := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).exists_sylow_map_eq_inf_of_normal N
  let e : N ≃* K := subgroupOfEquivOfLe (show K ≤ X from le_sup_left)
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change ((Q : Subgroup N).map e.toMonoidHom).map K.subtype ≤ _
  have he : ((Q : Subgroup N).map e.toMonoidHom).map K.subtype =
      ((Q : Subgroup N).map N.subtype).map X.subtype := by
    rw [map_map,map_map]
    rfl
  rw [he,hQ]
  exact (map_mono inf_le_left).trans (by
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X from le_sup_right)])

/-- The selected A₅ component normalizes the original covered point Baumann
subgroup. The calculation takes place in KR, retaining the source radical R. -/
theorem covered_five_original_baumann
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    elementaryAbelianMaxJ R = elementaryAbelianMaxJ ((K ⊔ R).pCoreIn 2) ∧
      ChapterB.baumann R = ChapterB.baumann ((K ⊔ R).pCoreIn 2) ∧
      K ≤ normalizer (ChapterB.baumann R : Set G) := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  let P := Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)
  let R := P.pCoreIn 2
  let X := K ⊔ R
  let Y := K ⊔ (T : Subgroup G)
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  have hTK := (h1332 K hfK).1
  have hPR : P ≤ normalizer (R : Set G) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have hRT : R ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 P).le_sylow_of_normalized T (le_sup_right.trans hPR)
  have hXY : X ≤ Y := sup_le le_sup_left (hRT.trans le_sup_right)
  have hYX : Y ≤ normalizer (X : Set G) := sup_le
    (le_sup_left.trans X.le_normalizer)
    ((le_inf hTK (le_sup_right.trans hPR)).trans (normalizer_inf_normalizer_le_normalizer_sup K R))
  obtain ⟨DK,qK,e,he⟩ := component_five_marking h₀ h structural D m
    h1332 modules hzT hz1 hKz hHN hKM hfK eK
  have hUK : U ≤ K := (component_moved_le_twoCore h₀ hzT hz1 hKz hTK).trans (pCoreIn_le 2 K)
  have hUX : U ≤ X := hUK.trans le_sup_left
  let Ki := K.subgroupOf X
  let Ui := U.subgroupOf X
  let ek : Ki ≃* K := subgroupOfEquivOfLe (show K ≤ X from le_sup_left)
  let eu : Ui ≃* U := subgroupOfEquivOfLe hUX
  let : Ki.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer (hRT.trans hTK))
  have hred := component_moved_reduced h₀ hzT hz1 hKz hTK
  let : (U.subgroupOf Y).Normal := hred.normal
  have hYU : Y ≤ normalizer (U : Set G) := by
    have hn := (map_mono (f := Y.subtype)
      (show (⊤ : Subgroup Y) ≤ normalizer (U.subgroupOf Y : Set Y) from le_normalizer_of_normal)).trans
        ((U.subgroupOf Y).le_normalizer_map Y.subtype)
    rwa [←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le (hUK.trans (show K ≤ Y from le_sup_left))] at hn
  let : Ui.Normal := normal_subgroupOf_of_le_normalizer (hXY.trans hYU)
  let := DK.elementary
  let : IsElementaryAbelian 2 Ui := IsElementaryAbelian.subgroupOf hUX
  let q0 := qK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let q := q0.comp ek.toMonoidHom
  have hq : Function.Surjective q :=
    (qK.surjective.comp (QuotientGroup.mk'_surjective _)).comp ek.surjective
  have hk : q.ker = pCore 2 Ki := by
    change q0.ker.comap ek.toMonoidHom = _
    have hq0 : q0.ker = pCore 2 K := by
      rw [MonoidHom.ker_comp_of_injective _ _ qK.injective,QuotientGroup.ker_mk']
    rw [hq0]
    exact ek.toMonoidHom.comap_pCore_of_ker_isPGroup ek.surjective
      (IsPGroup.ker_isPGroup_of_injective ek.injective)
  let ei := eu.trans e
  have hei (k : Ki) (u : Ui) : (ei (MulAut.conjNormal k.val u)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 5) (q k).val (ei u).toAdd := by
    exact he (ek k) (eu u)
  have hquot : IsPGroup 2 (X ⧸ Ki) := by
    apply isPGroup_quotient_of_sup_eq_top Ki (R.subgroupOf X)
      ((isPGroup_pCoreIn 2 P).comap_subtype)
    rw [←subgroupOf_sup (show K ≤ X from le_sup_left)
      (show R ≤ X from le_sup_right),subgroupOf_self]
  have hcore : pCore 2 X ≤ centralizer (Ui : Set X) := by
    intro x hx u hu
    exact Subtype.ext (DK.core_centralizes
      ((pCoreIn_mono_of_normalizes hXY hYX) (mem_map_of_mem X.subtype hx)) u.val hu)
  obtain ⟨w,hw,hTw,hpoint⟩ := component_fixed_generator_point_overgroup h₀ h structural m
    hzT hz1 hKz hTK hKM
  let wi := eu.symm w
  have hwi : wi ≠ 1 := fun hh => hw (by simpa [wi] using congrArg eu hh)
  obtain ⟨S,hS⟩ := component_sylow_in_original hTK
  let Si := S.mapSurjective (f := ek.symm.toMonoidHom) ek.symm.surjective
  have hSi : (Si : Subgroup Ki).map Ki.subtype ≤ centralizer ({wi.val} : Set X) := by
    rintro x ⟨a,ha,rfl⟩
    obtain ⟨k,hk,hka⟩ := (show a ∈ (S : Subgroup K).map ek.symm.toMonoidHom from ha)
    rw [←hka]
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hTw (hS (mem_map_of_mem K.subtype hk))))
  have hb := ChapterB.AlternatingFivePoint.overgroup_point_baumann Ki Ui q hq hk ei hei
    hquot hcore wi hwi Si hSi
  let C := centralizer ({wi.val} : Set X)
  have hCm : C.map X.subtype = X ⊓ centralizer ({m.constant.val} : Set G) := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,(hpoint.ge ⟨hXY a.property,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha))⟩).2⟩
    · rintro ⟨hx,hc⟩
      exact ⟨⟨x,hx⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp (hpoint.le ⟨hXY hx,hc⟩).2)),rfl⟩
  have h23 := (five_component_reciprocal_structure h₀ h structural D m h1332 modules
    hzT hz1 hKz hHN hKM hfK eK).2.1
  have hRm : (C.pCoreIn 2).map X.subtype = R := by
    rw [map_pCoreIn_of_injective 2 _ _ X.subtype_injective,hCm]
    exact covered_component_point_radical h structural D m hc z hzT hzL hKz hHN h23
      (nine_not_dvd_five eK)
  have hm := congrArg (fun A : Subgroup X => A.map X.subtype) hb.2.1
  change (ChapterB.baumann (C.pCoreIn 2)).map X.subtype = (ChapterB.baumann (pCore 2 X)).map X.subtype at hm
  dsimp only [ChapterB.baumann,ChapterB.thompsonAlpha] at hm
  rw [baumann_map_injective X.subtype X.subtype_injective,
    baumann_map_injective X.subtype X.subtype_injective,hRm] at hm
  have hj := congrArg (fun A : Subgroup X => A.map X.subtype) hb.1
  change (elementaryAbelianMaxJ (C.pCoreIn 2)).map X.subtype =
    (elementaryAbelianMaxJ (pCore 2 X)).map X.subtype at hj
  rw [←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,
    ←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,hRm] at hj
  change ChapterB.baumann R = ChapterB.baumann (X.pCoreIn 2) at hm
  refine ⟨hj,hm,?_⟩
  rw [hm]
  exact (show K ≤ X from le_sup_left).trans ((X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))).trans
      (normalizer_le_normalizer_baumann (X.pCoreIn 2)))

/-- The covered original augmentation row has no escaping selected A₅ component. -/
theorem covered_five_excluded
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) : False := by
  exact hKM ((covered_five_original_baumann h₀ h structural D m h1332 modules hc z hzT hzL
    hKz hHN hKM hfK eK).2.2.trans
      (covered_augmentation_baumann_normalizer h structural D m hc z hzT hzL))


open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural AlternatingSixReconstruction.Natural.Exhaustion

/-- Neither ordinary nor covered original augmentation admits the selected A₅ row.
The independent natural large-distance input is used only in the ordinary branch. -/
theorem five_excluded_of_largeDistance
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) : False := by
  let := h.quasisimple
  have hn : ¬ 2 ∣ Nat.card (center (L ⧸ pCore 2 L)) :=
    PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) (center (L ⧸ pCore 2 L)) le_rfl
  have ho : Odd (Nat.card (center (L ⧸ pCore 2 L))) :=
    Nat.not_even_iff_odd.mp (fun he => hn (even_iff_two_dvd.mp he))
  rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide)
    (augmentationCentralQuotient D m) ho with hc | ⟨_,hc⟩
  · let eL := GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 6
      (augmentationCentralQuotient D m) hc
    exact ordinary_five_excluded_of_largeDistance hl h₀ h structural D m h1332 modules
      eL z hzT hzL hKz hHN hKM hfK eK
  · exact covered_five_excluded h₀ h structural D m h1332 modules hc z hzT hzL
      hKz hHN hKM hfK eK


end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
