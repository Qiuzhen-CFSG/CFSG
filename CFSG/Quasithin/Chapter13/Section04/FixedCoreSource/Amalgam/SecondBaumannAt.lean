module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondBaumann
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondPointAt
public import CFSG.Quasithin.ChapterB.Section02.DoubledOvergroupPointBaumann
public import Stellmacher.BaumannMap

/-!
This guarded version uses earlier structure only at the original G,T.
All literal residuals, quotient maps and original source hypotheses are retained.

# Baumann normalization in the actual second join

The original first vertex is the full centralizer of the constant seed
point. The doubled-natural normalizer theorem applies to its entire
two-core, including actors outside the component. It identifies both
J(O₂(P)) and Baum(O₂(P)) with those of O₂(Y). Consequently Y normalizes
this Baumann subgroup and its full normalizer escapes N_G(L).

All maps are transported through the same intrinsic component and omega
span. No Thompson containment or Baumann normalization is assumed.
Source: Aschbacher--Smith 13.4.7(3), printed pp.903--904, using B.2.3(5).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- The original first-vertex radical has the Thompson and Baumann subgroups
of the second join's radical; its Baumann normalizer therefore escapes. -/
theorem original_plane_second_baumann_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcentral : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂))
    (hs : Group.IsSolvable (A ⊔ B : Subgroup G))
    (hcomm : ¬ ⁅(pResidual 2 A).map A.subtype,(pResidual 2 B).map B.subtype⁆ ≤
      centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G))
    (Wplane : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hWplane : Module.finrank (ZMod 2) Wplane = 2)
    (hTplane : (T : Subgroup G) ≤ normalizer (m.naturalPreimage Wplane : Set G))
    (hBplane : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage Wplane : Set G))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (h1332 : Source1332OneTwo T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (covered : Nonsolvable.OriginalCoveredNatural1332At T L)
    (h13316 : ∀ C : Subgroup G, Hypothesis1331 T C →
      ¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 3) :
    let X := A ⊔ B
    let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
    let P := firstFlagNormalizer T L V
    let Y := P ⊔ (Y₂ ⊔ (T : Subgroup G))
    elementaryAbelianMaxJ (P.pCoreIn 2) = elementaryAbelianMaxJ (Y.pCoreIn 2) ∧
      ChapterB.baumann (P.pCoreIn 2) = ChapterB.baumann (Y.pCoreIn 2) ∧
      Y ≤ normalizer (ChapterB.baumann (P.pCoreIn 2) : Set G) ∧
      ¬ normalizer (ChapterB.baumann (P.pCoreIn 2) : Set G) ≤ normalizer (L : Set G) := by
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
  let P := firstFlagNormalizer T L V
  let Y := P ⊔ (Y₂ ⊔ (T : Subgroup G))
  let U := conjugateSpanBy Z Y
  have hTP : (T : Subgroup G) ≤ P := sylow_le_firstFlagNormalizer
  have hTY : (T : Subgroup G) ≤ Y := hTP.trans le_sup_left
  have hUY : U ≤ Y := conjugateSpanBy_le (fun z hz =>
    hTY ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) Y.le_normalizer
  let S := T.subtype hTY
  let Ui := U.subgroupOf Y
  obtain ⟨_,_,_,_,_,_,_,hYout,hred,_⟩ :=
    original_plane_second_amalgam_at h₀ h structural D m hTA hTB eA eB hne
      hindexL hindexA hindexB hcentral hs hcomm Wplane hWplane hTplane hBplane
  obtain ⟨K,hK,hn,hf,hstar,hTK,hm,⟨eK,e,he⟩,hker,hr,hgen,hP,hY₂,hJ,hmove,hcard,hfix⟩ :=
    exists_original_plane_second_doubled_at h₀ h structural D m hTA hTB eA eB hne
      hindexL hindexA hindexB hcentral hs hcomm Wplane hWplane hTplane hBplane hM
      h1332 modules fixed covered h13316
  let := hn
  let : Ui.Normal := hred.normal
  let : IsElementaryAbelian 2 Ui := hred.elementary
  let j := K.equivMapOfInjective Y.subtype Y.subtype_injective
  let eu := subgroupOfEquivOfLe hUY
  let q0 := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (K.map Y.subtype)))
  let q := q0.comp j.toMonoidHom
  have hq : Function.Surjective q :=
    (eK.surjective.comp (QuotientGroup.mk'_surjective _)).comp j.surjective
  have hk : q.ker = pCore 2 K := by
    change q0.ker.comap j.toMonoidHom = _
    have hq0 : q0.ker = pCore 2 (K.map Y.subtype) := by
      rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
    rw [hq0]
    exact j.toMonoidHom.comap_pCore_of_ker_isPGroup j.surjective
      (IsPGroup.ker_isPGroup_of_injective j.injective)
  let ei := eu.trans e
  have hei (k : K) (v : Ui) : (ei (MulAut.conjNormal k.val v)).toAdd =
      (BinaryLinearThree.W.prod BinaryLinearThree.W) (q k) (ei v).toAdd :=
    he (j k) (eu v)
  have hKS : K ⊔ (S : Subgroup Y) = ⊤ := by
    rw [←hr]
    exact pResidual_sup_sylow_eq_top S
  have hquot : IsPGroup 2 (Y ⧸ K) :=
    isPGroup_quotient_of_sup_eq_top K (S : Subgroup Y) S.isPGroup' hKS
  have hz : m.constant.val ∈ Z := (m.constant_mem_central_four_at h structural).2
  have hzu : m.constant.val ∈ U := le_conjugateSpanBy Z Y hz
  let w : Ui := ⟨⟨m.constant.val,hUY hzu⟩,hzu⟩
  have hw : w ≠ 1 := fun hh => m.constant_ne_one
    (Subtype.ext (congrArg (fun v : Ui => v.val.val) hh))
  obtain ⟨R,hR⟩ := S.exists_sylow_map_eq_inf_of_normal K
  have hRw : (R : Subgroup K).map K.subtype ≤ centralizer ({w.val} : Set Y) := by
    rw [hR]
    intro r hr
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 r.val hr.1)
  have hb := ChapterB.doubled_overgroup_point_baumann K Ui q hq hk ei hei hquot
    (le_centralizer_iff.mp hred.le_centralizer_pCore) w hw R hRw
  have hp := (original_plane_second_point_parabolic_at h₀ h structural D m
    hTA hTB eA eB hne hindexL hindexA hindexB hcentral hs hcomm
    Wplane hWplane hTplane hBplane hM h1332 modules fixed covered h13316).2.2.2
      m.constant.val hz (fun hh => m.constant_ne_one (Subtype.ext hh))
  let C := centralizer ({w.val} : Set Y)
  change Y ⊓ centralizer ({m.constant.val} : Set G) = P at hp
  have hCm : C.map Y.subtype = P := by
    rw [←hp]
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha))⟩
    · rintro ⟨hx,hc⟩
      exact ⟨⟨x,hx⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hc)),rfl⟩
  have hj := congrArg (map Y.subtype) hb.1
  change (elementaryAbelianMaxJ (C.pCoreIn 2)).map Y.subtype =
    (elementaryAbelianMaxJ (pCore 2 Y)).map Y.subtype at hj
  rw [←elementaryAbelianMaxJ_map_injective Y.subtype Y.subtype_injective,
    ←elementaryAbelianMaxJ_map_injective Y.subtype Y.subtype_injective,
    map_pCoreIn_of_injective 2 C Y.subtype Y.subtype_injective,hCm] at hj
  have hm := congrArg (map Y.subtype) hb.2.1
  change (ChapterB.baumann (C.pCoreIn 2)).map Y.subtype =
    (ChapterB.baumann (pCore 2 Y)).map Y.subtype at hm
  dsimp only [ChapterB.baumann,ChapterB.thompsonAlpha] at hm
  rw [baumann_map_injective Y.subtype Y.subtype_injective,
    baumann_map_injective Y.subtype Y.subtype_injective,
    map_pCoreIn_of_injective 2 C Y.subtype Y.subtype_injective,hCm] at hm
  change ChapterB.baumann (P.pCoreIn 2) = ChapterB.baumann (Y.pCoreIn 2) at hm
  have hnorm : Y ≤ normalizer (ChapterB.baumann (P.pCoreIn 2) : Set G) := by
    rw [hm]
    exact (Y.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))).trans
      (normalizer_le_normalizer_baumann (Y.pCoreIn 2))
  exact ⟨hj,hm,hnorm,fun hh => hYout.2 (hnorm.trans hh)⟩


end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
