module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondShortExclusion
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinaryBaumannAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondBaumannAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentChief
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationAlternative
public import Theory.GroupTheory.PResidual.SylowCentralizer

/-!
This guarded version uses earlier structure only at the original G,T.
All literal residuals, quotient maps and original source hypotheses are retained.

# The chief-factor contradiction for the original solvable plane pair

The same second omega span U lies in the first vertex P and normalizes
its two-residual L₁. The doubled point-centralizer map constructs the
actual A₄ quotient of L₁ above its intersection with O₂(K_Y). A cubic
of L₁ has length two on U, while the original five-dimensional short
block gives length at most one on that quotient kernel. The checked
chief comparison yields the contradiction with both kernels retained.

Baumann escape and the genuine augmentation pushing-up alternative now
force shortness, excluding the original solvable noncommuting join,
not just a solvable second join. The independent natural large-distance
input and genuine earlier Chapter12/13.3 inputs remain explicit.
Source: Aschbacher--Smith 13.4.7(3), printed pp.903--904; 13.2.2(7).
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

private theorem residual_four_map (C J Q : Subgroup G)
    (hJ : (pResidual 2 C).map C.subtype = J)
    (q : C →* Equiv.Perm (Fin 4)) (hq : Function.Surjective q)
    (hqk : q.ker = Q.subgroupOf C) :
    ∃ f : J →* alternatingGroup (Fin 4), Function.Surjective f ∧
      f.ker = Q.subgroupOf J := by
  let R := pResidual 2 C
  have hJC : J ≤ C := hJ ▸ map_subtype_le R
  have hr : R.map q = alternatingGroup (Fin 4) :=
    (map_pResidual_of_surjective 2 q hq).trans
      Theory.SpecificGroups.SymmetricFourResidual.residual_eq
  let f : J →* alternatingGroup (Fin 4) :=
    (q.comp (inclusion hJC)).codRestrict _ (fun j => by
      rw [←hr]
      obtain ⟨c,hc,he⟩ := hJ.ge j.property
      have he' : c = inclusion hJC j := Subtype.ext he
      exact mem_map_of_mem q (he' ▸ hc))
  refine ⟨f,?_,?_⟩
  · intro a
    obtain ⟨c,hc,hca⟩ := (show a.val ∈ R.map q from hr.symm ▸ a.property)
    exact ⟨⟨c.val,hJ.le (mem_map_of_mem C.subtype hc)⟩,Subtype.ext hca⟩
  · ext j
    change f j = 1 ↔ j.val ∈ Q
    rw [Subtype.ext_iff]
    change inclusion hJC j ∈ q.ker ↔ _
    rw [hqk]
    rfl

/-- The actual second doubled module contradicts the original first-residual
chief budget when L is short; both A₄ quotient kernels are constructed. -/
theorem original_plane_second_short_impossible_at
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
      ¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 3)
    (hb : ChapterC.IsShort L) :
    False := by
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
  have hYn : Y ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy Z Y
  let S := T.subtype hTY
  obtain ⟨_,_,_,_,_,_,_,_,hred,_⟩ :=
    original_plane_second_amalgam_at h₀ h structural D m hTA hTB eA eB hne
      hindexL hindexA hindexB hcentral hs hcomm Wplane hWplane hTplane hBplane
  let : IsElementaryAbelian 2 (U.subgroupOf Y) := hred.elementary
  let : IsElementaryAbelian 2 U := by
    have hh : IsElementaryAbelian 2 ((U.subgroupOf Y).map Y.subtype) := IsElementaryAbelian.map _
    rwa [map_subgroupOf_eq_of_le hUY] at hh
  obtain ⟨K,hK,hn,hf,hstar,hTK,hm,⟨eK,e,he⟩,hker,hr,hgen,hP,hY₂,hJ,hmove,hcard,hfix⟩ :=
    exists_original_plane_second_doubled_at h₀ h structural D m hTA hTB eA eB hne
      hindexL hindexA hindexB hcentral hs hcomm Wplane hWplane hTplane hBplane hM
      h1332 modules fixed covered h13316
  let := hn
  let C := K.map Y.subtype
  have hCY : C ≤ Y := map_subtype_le K
  have hYC : Y ≤ normalizer (C : Set G) := by
    have hh := K.le_normalizer_map Y.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hUC : U ≤ C := hmove.symm.le.trans
    (le_normalizer_iff_commutator_le_right.mp (hUY.trans hYC))
  have hUcore : U ≤ C.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 U) hUC (hCY.trans hYn)
  obtain ⟨eL⟩ := original_plane_ordinary D m Wplane hWplane hTplane hBplane eB
  have hseed := (original_pair_source_seed_at h structural D m hTA hTB eA eB hne
    hindexL hindexA hindexB hcentral).2.1
  have hex : ∃ z ∈ Z, z ∉ centralizer (L : Set G) := by
    by_contra hh
    have hz : Z ≤ centralizer (L : Set G) := by
      intro z hz
      by_contra hn
      exact hh ⟨z,hz,hn⟩
    rw [inf_eq_left.mpr hz,relIndex_self] at hindexL
    omega
  obtain ⟨z,hz,hzL⟩ := hex
  let v : V := ⟨z,(hseed.le hz).1⟩
  let J := firstCentralizerResidual L z
  have hPr : (pResidual 2 P).map P.subtype = J :=
    firstFlagNormalizer_residual_at h structural D m eL v hz hzL
  have hJC : J ≤ C := hPr ▸ hP
  have hwZ : m.constant.val ∈ Z := (m.constant_mem_central_four_at h structural).2
  let w : U := ⟨m.constant.val,le_conjugateSpanBy Z Y hwZ⟩
  have hw : w ≠ 1 := fun hh => m.constant_ne_one (Subtype.ext (congrArg (fun u : U => u.val) hh))
  have hTw : (T : Subgroup G) ≤ centralizer ({w.val} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      (((mem_omegaOneCenterAmbient_iff _ _).mp hwZ).2.2 t ht)
  have hp := (original_plane_second_point_parabolic_at h₀ h structural D m
    hTA hTB eA eB hne hindexL hindexA hindexB hcentral hs hcomm
    Wplane hWplane hTplane hBplane hM h1332 modules fixed covered h13316).2.2.2
      w.val hwZ (fun hh => hw (Subtype.ext hh))
  change Y ⊓ centralizer ({w.val} : Set G) = P at hp
  have hUP : U ≤ P := by
    rw [←hp]
    refine le_inf hUY ?_
    intro u hu
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨u,hu⟩ : U) w))
  have hUJ : U ≤ normalizer (J : Set G) := by
    rw [←hPr]
    exact hUP.trans (P.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image P (pResidual 2 P)))
  let j := K.equivMapOfInjective Y.subtype Y.subtype_injective
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal K
  let Rc := R.mapSurjective (f := j.toMonoidHom) j.surjective
  have hRc : (Rc : Subgroup C).map C.subtype ≤ (T : Subgroup G) := by
    rintro x ⟨k,hk,rfl⟩
    obtain ⟨a,ha,rfl⟩ := (show k ∈ (R : Subgroup K).map j.toMonoidHom from hk)
    rw [hR] at ha
    exact ha
  obtain ⟨p,hps,hpk⟩ := BinaryLinearThree.doubled_point_centralizer_of_sylow C U
    (hCY.trans hYn) eK e he w hw Rc (hRc.trans hTw)
  let N := C ⊓ centralizer ({w.val} : Set G)
  let Rn := (pResidual 2 N).map N.subtype
  have hTN : (T : Subgroup G) ≤ normalizer (N : Set G) :=
    (le_inf hTK (hTw.trans (centralizer ({w.val} : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hTR : (T : Subgroup G) ≤ normalizer (Rn : Set G) :=
    hTN.trans (normalizer_le_normalizer_characteristic_image N (pResidual 2 N))
  have hjoin : Rn ⊔ (T : Subgroup G) = P := by
    have hh := embedded_pointResidual_sup_sylow T C hTK w.val hTw
    rw [←hgen] at hh
    exact hh.trans hp
  have hrJ : Rn = J := by
    rw [←hPr,←hjoin]
    exact (embedded_pResidual_join_pGroup Rn (T : Subgroup G)
      (isPPerfect_embedded_pResidual 2 N) T.isPGroup' hTR).symm
  obtain ⟨f,hfs,hfk⟩ := residual_four_map N J (C.pCoreIn 2) hrJ p hps hpk
  exact Nonsolvable.core_block_excludes_doubled_component D m hb eL v hzL C U
    hJC (hCY.trans hYn) hUcore hUJ eK e he f hfs hfk

/-- Exclude the original solvable noncommuting plane pair. The sole remaining
pushing-up input is the independent natural large-distance theorem. -/
theorem original_plane_solvable_noncommuting_impossible_of_largeDistance_at
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
      ¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 3)
    (hl : Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistanceInput.{u}
        KnownSimple.IsKnownSimple) :
    False := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let P := firstFlagNormalizer T L V
  obtain ⟨eL⟩ := original_plane_ordinary D m Wplane hWplane hTplane hBplane eB
  have hseed := (original_pair_source_seed_at h structural D m hTA hTB eA eB hne
    hindexL hindexA hindexB hcentral).2.1
  have hex : ∃ z ∈ Z, z ∉ centralizer (L : Set G) := by
    by_contra hh
    have hz : Z ≤ centralizer (L : Set G) := by
      intro z hz
      by_contra hn
      exact hh ⟨z,hz,hn⟩
    rw [inf_eq_left.mpr hz,relIndex_self] at hindexL
    omega
  obtain ⟨z,hz,hzL⟩ := hex
  let v : V := ⟨z,(hseed.le hz).1⟩
  have hP : P = firstCentralizerResidual L z ⊔ (T : Subgroup G) :=
    first_flag_normalizer_eq_firstResidual_sylow_at h structural D m eL v hz hzL
  have hcases := LocalGeometry.ordinary_augmentation_baumann_alternative_of_largeDistance_at
    hl h structural D m eL v hz hzL
  change normalizer (ChapterB.baumann ((firstCentralizerResidual L z ⊔
    (T : Subgroup G)).pCoreIn 2) : Set G) ≤ normalizer (L : Set G) ∨ ChapterC.IsShort L at hcases
  rw [←hP] at hcases
  rcases hcases with hbound | hshort
  · exact (original_plane_second_baumann_at h₀ h structural D m hTA hTB eA eB hne
      hindexL hindexA hindexB hcentral hs hcomm Wplane hWplane hTplane hBplane hM
      h1332 modules fixed covered h13316).2.2.2 hbound
  · exact original_plane_second_short_impossible_at h₀ h structural D m hTA hTB eA eB hne
      hindexL hindexA hindexB hcentral hs hcomm Wplane hWplane hTplane hBplane hM
      h1332 modules fixed covered h13316 hshort


end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
