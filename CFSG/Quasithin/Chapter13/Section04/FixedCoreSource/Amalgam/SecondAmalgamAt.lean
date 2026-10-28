module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondAmalgam
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.FirstFlagNormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.FirstFlagCore
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.PlaneOrdinary
public import Theory.GroupTheory.NormalSymmetricThreeExtension
public import Theory.GroupAction.MarkedCubicRecognition.CentralParabolic
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.CentralResidualAt
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.GoldschmidtSize.Complete

/-!
This guarded version uses earlier structure only at the original G,T.
All literal residuals, quotient maps and original source hypotheses are retained.

# The original second Goldschmidt triple

In the solvable noncommuting plane case, the actual first flag normalizer
is L₁T and centralizes Z=Ω₁Z(T). The central-preimage residual Y₂, already
constructed in the original join X, gives the other S₃ parabolic Y₂T.
Its escape from N_G(L) makes the two vertices distinct.

The original omega span has order 64 inside O₂(X), and the same Heisenberg
quotient gives |T|=4|O₂(X)|≥256. The complete Gol80 bound is at most 128
for a core-free triple, so the second join Y has nonzero two-core. Ambient
characteristic two now makes its literal omega span two-reduced. The
right vertex retains the ordinary Thompson normality from X and has
literal two-residual Y₂, with [Y₂,T]=Y₂.

This constructs the second triple and its locality, without an extra
amalgam or chief-count premise. Its full action kernel, subsequent F.6
selection and terminal doubled-natural contradiction are not asserted.
Source: Aschbacher--Smith 13.4.7(3), printed p.903; Goldschmidt (1980),
Theorem A and Table 1 for the completed common-Sylow bound.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original first flag is an S₃ parabolic fixing the whole original seed. -/
theorem ordinary_firstFlag_parabolic_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    Nonempty (((firstFlagNormalizer T L V) ⧸ pCore 2 (firstFlagNormalizer T L V)) ≃*
      Equiv.Perm (Fin 3)) ∧
      firstFlagNormalizer T L V ≤
        centralizer ((V ⊓ omegaOneCenterAmbient (T : Subgroup G) : Subgroup G) : Set G) := by
  let C := L ⊓ centralizer ({z.val} : Set G)
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf D.sylow_normalizes_component
      ((original_sylow_le_centralizer hz).trans (centralizer ({z.val} : Set G)).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
  have hflag := first_flag_normalizer_eq_centralizer_at h structural D m z hz hzL
  change firstFlagNormalizer T L V = _ at hflag
  have hCT : C ⊔ (T : Subgroup G) = firstFlagNormalizer T L V := by
    apply le_antisymm
    · rw [hflag]
      exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
        (le_inf le_sup_right (original_sylow_le_centralizer hz))
    · rw [hflag,local_centralizer_eq_firstResidual_sylow D m e z hz hzL]
      exact sup_le_sup_right (firstCentralizerResidual_le L z.val) _
  obtain ⟨ec⟩ := component_centralizer_quotient D m
    (by rw [centralCore_eq_twoCore_of_ordinary e]; exact pCore_isPGroup) z hzL
  have he := NormalSymmetricThreeExtension.normalized_join C (T : Subgroup G) hTC ec T.isPGroup'
  rw [hCT] at he
  refine ⟨he,?_⟩
  apply le_centralizer_iff.mpr
  rw [first_fixed_plane_eq_at h structural D m z hz hzL]
  apply sup_le
  · exact le_centralizer_iff.mp
      ((inf_le_left.trans (sup_le L.le_normalizer D.sylow_normalizes_component)).trans
        (normalizer_component_le_fixed_centralizer_at h structural D m))
  · apply le_centralizer_iff.mp
    rw [zpowers_eq_closure,centralizer_closure,hflag]
    exact inf_le_right


variable {A B : Subgroup G}

/-- Construct the actual second Goldschmidt triple and its nonzero core from
the original solvable plane alternative, retaining the two-residual Y₂. -/
theorem original_plane_second_amalgam_at
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
    (hBplane : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage Wplane : Set G)) :
    let X := A ⊔ B
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
    let P := firstFlagNormalizer T L V
    let Q := Y₂ ⊔ (T : Subgroup G)
    let Y := P ⊔ Q
    256 ≤ Nat.card T ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 3)) ∧
      P ≤ centralizer (Z : Set G) ∧ P ≠ Q ∧ P ⊓ Q = (T : Subgroup G) ∧
      ChapterF.IsGoldschmidtTriple (P.subgroupOf Y) (Q.subgroupOf Y) ∧
      Y ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G) ∧
      IsPReduced 2 ((conjugateSpanBy Z Y).subgroupOf Y) ∧
      ⁅Y₂,(T : Subgroup G)⁆ = Y₂ ∧
      (pResidual 2 Q).map Q.subtype = Y₂ ∧
      Q ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z X
  let R := MarkedCubicRecognition.centralThreeResidual X
  let Y₂ := R.map X.subtype
  let P := firstFlagNormalizer T L V
  let Q := Y₂ ⊔ (T : Subgroup G)
  let Y := P ⊔ Q
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  have hY₂X : Y₂ ≤ X := map_subtype_le _
  have hQX : Q ≤ X := sup_le hY₂X hTX
  let S := T.subtype hTX
  obtain ⟨_,⟨e⟩,hUcard,hJ⟩ := original_pair_solvable_case_three_at h₀ h structural D m
    hTA hTB eA eB hne hindexL hindexA hindexB hcentral hs hcomm
  have hred := (original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB).1
  let : (U.subgroupOf X).Normal := hred.normal
  let : IsElementaryAbelian 2 (U.subgroupOf X) := hred.elementary
  have hUX : U ≤ X := conjugateSpanBy_le (fun z hz =>
    hTX ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  have hucore : U.subgroupOf X ≤ pCore 2 X :=
    le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 _⟩
  have hUcard' : Nat.card (U.subgroupOf X) = 64 := by
    rw [natCard_subgroupOf_eq U X hUX]
    exact hUcard
  have hsize := MarkedCubicRecognition.sylow_card_eq_four_mul_twoCore S e
  have hScard : Nat.card S = Nat.card T :=
    Nat.card_congr (subgroupOfEquivOfLe hTX).toEquiv
  have hlarge : 256 ≤ Nat.card T := by
    have hh := card_le_of_le hucore
    rw [hUcard'] at hh
    rw [hScard] at hsize
    omega
  obtain ⟨_,hn,_,_,_,_,hout⟩ := original_pair_central_three_residual_at h₀ h structural D m
    hTA hTB eA eB hne hindexL hindexA hindexB hcentral hs hcomm
  obtain ⟨hmove,⟨er⟩⟩ := MarkedCubicRecognition.centralThreeResidual_parabolic S e
  have hPmap : (R ⊔ (S : Subgroup X)).map X.subtype = Q := by
    rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTX]
  let j : (R ⊔ (S : Subgroup X) : Subgroup X) ≃* Q :=
    ((R ⊔ (S : Subgroup X)).equivMapOfInjective X.subtype X.subtype_injective).trans
      (MulEquiv.subgroupCongr hPmap)
  let eq : (Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.congr _ _ j.symm (pCore_map_iso 2 j.symm)).trans er
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
  have hzV : z ∈ V := (hseed.le hz).1
  obtain ⟨⟨ep⟩,hcent⟩ := ordinary_firstFlag_parabolic_at h structural D m eL ⟨z,hzV⟩ hz hzL
  have hPZ : P ≤ centralizer (Z : Set G) := by
    simpa only [←hseed] using hcent
  have hPM : P ≤ normalizer (L : Set G) :=
    inf_le_left.trans (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hnePQ : P ≠ Q := by
    intro he
    exact hout (le_sup_left.trans (he ▸ hPM))
  have hTP : (T : Subgroup G) ≤ P := sylow_le_firstFlagNormalizer
  have hTQ : (T : Subgroup G) ≤ Q := le_sup_right
  have hint := intersection_eq_sylow hTP hTQ ep eq hnePQ
  have hg := pair_goldschmidt hTP hTQ ep eq hnePQ
  have hTY : (T : Subgroup G) ≤ Y := hTP.trans le_sup_left
  have hcore : pCore 2 Y ≠ ⊥ := by
    intro hh
    have hb := hg.intersection_card_le_128 hh
    change Nat.card ((P ⊓ Q).subgroupOf Y) ≤ 128 at hb
    rw [hint,Nat.card_congr (subgroupOfEquivOfLe hTY).toEquiv] at hb
    omega
  have hlocal : Y ∈ Chapter1.HOver G (T : Set G) := by
    refine ⟨?_,hTY⟩
    change (pCore 2 Y).map Y.subtype ≠ ⊥
    exact fun hh => hcore ((map_eq_bot_iff_of_injective _ Y.subtype_injective).mp hh)
  have houtY : ¬ Y ≤ normalizer (L : Set G) :=
    fun hh => hout (le_sup_left.trans (le_sup_right.trans hh))
  let : IsElementaryAbelian 2 Z := omegaOneCenterAmbient_elementaryAbelian _
  have hredY : IsPReduced 2 ((conjugateSpanBy Z Y).subgroupOf Y) :=
    reduced_conjugateSpan_of_sylow_central T Y Z hTY
      (fun z hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
      (fun z hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2)
      (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (h₀.qtke.evenCharacteristic T) hlocal))
  have hmoveG := congrArg (Subgroup.map X.subtype) hmove
  rw [map_commutator,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTX] at hmoveG
  have hp : IsPPerfect 2 Y₂ :=
    (isPPerfect_embedded_pResidual 2 (MarkedCubicRecognition.centralThreePreimage X)).of_surjective
      (X.subtype.subgroupMap R) (X.subtype.subgroupMap_surjective R)
  exact ⟨hlarge,⟨ep⟩,⟨eq⟩,hPZ,hnePQ,hint,hg,⟨hlocal,houtY⟩,hredY,hmoveG,
    embedded_pResidual_join_pGroup Y₂ T hp T.isPGroup' (hTX.trans hn),hQX.trans hJ⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
