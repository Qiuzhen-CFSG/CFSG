module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondAmalgam
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.SecondFlag
public import Theory.GroupTheory.TwoPerfectCyclicQuotient
public import Theory.GroupTheory.UniqueLocalResidualKernel

/-!
# Noncommutation of the actual second-amalgam residuals

The first flag parabolic centralizes the central seed, while the original
plane parabolic moves it. Their S₃ quotients give equal orders, so they
are distinct; maximality of the marked plane parabolic makes them generate
LT. No normalizer supplement or additional generation premise is assumed.

If the escaping central residual Y₂ normalized the literal L₁=O²(L₁T),
it would act trivially on L₁/O₂(L₁), which has order three. Residual
recovery then makes L₁ normalize Y₂. The original plane parabolic already
normalizes Y₂, so LT normalizes it. Maximal two-local uniqueness and
characteristic two of the original join force Y₂=1, contradicting escape.
This proves [L₁,Y₂] is not contained in O₂(L₁) for these actual subgroups.

The second-amalgam full action kernel and F.6 quotient selection remain
separate obligations. This theorem does not assert the plane exclusion
or the ambient 13.4.1 recognition.
Source: Aschbacher--Smith 13.4.7(3), printed p.903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- The actual first and plane parabolics generate LT, and Y₂ neither
normalizes L₁ nor commutes with it modulo its literal two-core. -/
theorem original_plane_second_noncommuting
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
    let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
    let P := firstFlagNormalizer T L V
    let L₁ := (pResidual 2 P).map P.subtype
    P ⊔ B = L ⊔ (T : Subgroup G) ∧
      ¬ Y₂ ≤ normalizer (L₁ : Set G) ∧ ¬ ⁅L₁,Y₂⁆ ≤ L₁.pCoreIn 2 := by
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let R := MarkedCubicRecognition.centralThreeResidual X
  let Y₂ := R.map X.subtype
  let P := firstFlagNormalizer T L V
  let L₁ := (pResidual 2 P).map P.subtype
  let M₀ := L ⊔ (T : Subgroup G)
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  have hTP : (T : Subgroup G) ≤ P := sylow_le_firstFlagNormalizer
  have hPM : P ≤ M₀ := inf_le_left
  have hBM : B ≤ M₀ := by rw [hBplane]; exact inf_le_left
  obtain ⟨_,⟨ep⟩,_,hPZ,_⟩ := original_plane_second_amalgam h₀ h structural D m
    hTA hTB eA eB hne hindexL hindexA hindexB hcentral hs hcomm
    Wplane hWplane hTplane hBplane
  have hnePB : P ≠ B := by
    intro he
    have hBZ : B ≤ centralizer (Z : Set G) := he ▸ hPZ
    have hZB : Z ≤ centralizer (B : Set G) := le_centralizer_iff.mp hBZ
    rw [inf_eq_left.mpr hZB,relIndex_self] at hindexB
    omega
  have hnotPB : ¬ P ≤ B := by
    intro hh
    apply hnePB
    apply eq_of_le_of_card_ge hh
    have hcP := ((T : Subgroup G).subgroupOf P).index_mul_card
    have hcB := ((T : Subgroup G).subgroupOf B).index_mul_card
    rw [show ((T : Subgroup G).subgroupOf P).index = 3 from
      SymmetricThreeTwoCore.sylow_index_three ep (T.subtype hTP),
      Nat.card_congr (subgroupOfEquivOfLe hTP).toEquiv] at hcP
    rw [show ((T : Subgroup G).subgroupOf B).index = 3 from
      SymmetricThreeTwoCore.sylow_index_three eB (T.subtype hTB),
      Nat.card_congr (subgroupOfEquivOfLe hTB).toEquiv] at hcB
    omega
  have hmax : IsCoatom (B.subgroupOf M₀) := by
    rw [hBplane]
    exact original_second_flag_coatom D m Wplane hWplane hTplane
  have hgen : P ⊔ B = M₀ := by
    have hi : B.subgroupOf M₀ < (P ⊔ B).subgroupOf M₀ := by
      apply lt_of_le_of_ne (subgroupOf_mono M₀ le_sup_right)
      intro he
      apply hnotPB
      intro p hp
      have hh : (⟨p,hPM hp⟩ : M₀) ∈ (P ⊔ B).subgroupOf M₀ := mem_sup_left hp
      rw [←he] at hh
      exact hh
    have hh := congrArg (Subgroup.map M₀.subtype) (hmax.lt_iff.mp hi)
    rwa [map_subgroupOf_eq_of_le (sup_le hPM hBM),←MonoidHom.range_eq_map,range_subtype] at hh
  obtain ⟨hRX,hnR,_,_,_,_,hout⟩ := original_pair_central_three_residual h₀ h structural D m
    hTA hTB eA eB hne hindexL hindexA hindexB hcentral hs hcomm
  have hpR : IsPPerfect 2 Y₂ :=
    (isPPerfect_embedded_pResidual 2 (MarkedCubicRecognition.centralThreePreimage X)).of_surjective
      (X.subtype.subgroupMap R) (X.subtype.subgroupMap_surjective R)
  have hresR : (pResidual 2 Y₂).map Y₂.subtype = Y₂ := by
    rw [(pResidual_eq_top_iff 2 Y₂).mpr hpR,←MonoidHom.range_eq_map,range_subtype]
  have hPL₁ : P ≤ normalizer (L₁ : Set G) := by
    have hh := (pResidual 2 P).le_normalizer_map P.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hTL₁ : (T : Subgroup G) ≤ normalizer (L₁ : Set G) := hTP.trans hPL₁
  have hcoreT : L₁.pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 L₁).le_sylow_of_normalized T
      (hTL₁.trans (normalizer_le_normalizer_characteristic_image L₁ (pCore 2 L₁)))
  obtain ⟨eL⟩ := original_plane_ordinary D m Wplane hWplane hTplane hBplane eB
  have hseed := (original_pair_source_seed h structural D m hTA hTB eA eB hne
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
  have hL₁ : L₁ = firstCentralizerResidual L z :=
    firstFlagNormalizer_residual h structural D m eL v hz hzL
  have hcard : Nat.card (L₁ ⧸ pCore 2 L₁) = 3 := by
    rw [hL₁]
    exact firstCentralizerResidual_core_quotient_card D m
      (by rw [centralCore_eq_twoCore_of_ordinary eL]; exact pCore_isPGroup) v hzL
  have hnot : ¬ Y₂ ≤ normalizer (L₁ : Set G) := by
    intro hn
    have hc := commutator_le_pCoreIn_of_twoPerfect_of_normalizes_of_quotient_card_three
      L₁ Y₂ hpR hn hcard
    have hL₁R : L₁ ≤ normalizer (Y₂ : Set G) := by
      have hh := normalizes_residual_of_commutator_le_two L₁ (T : Subgroup G) Y₂
        (L₁.pCoreIn 2) (hTX.trans hnR) hcoreT (isPGroup_pCoreIn 2 L₁)
        (L₁.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L₁ (pCore 2 L₁)))
        (by rw [hresR,commutator_comm]; exact hc)
      rwa [hresR] at hh
    have hcover : P ≤ L₁ ⊔ (T : Subgroup G) :=
      le_embedded_pResidual_sup_sylow_of_normalizes T P (hTP.trans P.le_normalizer)
    have hMR : M₀ ≤ normalizer (Y₂ : Set G) := by
      rw [←hgen]
      exact sup_le (hcover.trans (sup_le hL₁R (hTX.trans hnR))) (le_sup_right.trans hnR)
    have hlocal := original_pair_local D m hTA hTB eA eB hne hindexA hindexB
    have hself := Chapter1.lemma_1_1_4_6 T (h₀.qtke.evenCharacteristic T) hlocal
    have he := normal_eq_bot_of_unique_core M₀ X (normalizer (L : Set G)) Y₂
      (h.source_normalizer_maximal_unique structural
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2
      (fun hh => hout (hRX.trans hh)) hself hRX hnR hMR
    apply hout
    change Y₂ ≤ normalizer (L : Set G)
    rw [he]
    exact bot_le
  refine ⟨hgen,hnot,?_⟩
  intro hc
  apply hnot
  apply le_normalizer_iff_commutator_le_right.mpr
  rw [commutator_comm]
  exact hc.trans (pCoreIn_le 2 L₁)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
