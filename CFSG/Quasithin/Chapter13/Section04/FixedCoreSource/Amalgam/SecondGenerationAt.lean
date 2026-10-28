module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondGeneration
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondComponentAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.MidSizeFiveExclusion
public import Theory.GroupTheory.PGroup.OmegaCentralizerDetection

/-!
This guarded version uses earlier structure only at the original G,T.
All literal residuals, quotient maps and original source hypotheses are retained.

# Generation and movement in the actual second amalgam

The normal component constructed in SecondComponent is the whole
O²(Y), and Y=K_Y T. Both original vertex residuals, including L₁,
lie in this same component. The ordinary Thompson action gives
K_Y=[K_Y,J(T)], and the actual A₅ quotient is excluded.

The original cubic orbit contains the seed, so its containment in K_Y
makes the whole omega span U=[U,K_Y]. It has at least sixteen elements.
Fixed-point-freeness on the original seed, followed by omega-center
detection, gives C_U(K_Y)=1. All assertions retain the same second join,
component, original two vertices, omega span and action kernel.

The preceding source assumptions remain explicit. These are inputs to
the remaining B.5/module selection and chief-factor contradiction; this
theorem does not yet exclude the first solvable join or prove 13.4.1.
Source: Aschbacher--Smith 13.4.7(3), printed pp.903--904,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

open Section03.Noncentrality.SupercriticalSource

/-- Construct the component supplement, both residual containments, ordinary
Thompson movement and the fully moved fixed-free omega module of the
original second join, without a supplied component or model marking. -/
theorem exists_original_plane_second_generation_at
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
    (h1332 : Source1332OneTwo T) :
    let X := A ⊔ B
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
    let P := firstFlagNormalizer T L V
    let Y := P ⊔ (Y₂ ⊔ (T : Subgroup G))
    let U := conjugateSpanBy Z Y
    ∃ K : Subgroup Y, K.IsCComponent ∧ K.Normal ∧
      K.map Y.subtype ∈ MainForward.faithfulLocalComponents T ∧
      K.map Y.subtype ∈ Chapter1.LStar G T ∧
      (T : Subgroup G) ≤ normalizer (K.map Y.subtype : Set G) ∧
      ⁅U,K.map Y.subtype⁆ ≠ ⊥ ∧
      (ClassicalGroup.IsPSL ((K.map Y.subtype) ⧸ pCore 2 (K.map Y.subtype)) 3 2 ∨
        Chapter1.Section02.LocalModels.IsAlternating
          ((K.map Y.subtype) ⧸ pCore 2 (K.map Y.subtype)) 6 ∨
        Chapter1.Section02.LocalModels.IsAlternatingCover
          ((K.map Y.subtype) ⧸ pCore 2 (K.map Y.subtype)) 6 ∨
        ClassicalGroup.IsPSU ((K.map Y.subtype) ⧸ pCore 2 (K.map Y.subtype)) 3 3) ∧
      K ⊓ centralizer (U.subgroupOf Y : Set Y) = K.pCoreIn 2 ∧
      pResidual 2 Y = K ∧ Y = K.map Y.subtype ⊔ (T : Subgroup G) ∧
      (pResidual 2 P).map P.subtype ≤ K.map Y.subtype ∧
      Y₂ ≤ K.map Y.subtype ∧
      ⁅K.map Y.subtype,elementaryAbelianMaxJ (T : Subgroup G)⁆ = K.map Y.subtype ∧
      ⁅U,K.map Y.subtype⁆ = U ∧ 16 ≤ Nat.card U ∧
      U ⊓ centralizer (K.map Y.subtype : Set G) = ⊥ := by
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
  let P := firstFlagNormalizer T L V
  let Q := Y₂ ⊔ (T : Subgroup G)
  let Y := P ⊔ Q
  have hTY : (T : Subgroup G) ≤ Y := le_sup_right.trans le_sup_right
  obtain ⟨K,hK,hn,hf,hstar,hTK,hm,hmK,hker⟩ :=
    exists_original_plane_second_component_at h₀ h structural D m hTA hTB eA eB hne
      hindexL hindexA hindexB hcentral hs hcomm Wplane hWplane hTplane hBplane hM h1332
  let : K.Normal := hn
  let j := K.equivMapOfInjective Y.subtype Y.subtype_injective
  let jq := QuotientGroup.congr (pCore 2 K) (pCore 2 (K.map Y.subtype)) j (pCore_map_iso 2 j)
  have hmKi : MidSizeModel (K ⧸ pCore 2 K) :=
    SecondGeneration.midSize_of_mulEquiv hmK jq.symm
  obtain ⟨_,_,_,_,_,_,hg,hlocal,hred,_,hY₂,_⟩ := original_plane_second_amalgam_at
    h₀ h structural D m hTA hTB eA eB hne hindexL hindexA hindexB hcentral
      hs hcomm Wplane hWplane hTplane hBplane
  have hr := (SecondGeneration.component_is_residual
    (Chapter3.sqtk_of_mem_H h₀.qtke hlocal.1.1) hg K hK hmKi).2.2
  have hgen : Y = K.map Y.subtype ⊔ (T : Subgroup G) := by
    have hh := pResidual_sup_sylow_eq_top (T.subtype hTY)
    rw [hr] at hh
    have hh' := congrArg (Subgroup.map Y.subtype) hh
    rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTY,
      ←MonoidHom.range_eq_map,range_subtype] at hh'
    exact hh'.symm
  have hlocalres (R : Subgroup G) (hRY : R ≤ Y) :
      (pResidual 2 R).map R.subtype ≤ K.map Y.subtype := by
    have hh := map_mono (f := Y.subtype)
      (map_pResidual_le 2 (inclusion hRY))
    rw [map_map,hr] at hh
    exact hh
  have hth := (original_plane_second_thompson_at h₀ h structural D m hTA hTB eA eB hne
    hindexL hindexA hindexB hcentral hs hcomm Wplane hWplane hTplane hBplane).2.2.1
  let S := T.subtype hTY
  let Ji := elementaryAbelianMaxJ (S : Subgroup Y)
  have hjmap : Ji.map Y.subtype = elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective Y.subtype Y.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTY]
  have hpmap : ((pResidual 2 (P.subgroupOf Y)).map (P.subgroupOf Y).subtype).map
      Y.subtype = (pResidual 2 P).map P.subtype := by
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le le_sup_left]
  have hi : ⁅(pResidual 2 (P.subgroupOf Y)).map (P.subgroupOf Y).subtype,Ji⁆ =
      (pResidual 2 (P.subgroupOf Y)).map (P.subgroupOf Y).subtype := by
    apply map_injective Y.subtype_injective
    rw [map_commutator,hpmap,hjmap]
    exact hth
  have hmove := congrArg (Subgroup.map Y.subtype)
    (SecondGeneration.component_commutator hg K hK hmKi hr Ji hi)
  rw [map_commutator,hjmap] at hmove
  let U := conjugateSpanBy Z Y
  have hCY : Y ≤ normalizer (K.map Y.subtype : Set G) := by
    have hh := K.le_normalizer_map Y.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hY₂K : Y₂ ≤ K.map Y.subtype := hY₂.symm.le.trans (hlocalres Q le_sup_right)
  obtain ⟨_,_,_,hfixed,hseedOrbit,hseedCard,_⟩ := original_pair_central_three_residual_at
    h₀ h structural D m hTA hTB eA eB hne hindexL hindexA hindexB hcentral hs hcomm
  have hnorm : Y ≤ normalizer ((⁅U,K.map Y.subtype⁆ : Subgroup G) : Set G) := by
    intro y hy
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy Z Y hy),
      mem_normalizer_iff_map_conj_eq.mp (hCY hy)]
  have hseed : Z ≤ ⁅U,K.map Y.subtype⁆ :=
    ((le_conjugateSpanBy Z Y₂).trans_eq hseedOrbit).trans
      (commutator_mono (le_conjugateSpanBy Z Y) hY₂K)
  have hfull : ⁅U,K.map Y.subtype⁆ = U :=
    le_antisymm (le_normalizer_iff_commutator_le_left.mp
      ((map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z Y)))
      (conjugateSpanBy_le hseed hnorm)
  have hdim : 16 ≤ Nat.card U := by
    rw [←hseedCard,←hseedOrbit]
    exact card_le_of_le (conjugateSpanBy_mono le_rfl
      (show Y₂ ≤ Y from le_sup_left.trans le_sup_right))
  have hUY : U ≤ Y := conjugateSpanBy_le
    (fun z hz => hTY ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) Y.le_normalizer
  let : IsElementaryAbelian 2 (U.subgroupOf Y) := hred.elementary
  have heU : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hUY).symm.toMonoidHom (subgroupOfEquivOfLe hUY).symm.injective
  have hUT : U ≤ (T : Subgroup G) := by
    intro u hu
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype hTY)
      (hred.le_pCore (show (⟨u,hUY hu⟩ : Y) ∈ U.subgroupOf Y from hu))
  have hZfixed : Z ⊓ centralizer (K.map Y.subtype : Set G) = ⊥ := by
    apply le_bot_iff.mp
    exact (inf_le_inf (le_conjugateSpanBy Z X) (centralizer_le hY₂K)).trans hfixed.le
  have hfixedU : U ⊓ centralizer (K.map Y.subtype : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_omega_disjoint T (K.map Y.subtype) U heU hUT
      (hTY.trans (le_normalizer_conjugateSpanBy Z Y)) hTK hZfixed
  have hnotfive := SecondGeneration.component_not_alternatingFive hg K hK hr
  have hmodels := hmK.resolve_left (fun he => hnotfive ⟨jq.trans he.some⟩)
  exact ⟨K,hK,hn,hf,hstar,hTK,hm,hmodels,hker,hr,hgen,
    hlocalres P le_sup_left,hY₂K,hmove,hfull,hdim,hfixedU⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
