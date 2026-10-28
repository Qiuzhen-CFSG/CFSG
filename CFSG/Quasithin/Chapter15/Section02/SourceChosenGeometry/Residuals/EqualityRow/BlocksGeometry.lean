module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.SimpleComponentEscape
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.BinaryG2Exclusion
public import Theory.GroupTheory.SylowNormalizerOvergroup

/-!
# Parabolic and Thompson geometry for the original equality-row blocks

The actual Sylow subgroup of each escaping I contains O₂(I). The original
wreath residual K and the index-two plane centralizer S generate an
H-normalized parabolic KS. Its nontrivial two-core QI has its Thompson
normalizer inside Mc by the unique maximal two-local overgroup of H.
This supplies the geometric input to the literal A₅ and A₇ block actions,
without the partner residual identity or a plane-uniqueness packet.

Source: Aschbacher--Smith, 15.2.18 and preliminary 15.2.23, printed
pp.1113--1115, refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.ResidualInput
open Section01 Section03 ChapterA.Section04 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (r : ResidualInput hsource H B)
include r

/-- The original Sylow notation is identified with the constructed centralizer. -/
theorem sylow_in_escape_for_blocks (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆ :=
  r.sylow_in_escape hI

/-- The literal source join K S lies in the original escaping intersection. -/
theorem residual_sup_planeSylow_le_for_blocks (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    (pResidual 2 H).map H.subtype ⊔ planeSylow T ⁅V,B⁆ ≤ Mc ⊓ I :=
  r.residual_sup_planeCentralizer_le hI

/-- The omega center in the original Sylow notation is the same plane. -/
theorem plane_omega_for_blocks : ⁅V,B⁆ = omegaOneCenterAmbient (planeSylow T ⁅V,B⁆) :=
  r.plane_eq_omegaCenter

private theorem core_le_plane_for_blocks
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) : I.pCoreIn 2 ≤ planeSylow T ⁅V,B⁆ := by
  obtain ⟨P,hP⟩ := r.sylow_in_escape_for_blocks hI
  have hm := map_mono (f := I.subtype) (pCore_isPGroup.le_sylow_of_normal P)
  rwa [hP] at hm

private theorem plane_le_centralizer_for_blocks :
    ⁅V,B⁆ ≤ centralizer ((⁅V,B⁆ : Subgroup G) : Set G) := by
  let := hsource.prepared.elementary
  have hVV : V ≤ centralizer (V : Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
  exact r.plane_le.trans (hVV.trans (centralizer_le r.plane_le))

/-- H-normality of a nontrivial two-subgroup controls its full normalizer,
using only the source's two maximal Sylow overgroups. -/
theorem normalizer_le_partner_of_seed_normal
    {R : Subgroup G} (hp : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hn : H ≤ normalizer (R : Set G)) : normalizer (R : Set G) ≤ Mc := by
  obtain ⟨N,hRN,hN⟩ := Finite.exists_le_maximal
    (show IsTwoLocal (normalizer (R : Set G)) from ⟨R,hne,hp,rfl⟩)
  have hNT : N ∈ maximalTwoLocalOvergroups (T : Subgroup G) :=
    ⟨hN,r.outside.1.1.2.trans (hn.trans hRN)⟩
  rw [r.two_overgroups,Set.mem_insert_iff,Set.mem_singleton_iff] at hNT
  rcases hNT with rfl | rfl
  · exact (r.outside.1.2 (hn.trans hRN)).elim
  · exact hRN

/-- KS is H-invariant, using the actual index-two S and H = KT. -/
theorem residual_plane_join_normalized (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) :
    H ≤ normalizer (((pResidual 2 H).map H.subtype ⊔ planeSylow T (⁅V,B⁆ : Subgroup G) : Subgroup G) : Set G) := by
  have hTS : (T : Subgroup G) ≤ normalizer (planeSylow T (⁅V,B⁆ : Subgroup G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mp
      (normal_of_index_eq_two (r.escape_index hI).2)
  have hTK : (T : Subgroup G) ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) :=
    r.geometry.outside.1.1.2.trans
      (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pResidual 2 H)))
  exact r.residual_join.ge.trans
    (sup_le (le_sup_left.trans le_normalizer)
      ((le_inf hTK hTS).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)))

/-- Nontriviality of QI comes from the original nontrivial two-core of I. -/
theorem planeParabolicCore_ne_bot (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) :
    planeParabolicCore T H (⁅V,B⁆ : Subgroup G) ≠ ⊥ := by
  have hQ : I.pCoreIn 2 ≤ (pResidual 2 H).map H.subtype ⊔ planeSylow T (⁅V,B⁆ : Subgroup G) :=
    (core_le_plane_for_blocks r hI).trans le_sup_right
  have hle : I.pCoreIn 2 ≤ planeParabolicCore T H (⁅V,B⁆ : Subgroup G) := by
    simpa only [inf_eq_right.mpr hQ] using
      inf_pCoreIn_le_of_le 2 ((r.residual_sup_planeSylow_le_for_blocks hI).trans inf_le_right)
  intro he
  exact hI.1 (bot_unique (hle.trans_eq he))

/-- QI is normal in H, with normality expressed in the original ambient group. -/
theorem planeParabolicCore_normalized (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) :
    H ≤ normalizer (planeParabolicCore T H (⁅V,B⁆ : Subgroup G) : Set G) :=
  (r.residual_plane_join_normalized hI).trans (normalizer_le_normalizer_intrinsicCore _)

/-- The same QI lies in the original S, with both Sylow embeddings unchanged. -/
theorem planeParabolicCore_le_plane (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) :
    planeParabolicCore T H (⁅V,B⁆ : Subgroup G) ≤ planeSylow T (⁅V,B⁆ : Subgroup G) := by
  have hTH : (T : Subgroup G) ≤ H := r.geometry.outside.1.1.2
  have hQH : planeParabolicCore T H (⁅V,B⁆ : Subgroup G) ≤ H.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes
      (sup_le (map_subtype_le _) (inf_le_left.trans hTH))
      (r.residual_plane_join_normalized hI)
  have hHT := pCoreIn_le_sylow H (T.subtype hTH)
  rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] at hHT
  exact le_inf (hQH.trans hHT)
    ((pCoreIn_le 2 _).trans (sup_le r.residual_centralizes_plane inf_le_right))

/-- The source uniqueness theorem controls the full Thompson normalizer. -/
theorem planeParabolicCore_thompson_normalizer_le (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) :
    normalizer (elementaryAbelianMaxJ (planeParabolicCore T H (⁅V,B⁆ : Subgroup G)) : Set G) ≤ Mc := by
  let Q := planeParabolicCore T H (⁅V,B⁆ : Subgroup G)
  have hJQ : elementaryAbelianMaxJ Q ≤ Q := sSup_le fun _ hA => hA.1
  exact r.normalizer_le_partner_of_seed_normal
    ((isPGroup_pCoreIn 2 _).to_le hJQ)
    (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup Q (isPGroup_pCoreIn 2 _)
      (r.planeParabolicCore_ne_bot hI))
    ((r.planeParabolicCore_normalized hI).trans
      (normalizer_le_normalizer_elementaryAbelianMaxJ Q))

/-- The Thompson subgroup cannot lie in the two-core of an escaping extension.
The core bound is the precise output of the M₀QI calculation in each model. -/
theorem planeParabolicCore_thompson_not_le_core
    (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) {X0 : Subgroup G} (hout : ¬ X0 ≤ Mc)
    (hcore : (X0 ⊔ planeParabolicCore T H (⁅V,B⁆ : Subgroup G)).pCoreIn 2 ≤ planeParabolicCore T H (⁅V,B⁆ : Subgroup G)) :
    ¬ elementaryAbelianMaxJ (planeParabolicCore T H (⁅V,B⁆ : Subgroup G)) ≤
      (X0 ⊔ planeParabolicCore T H (⁅V,B⁆ : Subgroup G)).pCoreIn 2 := by
  intro hj
  have he := elementaryAbelianMaxJ_eq_of_intermediate_finite
    (planeParabolicCore T H (⁅V,B⁆ : Subgroup G)) _ hj hcore
  have hn : X0 ≤ normalizer
      (elementaryAbelianMaxJ (planeParabolicCore T H (⁅V,B⁆ : Subgroup G)) : Set G) := by
    rw [← he]
    exact le_sup_left.trans ((X0 ⊔ planeParabolicCore T H (⁅V,B⁆ : Subgroup G)).le_normalizer.trans
      ((normalizer_le_normalizer_intrinsicCore _).trans
        (normalizer_le_normalizer_elementaryAbelianMaxJ _)))
  exact hout (hn.trans (r.planeParabolicCore_thompson_normalizer_le hI))

/-- In characteristic two the original plane lies in Ω₁Z(O₂(I)). -/
theorem plane_le_escape_core_omega
    (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) (hfit : generalizedFitting I = pCore 2 I) :
    (⁅V,B⁆ : Subgroup G) ≤ omegaOneCenterAmbient (I.pCoreIn 2) := by
  have hSI : planeSylow T (⁅V,B⁆ : Subgroup G) ≤ I :=
    (le_sup_right.trans (r.residual_sup_planeSylow_le_for_blocks hI)).trans inf_le_right
  intro z hz
  have hzS := (mem_omegaOneCenterAmbient_iff _ z).mp (r.plane_omega_for_blocks ▸ hz)
  have hc : ∀ q ∈ I.pCoreIn 2, q * z = z * q :=
    fun q hq => hzS.2.2 q (core_le_plane_for_blocks r hI hq)
  have hzQ : z ∈ I.pCoreIn 2 := by
    have hzC : (⟨z,hSI hzS.1⟩ : I) ∈ centralizer (pCore 2 I : Set I) := by
      intro q hq
      apply Subtype.ext
      exact hc q (mem_map_of_mem I.subtype hq)
    have hself : centralizer (pCore 2 I : Set I) ≤ pCore 2 I := by
      rw [← hfit]
      exact centralizer_generalizedFitting_le I
    exact mem_map_of_mem I.subtype (hself hzC)
  exact (mem_omegaOneCenterAmbient_iff _ z).mpr ⟨hzQ,hzS.2.1,hc⟩

/-- The literal U₀ is elementary: all its conjugates lie in Ω₁Z(O₂(I)). -/
theorem plane_span_elementary
    (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) (hfit : generalizedFitting I = pCore 2 I)
    {X0 : Subgroup G} (hXI : X0 ≤ I) :
    IsElementaryAbelian 2 (conjugateSpanBy (⁅V,B⁆ : Subgroup G) X0) := by
  have hU : conjugateSpanBy (⁅V,B⁆ : Subgroup G) X0 ≤ omegaOneCenterAmbient (I.pCoreIn 2) :=
    conjugateSpanBy_le (r.plane_le_escape_core_omega hI hfit)
      (hXI.trans (I.le_normalizer.trans ((normalizer_le_normalizer_intrinsicCore I).trans
        (normalizer_le_normalizer_omegaCenter _))))
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (I.pCoreIn 2)) :=
    omegaOneCenterAmbient_elementaryAbelian _
  exact IsElementaryAbelian.of_injective (inclusion hU) (inclusion_injective hU)

/-- The source plane is already in QI in the characteristic-two branch. -/
theorem plane_le_planeParabolicCore
    (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) (hfit : generalizedFitting I = pCore 2 I) :
    (⁅V,B⁆ : Subgroup G) ≤ planeParabolicCore T H (⁅V,B⁆ : Subgroup G) := by
  have hQ : I.pCoreIn 2 ≤ (pResidual 2 H).map H.subtype ⊔ planeSylow T (⁅V,B⁆ : Subgroup G) :=
    (core_le_plane_for_blocks r hI).trans le_sup_right
  have hle : I.pCoreIn 2 ≤ planeParabolicCore T H (⁅V,B⁆ : Subgroup G) := by
    simpa only [inf_eq_right.mpr hQ] using
      inf_pCoreIn_le_of_le 2 ((r.residual_sup_planeSylow_le_for_blocks hI).trans inf_le_right)
  have hOmega : omegaOneCenterAmbient (I.pCoreIn 2) ≤ I.pCoreIn 2 :=
    fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  exact (r.plane_le_escape_core_omega hI hfit).trans (hOmega.trans hle)

/-- The complete orbit span U₀, not just its seed plane, lies in QI. -/
theorem plane_span_le_planeParabolicCore
    (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) (hfit : generalizedFitting I = pCore 2 I)
    {X0 : Subgroup G} (hXI : X0 ≤ I) :
    conjugateSpanBy (⁅V,B⁆ : Subgroup G) X0 ≤ planeParabolicCore T H (⁅V,B⁆ : Subgroup G) := by
  have hOmega : omegaOneCenterAmbient (I.pCoreIn 2) ≤ I.pCoreIn 2 :=
    fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hU : conjugateSpanBy (⁅V,B⁆ : Subgroup G) X0 ≤ I.pCoreIn 2 :=
    conjugateSpanBy_le ((r.plane_le_escape_core_omega hI hfit).trans hOmega)
      (hXI.trans (I.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore I)))
  have hQ : I.pCoreIn 2 ≤ (pResidual 2 H).map H.subtype ⊔ planeSylow T (⁅V,B⁆ : Subgroup G) :=
    (core_le_plane_for_blocks r hI).trans le_sup_right
  apply hU.trans
  simpa only [inf_eq_right.mpr hQ] using
    inf_pCoreIn_le_of_le 2 ((r.residual_sup_planeSylow_le_for_blocks hI).trans inf_le_right)

/-- The whole span U₀ is normalized by X₀QI, using relative normality of X₀. -/
theorem plane_span_normalized (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I)
    {X0 : Subgroup G} (hn : I ≤ normalizer (X0 : Set G)) :
    X0 ⊔ planeParabolicCore T H (⁅V,B⁆ : Subgroup G) ≤ normalizer (conjugateSpanBy (⁅V,B⁆ : Subgroup G) X0 : Set G) := by
  have hQI : planeParabolicCore T H (⁅V,B⁆ : Subgroup G) ≤ I :=
    (pCoreIn_le 2 _).trans ((r.residual_sup_planeSylow_le_for_blocks hI).trans inf_le_right)
  have hQZ : planeParabolicCore T H (⁅V,B⁆ : Subgroup G) ≤ centralizer ((⁅V,B⁆ : Subgroup G) : Set G) :=
    (pCoreIn_le 2 _).trans (sup_le r.residual_centralizes_plane inf_le_right)
  exact sup_le (le_normalizer_conjugateSpanBy (⁅V,B⁆ : Subgroup G) X0)
    (normalizes_conjugateSpanBy (⁅V,B⁆ : Subgroup G) X0 _
      (hQZ.trans (Subgroup.centralizer_le_normalizer _)) (hQI.trans hn))

theorem plane_span_extension_core_le_sylow
    (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) {X0 : Subgroup G}
    (hXI : X0 ≤ I) (hn : I ≤ normalizer (X0 : Set G)) :
    (X0 ⊔ planeParabolicCore T H (⁅V,B⁆ : Subgroup G)).pCoreIn 2 ≤ planeSylow T (⁅V,B⁆ : Subgroup G) := by
  let Q := planeParabolicCore T H (⁅V,B⁆ : Subgroup G)
  let E := X0 ⊔ Q
  let R := E.pCoreIn 2
  have hPI : (pResidual 2 H).map H.subtype ⊔ planeSylow T (⁅V,B⁆ : Subgroup G) ≤ I :=
    (r.residual_sup_planeSylow_le_for_blocks hI).trans inf_le_right
  have hQI : Q ≤ I := (pCoreIn_le 2 _).trans hPI
  have hEI : E ≤ I := sup_le hXI hQI
  have hSI : planeSylow T (⁅V,B⁆ : Subgroup G) ≤ I := le_sup_right.trans hPI
  have hSQ : planeSylow T (⁅V,B⁆ : Subgroup G) ≤ normalizer (Q : Set G) :=
    le_sup_right.trans (((pResidual 2 H).map H.subtype ⊔ planeSylow T (⁅V,B⁆ : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_intrinsicCore _))
  have hSE : planeSylow T (⁅V,B⁆ : Subgroup G) ≤ normalizer (E : Set G) :=
    (le_inf (hSI.trans hn) hSQ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hSR : planeSylow T (⁅V,B⁆ : Subgroup G) ≤ normalizer (R : Set G) :=
    hSE.trans (normalizer_le_normalizer_intrinsicCore E)
  have hRI : R ≤ I := (pCoreIn_le 2 E).trans hEI
  obtain ⟨P,hP⟩ := r.sylow_in_escape_for_blocks hI
  have hPR : (P : Subgroup I) ≤ normalizer (R.subgroupOf I : Set I) := by
    rw [← subgroupOf_normalizer_eq hRI]
    intro x hx
    exact hSR (hP ▸ mem_map_of_mem I.subtype hx)
  have hRS := ((isPGroup_pCoreIn 2 E).comap_subtype (K := I)).le_sylow_of_normalized P hPR
  intro x hx
  rw [← hP]
  exact mem_map_of_mem I.subtype (hRS (show (⟨x,hRI hx⟩ : I) ∈ R.subgroupOf I from hx))

/-- The original two-core is contained in QI = O₂(KS). -/
theorem escape_core_le_planeParabolicCore
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) : I.pCoreIn 2 ≤ planeParabolicCore T H ⁅V,B⁆ := by
  have hQ : I.pCoreIn 2 ≤ (pResidual 2 H).map H.subtype ⊔ planeSylow T ⁅V,B⁆ :=
    (core_le_plane_for_blocks r hI).trans le_sup_right
  simpa only [inf_eq_right.mpr hQ] using
    inf_pCoreIn_le_of_le 2 ((r.residual_sup_planeSylow_le_for_blocks hI).trans inf_le_right)

/-- The original plane lies in every escaping I. -/
theorem plane_le_escape_for_blocks (hI : PlaneEscapes Mc ⁅V,B⁆ I) : ⁅V,B⁆ ≤ I :=
  (plane_le_centralizer_for_blocks r).trans
    ((r.plane_centralizer_le_intersection hI).trans inf_le_right)

/-- The actual wreath residual has cubic rank at least two before embedding. -/
theorem residual_threeRank_ge_two : 2 ≤ primeRank 3 (pResidual 2 H) := by
  let e := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  rw [primeRank_congr 3 e]
  exact r.residual_rank_two.ge

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.ResidualInput
