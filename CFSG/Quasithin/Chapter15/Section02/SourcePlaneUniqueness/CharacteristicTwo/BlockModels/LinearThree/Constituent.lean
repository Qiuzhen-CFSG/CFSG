module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.LinearThree.Escape
public import Theory.GroupTheory.CComponent.OddRadicalNormalizer
public import Theory.GroupTheory.PCoreSubnormalExtension
public import Theory.GroupTheory.SylowNormalizedSupIntersection

/-!
# The original constituent MS pair, including exchanged components

An odd nontrivial subgroup of K intersect X normalizes QI. Modulo O₂(I),
the odd-subgroup normalization lemma forces QI to preserve X. Consequently
S intersect XQI is Sylow in XQI even when S exchanges X with another
component. Restricting the odd-index subgroup KS to XQI gives its actual
centralizer of ZS, with two-core QI. The characteristic-normalizer control
then constructs the genuine MS pair (XQI,QI).

The source application starts from an MS pair (XR,R) with its original
radical R, obtains escape from Mc, and constructs the new pair. It neither
identifies R with QI nor makes the whole exchanged orbit a single linear-three
component. Transport of the C.1.34 module alternatives and comparison with
the local Sylow omega-center remain with qt-e-152-char2-block-exclusion.
The explicit earlier Kc alternative retains its existing geometry and
small-parabolic producers and final plane-uniqueness discharge.

Source: Aschbacher--Smith, preliminary 15.2.23, printed pp.1115--1116;
C.1.31--34, printed pp.135--137, refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
open Section01 Section03 ChapterA.Section04 ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- QI preserves each original constituent, whether or not S preserves it. -/
theorem linearThree_parabolic_core_normalizes_component
    (hI : PlaneEscapes Mc ZS I) {X : Subgroup I} (hX : X.IsCComponent)
    (e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL) :
    (planeParabolicCore T H ZS).subgroupOf I ≤ normalizer (X : Set I) := by
  obtain ⟨D,hDX,ho,hd,hDK⟩ := d.linearThree_component_odd_intersection hI hX e
  let Q := planeParabolicCore T H ZS
  have hQI : Q ≤ I := (pCoreIn_le 2 _).trans
    ((d.residual_sup_planeSylow_le hI).trans inf_le_right)
  have hDQ : D ≤ normalizer (Q.subgroupOf I : Set I) := by
    rw [←subgroupOf_normalizer_eq hQI]
    intro x hx
    exact d.planeParabolicCore_normalized hI
      (map_subtype_le (pResidual 2 H) (hDK (mem_map_of_mem I.subtype hx)))
  let : IsSimpleGroup Matrix.PSL3Two.PSL :=
    Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup (X ⧸ pCore 2 X) := e.isSimpleGroup
  exact normalizes_cComponent_of_odd_subgroup X (Q.subgroupOf I) D hX
    (isPGroup_pCoreIn 2 _).comap_subtype ho hd hDX hDQ

/-- The original Sylow intersection is Sylow in the constituent extension. -/
theorem linearThree_component_extension_sylow
    (hI : PlaneEscapes Mc ZS I) {X : Subgroup I} (hX : X.IsCComponent)
    (e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL) :
    Chapter1.IsSylowIn 2
      (planeSylow T ZS ⊓ (X.map I.subtype ⊔ planeParabolicCore T H ZS))
      (X.map I.subtype ⊔ planeParabolicCore T H ZS) := by
  let Q := (planeParabolicCore T H ZS).subgroupOf I
  have hQI : planeParabolicCore T H ZS ≤ I := (pCoreIn_le 2 _).trans
    ((d.residual_sup_planeSylow_le hI).trans inf_le_right)
  obtain ⟨S,hS⟩ := d.sylow_in_escape hI
  have hQS : Q ≤ (S : Subgroup I) := by
    intro q hq
    have hh := d.planeParabolicCore_le_plane hI hq
    rw [←hS] at hh
    obtain ⟨a,ha,he⟩ := hh
    exact (Subtype.ext he : a = q) ▸ ha
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_sup_of_normalized X Q hQS
    (d.linearThree_parabolic_core_normalizes_component hI hX e)
    (S.exists_subgroupOf_eq_of_subnormal X hX.subnormal)
  have hs : Chapter1.IsSylowIn 2 ((S : Subgroup I) ⊓ (X ⊔ Q)) (X ⊔ Q) :=
    ⟨P,by rw [hP,subgroupOf_map_subtype]⟩
  have hm := Chapter1.Section02.IndexTwo.isSylowIn_map hs I.subtype
  rwa [Subgroup.map_inf _ _ _ I.subtype_injective,hS,Subgroup.map_sup,
    map_subgroupOf_eq_of_le hQI] at hm


/-- Restrict KS to XQI. The result is precisely C_XQI(ZS), with two-core QI,
and has proper odd index. No normality of X in I is assumed. -/
theorem linearThree_component_ms_odd_index
    (hI : PlaneEscapes Mc ZS I) {X : Subgroup I} (hX : X.IsCComponent)
    (e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL)
    (hout : ¬ X.map I.subtype ≤ Mc) :
    MSOddIndex (X.map I.subtype) (planeParabolicCore T H ZS) ∧
      ((X.map I.subtype ⊔ planeParabolicCore T H ZS) ⊓
        centralizer (ZS : Set G)).pCoreIn 2 = planeParabolicCore T H ZS := by
  let P0 := (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS
  let Q0 := planeParabolicCore T H ZS
  let P := P0.subgroupOf I
  let Q := Q0.subgroupOf I
  let N := X ⊔ Q
  let E := X.map I.subtype ⊔ Q0
  let A := P0 ⊓ E
  have hPI : P0 ≤ I := (d.residual_sup_planeSylow_le hI).trans inf_le_right
  have hQI : Q0 ≤ I := (pCoreIn_le 2 _).trans hPI
  have heQ : P.pCoreIn 2 = Q := pCoreIn_subgroupOf 2 P0 I hPI
  have hQX : Q ≤ normalizer (X : Set I) :=
    d.linearThree_parabolic_core_normalizes_component hI hX e
  have hPodd : Odd P.index := by
    obtain ⟨S,hS⟩ := d.sylow_in_escape hI
    have hSP : (S : Subgroup I) ≤ P := by
      intro s hs
      exact (le_sup_right : planeSylow T ZS ≤ P0) (hS ▸ mem_map_of_mem I.subtype hs)
    exact Nat.not_even_iff_odd.mp (by
      rw [even_iff_two_dvd]
      exact fun hh => S.not_dvd_index (hh.trans (index_dvd_of_le hSP)))
  have heN : N.map I.subtype = E := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hQI]
  have heP : P.map I.subtype = P0 := map_subgroupOf_eq_of_le hPI
  have hc : A.pCoreIn 2 = Q0 := by
    have hh := pCoreIn_subnormal_core_supplement X P hX.subnormal (heQ.symm ▸ hQX)
    rw [heQ] at hh
    have hm := congrArg (Subgroup.map (I.subtype.comp N.subtype)) hh
    rw [map_pCoreIn_of_injective 2 (P.subgroupOf N) (I.subtype.comp N.subtype)
      (I.subtype_injective.comp N.subtype_injective),
      ←map_map,subgroupOf_map_subtype,Subgroup.map_inf _ _ _ I.subtype_injective,
      heP,heN,←map_map,map_subgroupOf_eq_of_le (show Q ≤ N from le_sup_right),
      map_subgroupOf_eq_of_le hQI] at hm
    exact hm
  have ho : Odd (A.subgroupOf E).index := by
    have hh := odd_index_subnormal_core_supplement X P hX.subnormal (heQ.symm ▸ hQX) hPodd
    rw [heQ] at hh
    change Odd (P.relIndex N) at hh
    rw [← relIndex_map_map_of_injective P N I.subtype_injective,heP,heN] at hh
    change Odd ((P0 ⊓ E).relIndex E)
    rwa [inf_relIndex_right]
  have hPZ : P0 ≤ centralizer (ZS : Set G) := sup_le d.residual_centralizes inf_le_right
  have hproper : A < E := lt_of_le_of_ne inf_le_right (by
    intro he
    apply hout
    have hEP : E ≤ P0 := he ▸ (show A ≤ P0 from inf_le_left)
    exact (le_sup_left.trans hEP).trans
      ((d.residual_sup_planeSylow_le hI).trans inf_le_left))
  have hCE : E ⊓ centralizer (ZS : Set G) = A := by
    apply le_antisymm
    · rintro g ⟨hg,hgZ⟩
      have hnorm : Q0 ≤ normalizer (X.map I.subtype : Set G) := by
        rw [←map_subgroupOf_eq_of_le hQI]
        exact (map_mono hQX).trans (le_normalizer_map I.subtype)
      have hp : g ∈ (X.map I.subtype : Set G) * (Q0 : Set G) := by
        rw [← coe_mul_of_right_le_normalizer_left _ _ hnorm]
        exact hg
      obtain ⟨x,hx,q,hq,he⟩ := hp
      have hxZ : x ∈ centralizer (ZS : Set G) := by
        have hh := (centralizer (ZS : Set G)).mul_mem hgZ
          ((centralizer (ZS : Set G)).inv_mem (hPZ (pCoreIn_le 2 P0 hq)))
        rwa [←he,mul_inv_cancel_right] at hh
      refine ⟨?_,hg⟩
      rw [←he]
      exact P0.mul_mem ((d.linearThree_component_centralizer_parabolic hI hX e hout).2.2
        ⟨hx,hxZ⟩) (pCoreIn_le 2 P0 hq)
    · exact fun _ hg => ⟨hg.2,hPZ hg.1⟩
  exact ⟨⟨A,hproper,ho,hc⟩,hCE ▸ hc⟩


/-- The constituent parabolic marking supplies all MS-pair hypotheses. -/
theorem linearThree_component_msPair_of_escape
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : X.IsCComponent)
    (e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL)
    (hout : ¬ X.map I.subtype ≤ Mc) :
    LinearThreeMSPair KnownSimple.IsKnownSimple (X.map I.subtype)
      (planeParabolicCore T H ZS) 1 (ZMod 2) := by
  let Y := X.map I.subtype
  let a : X ≃* Y := X.equivMapOfInjective I.subtype I.subtype_injective
  let eQ : (Y ⧸ pCore 2 Y) ≃* Matrix.PSL3Two.SL :=
    ((QuotientGroup.congr _ _ a.symm (pCore_map_iso 2 a.symm)).trans e).trans
      Matrix.PSL3Two.equiv.symm
  have hY : Y ∈ Chapter1.cComponentsIn I := by
    refine ⟨map_subtype_le _,?_⟩
    have he : Y.subgroupOf I = X := comap_map_eq_self_of_injective I.subtype_injective X
    rwa [he]
  have hEI : Y ⊔ planeParabolicCore T H ZS ≤ I := sup_le hY.1
    ((pCoreIn_le 2 _).trans ((d.residual_sup_planeSylow_le hI).trans inf_le_right))
  refine ⟨by decide,by norm_num [Nat.card_eq_fintype_card],⟨eQ⟩,?_,
    d.plane_extension_fitting hI hfit hY.1,?_,
    Or.inl (d.linearThree_component_ms_odd_index hI hX e hout).1,
    d.plane_ms_characteristic hI hout⟩
  · exact (IsSQTK.equiv (subgroupOfEquivOfLe hEI)).mp
      ((Chapter3.sqtk_of_mem_H hsource.ambient hI.1).subgroup _)
  · exact ⟨le_sup_left,hY.2.subgroupOf_of_le le_sup_left hEI⟩

/-- Apply the construction to the actual source MS component and radical.
The earlier Kc alternative is discharged by the enclosing plane assembly. -/
theorem linearThree_component_msPair_of_source
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : X.IsCComponent)
    (e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL)
    {R : Subgroup G} (hpR : IsPGroup 2 R) {n : ℕ} {F : Type} [Field F] [Finite F]
    (hms : LinearThreeMSPair KnownSimple.IsKnownSimple (X.map I.subtype) R n F) :
    LinearThreeMSPair KnownSimple.IsKnownSimple (X.map I.subtype)
      (planeParabolicCore T H ZS) 1 (ZMod 2) :=
  d.linearThree_component_msPair_of_escape hI hfit hX e
    (d.linearThree_ms_component_not_le_partner horbit hI hX e hpR hms)

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
