module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeExchangedSelection
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ComponentOrbitBound
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation

/-!
# The normalized Bender right factor

The single Bender source row identifies the original component with O²(H).
Its intrinsic two-core quotient is PSL₂, Suzuki, SU₃ or PSU₃ by the existing
central-cover proofs, yielding the singleton right family.

In the exchanged row retain the original C-component. The proved source
geometry supplies its containment, Sylow intersection, intrinsic quotient,
S-normalization and full Borel product. To obtain the missing left-Cartan
action, place the residual normalizer in a maximal two-local subgroup using
its nontrivial two-core. The C-component orbit bound there has size at most
two, so the odd Cartan fixes the selected component whenever it normalizes
the residual. This proves all seven `RightFactor` fields for both Bender
rows, without identifying an exchanged component with the entire residual.

The Chapter 12 extension applies this result to the actual preparation and
global-exit consumers. Diagram selection, uniqueness over L and completion
recognition remain separate obligations of the source assembly.
Source: Aschbacher--Smith, A.3.8(3), E.2.2, 5.1.10--11 and 5.2.4--5,
printed pp.46,215--216,634--635,649--650 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

private theorem residual_normalizer_sqtk
    {T : Sylow 2 G} {L W H : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    IsSQTK KnownSimple.IsKnownSimple (normalizer (residual H : Set G)) := by
  let N := normalizer (residual H : Set G)
  have hne : N ≠ ⊥ := by
    intro hn
    exact residual_not_le T H _ hH.1.1.2 h.sylow_normalizes hH.1.2
      ((residual H).le_normalizer.trans (show N ≤ normalizer (L : Set G) by rw [hn]; exact bot_le))
  have hc : pCore 2 N ≠ ⊥ := by
    intro hc
    have he := residual_normalizer_mem_He h hH
    change N ⊓ centralizer (N.pCoreIn 2 : Set G) ≤ N.pCoreIn 2 at he
    have hz : N.pCoreIn 2 = ⊥ := by
      change (pCore 2 N).map N.subtype = ⊥
      rw [hc, Subgroup.map_bot]
    have hcent : centralizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      centralizer_eq_top_iff_subset.mpr (show (⊥ : Subgroup G) ≤ center G from bot_le)
    rw [hz,hcent,inf_top_eq] at he
    exact hne (le_bot_iff.mp he)
  obtain ⟨M,hM,hNM⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot N hc
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hNM)).mp
    ((h.qtke.twoLocal_sqtk hM.1).subgroup (N.subgroupOf M))

/-- The left odd Cartan fixes every original component of H contained in O²(H)
when it normalizes that residual. The orbit argument takes place in N_G(O²(H)). -/
theorem cartan_normalizes_residual_component
    {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hRK : R ≤ residual H) (hR : (R.subgroupOf H).IsCComponent) :
    A ≤ normalizer (R : Set G) := by
  let K := residual H
  let N := normalizer (K : Set G)
  have hKN : K ≤ N := K.le_normalizer
  have hRN : R ≤ N := hRK.trans hKN
  have hKH : K ≤ H := map_subtype_le _
  have hRC : (R.subgroupOf K).IsCComponent := by
    have hh := hR.subgroupOf_of_le hRK hKH
    exact hh
  have hn : (K.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have hRCN : (R.subgroupOf N).IsCComponent := by
    let e := subgroupOfEquivOfLe hKN
    have hh := (hRC.map_equiv e.symm).map_subtype hn.isSubnormal
    have he : ((R.subgroupOf K).map e.symm.toMonoidHom).map
        (K.subgroupOf N).subtype = R.subgroupOf N := by
      rw [map_map]
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x,hRK hx⟩,hx,rfl⟩
    rwa [he] at hh
  have hQ := ChapterE.Structure.sqtk_two_quotient (residual_normalizer_sqtk h hH) (pCore 2 N) pCore_isPGroup
  let := pCore_isNilpotent (p := 2) (G := N)
  have horbit := cComponent_normal_or_index_two_of_quotient hRCN (pCore 2 N)
    (ChapterA.Section03.ComponentOrbitBound.normal_or_index_two_of_noncentral_structure
      (ChapterA.Section03.CComponentCommutation.noncentralStructureInput KnownSimple.IsKnownSimple)
      hQ (pCore_quotient_pCore_eq_bot 2) (hRCN.map_quotient _))
  have hAN : A ≤ N := c.left_le.trans hN
  have ho : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  intro a ha
  have haN : (⟨a,hAN ha⟩ : N) ∈ normalizer (R.subgroupOf N : Set N) := by
    rcases horbit with hn | hi
    · let := hn
      rw [normalizer_eq_top]
      exact mem_top _
    · have hod : Odd (orderOf (⟨a,hAN ha⟩ : N)) := by
        rw [←Subgroup.orderOf_coe]
        exact ho.of_dvd_nat (by
          simpa only [←Subgroup.orderOf_coe] using orderOf_dvd_natCard (⟨a,ha⟩ : A))
      exact (zpowers_le.mpr ((normalizer (R.subgroupOf N : Set N)).sq_mem_of_index_two hi
        ⟨a,hAN ha⟩)) (mem_zpowers_pow_iff.mpr (Nat.coprime_two_left.mpr hod))
  rw [←subgroupOf_normalizer_eq hRN] at haN
  exact haN

/-- The single Bender row constructs the full singleton family, including
SU₃ and PSU₃; the two quotient kernels are compared before identification. -/
theorem single_bender_source_geometry
    {T : Sylow 2 G} {L H : Subgroup G} {f : ℕ}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    (hm : BenderModel ((normalizer (L : Set G)).subgroupOf H) C f) :
    RightGeometry T L H {residual H} := by
  have hO : pCore 2 H ≤ sourceKernel ((normalizer (L : Set G)).subgroupOf H) := by
    apply normal_le_normalCore.mpr
    exact (pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2)).trans (comap_mono hTL)
  have hr := Prime.single_bender_component_quotient hC hqs hO hc hm
  have he : C = pResidual 2 H :=
    BenderHall.SingleClauses.component_eq_residual (S := T.subtype hH.1.1.2) hc hC
  subst C
  exact rankOne_residual_geometry hTL hH hr

/-- The exchanged source component is a right factor in the normalized branch.
The extra left-Cartan action is proved in the residual normalizer, while the
original factor, quotient, Sylow and full Borel product remain literal. -/
theorem exchanged_source_rightFactor
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n f : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    {C : Subgroup H} (hC : C.IsCComponent)
    (hjoin : C ⊔ (T : Subgroup G).subgroupOf H = ⊤)
    (hc : ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    (hm : ExchangedModel ((normalizer (L : Set G)).subgroupOf H) C f) :
    RightFactor T L H A B (C.map H.subtype) := by
  have d := Prime.exchanged_source_rightData h hH hgen c hC hjoin hc hm
  have hRC : ((C.map H.subtype).subgroupOf H).IsCComponent := by
    change ((C.map H.subtype).comap H.subtype).IsCComponent
    rwa [comap_map_eq_self_of_injective H.subtype_injective]
  exact ⟨d.right_le_residual,d.right_outside,d.right_sylow,d.right_quotient,
    d.S_normalizes_right,
    cartan_normalizes_residual_component h hH c hN d.right_le_residual hRC,d.right_borel⟩

/-- Both original Bender rows supply the normalized right factor with no
remaining component, quotient, Borel or Cartan-action premise. -/
theorem rankOne_source_rightFactor
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hs : RightRankOneSource T L H) :
    ∃ R : Subgroup G, RightFactor T L H A B R := by
  obtain ⟨C,f,hC,hqs,hjoin,_,hc | hc⟩ := hs
  · exact ⟨C.map H.subtype,exchanged_source_rightFactor h hH hgen c hN hC hjoin hc.1 hc.2⟩
  · exact (single_bender_source_geometry h.sylow_normalizes hH hC hqs hc.1 hc.2).exists_rightFactor
      c h.sylow_normalizes hH hN

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
