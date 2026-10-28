module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalSparseExclusion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicLocalContainers
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicLocalContainers
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicFiniteContainers
import all CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFourMax1
/-!
# The original M₂₄ Cartan container is impossible

The actual M₂₄ order is prime to 25, so the original seed equals the
whole residual. Restrict the original Sylow to the same containing image
in Y/O₂(Y), retaining the intrinsic residual quotient through every map.
The source E.2.2 alternatives give either a rank-one quotient or a diagram
quotient. Finite order forces the diagram field to four; the original
escape excludes PSL₃(4), native local geometry excludes SL₃(4), and order
excludes Sp₄(4). In the rank-one case the Mathieu calculation forces
PSL₂(4), excluded by the native M₂₄ local-section theorem.

This is the original-input M₂₄ exclusion used by the remaining-container
assembly. No residual model, trivial two-core, or module coordinates are
assumed. Internal imports reuse checked local calculations without changing
their existing public boundaries.
Source: Aschbacher–Smith A.3.12(14), E.2.2 and 5.1.12–13,
printed pp.47,215–216,635–637, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Chapter1.Section02.LocalModels
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]
/-- The original escaping configuration has no M₂₄ containing quotient. -/
theorem not_mathieu_twentyFour_container
    {T : Sylow 2 G} {L W H A K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M24)) : False := by
  have he := seed_eq_residual_of_normal_twentyFive_free_container h.qtke hK hKT horbit
    hY hescape C hKC (by rw [Nat.card_congr hm.some.toEquiv,Sporadic.Mathieu.m24_order]; norm_num)
  have hR : residual H ∈ Chapter1.L G (T : Subgroup G) := he ▸ hK
  have hRC : residual H ≤ C.map Y.subtype := he ▸ hKC
  have hR' : (pResidual 2 H).IsCComponent := by
    have hh := hR.1
    rw [residual_sup_sylow T H hH.1.1.2] at hh
    simpa only [residual,subgroupOf,comap_map_eq_self_of_injective H.subtype_injective] using hh
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  have hTY := hH.1.1.2.trans hY.2
  let q := QuotientGroup.mk' (pCore 2 Y)
  let S := T.subtype hTY
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  let Rbar := ((residual H).subgroupOf Y).map q
  let Cbar := C.map q
  have hl : (residual H).subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTY hRY).mp ⟨hRY,hR⟩
  have hlq : Rbar ∈ ChapterA.Section03.localCComponents P :=
    Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hl
  have hRC' : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hRC
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  have hle : Rbar ≤ Cbar := map_mono hRC'
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  obtain ⟨Q,hQ,hU⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_restriction
    P hlq hle (hC.map_quotient (pCore 2 Y)).subnormal
  let U := Rbar.subgroupOf Cbar
  have hn : (P : Subgroup (Y ⧸ pCore 2 Y)) ≤ normalizer (Rbar : Set _) := by
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    rw [←subgroupOf_normalizer_eq hRY]
    exact comap_mono (hH.1.1.2.trans (le_normalizer_residual H))
  have hnU : (Q : Subgroup Cbar) ≤ normalizer (U : Set Cbar) := by
    rw [hQ,←subgroupOf_normalizer_eq hle]
    exact comap_mono hn
  let r := q.subgroupMap ((residual H).subgroupOf Y)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let e₀ := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let e₁ := e₀.trans (subgroupOfEquivOfLe hRY).symm
  let e₂ := r.pCoreQuotientEquiv (q.subgroupMap_surjective _) hr
  let e₃ := (subgroupOfEquivOfLe hle).symm
  let eR : ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* (U ⧸ pCore 2 U) :=
    (QuotientGroup.congr _ _ e₁ (pCore_map_iso 2 e₁)).trans
      (e₂.trans (QuotientGroup.congr _ _ e₃ (pCore_map_iso 2 e₃)))
  let eC : Cbar ≃* (C ⧸ pCore 2 C) := (cComponentTwoCoreQuotientEquiv hC).symm
  have hd : Nat.card ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ∣ 244823040 := by
    rw [Nat.card_congr eR.toEquiv]
    have hh := (card_quotient_dvd_card (pCore 2 U)).trans U.card_subgroup_dvd_card
    rw [Nat.card_congr eC.toEquiv] at hh
    rwa [Nat.card_congr hm.some.toEquiv,Sporadic.Mathieu.m24_order] at hh
  have hQ := Chapter3.sqtk_of_mem_H h.qtke hY.1
  have hbar := ChapterE.Structure.sqtk_two_quotient hQ (pCore 2 Y) pCore_isPGroup
  have hCQ := hbar.subgroup Cbar
  have hmodel : ChapterF.Source.IsRankOneModel
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) := by
    rcases Global.right_source_cases h.qtke h.sylow_normalizes hH hgen with hs | hs
    · obtain ⟨K,f,hK,hqs,_,_,hc | hc⟩ := hs
      · have hKR : K = pResidual 2 H := by
          apply hK.eq_of_le hR'
          let := hK.perfect
          apply le_sInf
          rintro N ⟨hn,hN⟩
          let := hn
          let : Group.IsNilpotent (H ⧸ N) := hN.isNilpotent
          exact (le_solvableResidual_of_isPerfect K).trans (solvableResidual_le_of_solvable_quotient N)
        subst K
        obtain ⟨t,_,hne,_⟩ := hc.1.exchanged_product
        exact (hne (mem_normalizer_iff_map_conj_eq.mp
          (show t⁻¹ ∈ normalizer (pResidual 2 H : Set H) by
            rw [normalizer_eq_top]; exact mem_top _)).symm).elim
      · have he : K = pResidual 2 H :=
          BenderHall.SingleClauses.component_eq_residual (S := T.subtype hH.1.1.2) hc.1 hK
        subst K
        have hO : pCore 2 H ≤ sourceKernel ((normalizer (L : Set G)).subgroupOf H) := by
          apply normal_le_normalCore.mpr
          exact (pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2)).trans
            (comap_mono h.sylow_normalizes)
        exact Prime.single_bender_component_quotient hK hqs hO hc.1 hc.2
    · obtain ⟨K,f,hK,hqs,_,hf,hc,hdiagram⟩ := hs
      have hmodels := Prime.diagram_source_residual_quotient h.sylow_normalizes hH.1.1.2 hK hqs hc hf hdiagram
      have hf2 := Prime.diagram_finite_order hf (by simp [Prime.finiteOrders]) hd hmodels
      subst f
      rcases hmodels with hlin | hsl | hsp
      · exact (not_linear_four_residual_of_escape h.qtke h.sylow_normalizes hH hY hescape hlin).elim
      · have hslU : IsSL (U ⧸ pCore 2 U) 3 4 := by
          obtain ⟨F,_,_,hF,⟨a⟩⟩ := hsl
          exact ⟨F,inferInstance,inferInstance,hF,⟨eR.symm.trans a⟩⟩
        exact (Prime.local_sl3_four_not_mathieu hCQ Q U hU hnU hslU (eC.trans hm.some)).elim
      · obtain ⟨F,_,_,hF,⟨a⟩⟩ := hsp
        let : Fintype F := Fintype.ofFinite F
        let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
          (by simpa only [Nat.card_eq_fintype_card] using hF)
        let b := a.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
        rw [Nat.card_congr b.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp,hF] at hd
        norm_num at hd
  have hfour := ChapterF.Source.MathieuLocal.rankOne_quotient_four Q U hU hnU
    (hmodel.of_equiv eR.symm) (.inr (.inr ⟨eC.trans hm.some⟩))
  let e := eC.trans hm.some
  let V := U.map e.toMonoidHom
  let S' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  let v := e.subgroupMap U
  let eqv := QuotientGroup.congr _ _ v (pCore_map_iso 2 v)
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]; infer_instance
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hfour
  exact ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFour.m24_not_section S' V
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hU e.toMonoidHom)
    ((map_mono hnU).trans (le_normalizer_map e.toMonoidHom))
    (eqv.symm.trans (a.trans (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
