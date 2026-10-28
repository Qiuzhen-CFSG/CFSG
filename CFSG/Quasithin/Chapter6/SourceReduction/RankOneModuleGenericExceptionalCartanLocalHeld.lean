module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalMathieuTwentyFour
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeLargerInvariant
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicHeldContainers
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicHeldContainers
public import CFSG.Quasithin.ChapterF.Section01.RankOneHeldLocal

/-!
# The original Held Cartan container and the remaining source alternatives

A normal containing component preserves the original seed: a moved seed
would contradict the checked full-Sylow containing-component theorem,
including its actual A₅-square involution-centralizer argument. Thus the
seed is the whole original residual. Its literal quotient image, with the
restricted full Sylow, is a local component in the Held carrier.

The original E.2.2 rank-one alternative is excluded by the native Held
local-section theorem. In the diagram alternative, the actual Held order
bound forces field four. Escape excludes PSL₃(4), and the checked full-Sylow
Held calculations exclude the SL₃(4) cover and Sp₄(4), retaining their kernels.

Together with the M₂₄ exclusion this removes every remaining simple
non-rank-two carrier. The source reduction keeps the original whole W,
both Hall conditions and the same selected container. Binary triality and
both nonquasisimple alternatives remain explicit; full local escape is
still an assembly obligation. Internal imports reuse this theorem family's
checked diagram calculations without altering their public boundary.
Source: Aschbacher–Smith A.3.12(19), E.2.2 and 5.1.12–13,
printed pp.48,215–216,635–638, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Chapter1.Section02.LocalModels
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]
/-- A normal containing component fixes the original source seed. -/
theorem seed_eq_residual_of_normal_container
    {T : Sylow 2 G} {K H Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTH : (T : Subgroup G) ≤ H)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype) : K = residual H := by
  by_contra hmoved
  have hTY := hTH.trans hY.2
  have hc : ((C.map Y.subtype).subgroupOf Y).IsCComponent := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hC
  have hlocal : C.map Y.subtype ∈ Chapter1.L G (T : Subgroup G) :=
    Chapter1.mem_L_of_cComponent hY.1
      ⟨T.subtype hTY,map_subgroupOf_eq_of_le hTY⟩ (map_subtype_le C) hc
  have hYn : Y ≤ normalizer (C.map Y.subtype : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le C)).mp
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective]
      using (inferInstance : C.Normal)
  apply Prime.LargerInvariant.normalized_chain_impossible hG T hK hlocal hKC (hTY.trans hYn)
  rw [conjugateSpanBy_eq_iSup_conj]
  change K < componentOrbit K (T : Subgroup G)
  exact lt_of_le_of_ne (le_componentOrbit K _) (fun he => hmoved (he.trans horbit))

/-- The original escaping configuration has no Held containing quotient. -/
theorem not_held_container
    {T : Sylow 2 G} {L W H A K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Held.He)) : False := by
  have he := seed_eq_residual_of_normal_container h.qtke hH.1.1.2 hK horbit hY C hC hKC
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
  let e := eC.trans hm.some
  let V := U.map e.toMonoidHom
  let S' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  let v := e.subgroupMap U
  let eqv := QuotientGroup.congr _ _ v (pCore_map_iso 2 v)
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]; infer_instance
  have hlV := Chapter1.Section02.localCComponents_map_of_solvable_ker hU e.toMonoidHom
  have hnV := (map_mono hnU).trans (le_normalizer_map e.toMonoidHom)
  have hd : Nat.card ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ∣ Nat.card Held.He := by
    rw [Nat.card_congr eR.toEquiv]
    have hh := (card_quotient_dvd_card (pCore 2 U)).trans U.card_subgroup_dvd_card
    rwa [Nat.card_congr e.toEquiv] at hh
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
      have hf2 := Prime.held_diagram_degree hf hd hmodels
      subst f
      rcases hmodels with hlin | hsl | hsp
      · exact (not_linear_four_residual_of_escape h.qtke h.sylow_normalizes hH hY hescape hlin).elim
      · obtain ⟨F,_,_,hF,⟨a⟩⟩ := hsl
        exact (Prime.held_local_not_diagram_four S' V hlV hnV
          (.inl ⟨F,inferInstance,inferInstance,hF,⟨eqv.symm.trans (eR.symm.trans a)⟩⟩)).elim
      · obtain ⟨F,_,_,hF,⟨a⟩⟩ := hsp
        exact (Prime.held_local_not_diagram_four S' V hlV hnV
          (.inr ⟨F,inferInstance,inferInstance,hF,⟨eqv.symm.trans (eR.symm.trans a)⟩⟩)).elim
  exact ChapterF.Source.HeldLocal.not_rankOne e Q U hU hnU (hmodel.of_equiv eR.symm)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- Every remaining original container is binary triality or one of the
 two nonquasisimple alternatives. Its seed is the original whole residual. -/
theorem localCartan_escape_binary_or_nonquasisimple
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    (n = 2 ∧ CartanExceptionalConclusion T L W H) ∨
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ C.Normal ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        let I := C.map (QuotientGroup.mk' (pCore 2 Y))
        A36Common I ∧ K = residual H ∧
          ((K = residual H ∧ C.Normal ∧
            Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
            ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8 ∧
            n = 2 ∧ Nat.card A = 3 ∧ A ≤ C.map Y.subtype ∧
            localBorel T L ≤ omegaCentralizer T ∧
            IsOneOrTwoA5Modules L (layer L W) ∧ Nat.card B = 7 ∧
            B ≤ centralizer
              (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L : Set G)) ∨
          A36Natural I ∨ A36Nilpotent I) := by
  rcases localCartan_escape_nonsparse_carriers h hH hgen c hY hescape with hout |
    ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hCn,hKC,hlt,hn,hqlt,hcommon,halt⟩
  · exact .inl hout
  · let := hCn
    have hKR := LocalSieve.seed_eq_residual_of_normal_container h.qtke hH.1.1.2
      hKL hR hY C hC hKC
    refine .inr ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hCn,hKC,hlt,hn,hqlt,hcommon,hKR,?_⟩
    rcases halt with hbin | ⟨_,hm⟩ | hnat | hnil
    · exact .inl hbin
    · rcases hm with hM | hHe
      · exact (LocalSieve.not_mathieu_twentyFour_container h hH hgen hY hescape
          hKL hKT hR C hC hKC hM).elim
      · exact (LocalSieve.not_held_container h hH hgen hY hescape hKL hR C hC hKC hHe).elim
    · exact .inr (.inl hnat)
    · exact .inr (.inr hnil)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
