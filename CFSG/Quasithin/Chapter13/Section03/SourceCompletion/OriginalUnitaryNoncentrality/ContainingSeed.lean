module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Components.OrdinaryNoncontainment

/-!
# The seed in a containing component

Under the contrary containment L₁≤K, seed generation and reduction (a) put
V₃ in the intrinsic module of K. The cubic action forces O₂(KL₁T) to
centralize V₃. Its normal closure is therefore reduced, and generation
places V₃ in the literal [R₂(KL₁T),K]. All normality is relative to the
original point normalizer. The unitary source application is in ReductionG.
Source: Aschbacher--Smith 13.3.14(g), printed pp.892--893.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterA.Section04 Noncentrality
variable {G : Type*} [Group G] [Finite G]

/-- In the containing branch, a point residual generating the elementary seed
puts it in the literal moved reduced module of the selected component. -/
theorem seed_le_movedModule_of_actor_le
    (T : Sylow 2 G) (H A U : Subgroup G) [IsElementaryAbelian 2 U]
    (hTH : (T : Subgroup G) ≤ H) (hAH : A ≤ H)
    (hU : Nat.card U = 8) (hA : IsPPerfect 2 A)
    (hA3 : Nat.card (A ⧸ pCore 2 A) = 3)
    (hAU : A ≤ normalizer (U : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hgenU : ⁅U,A⁆ = U) (hUQ : U ≤ omegaOneCenterAmbient (H.pCoreIn 2))
    (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hHN : H ≤ normalizer (K.map H.subtype : Set G))
    (hAK : A ≤ K.map H.subtype) :
    U ≤ Diagonal.movedModule (K.map H.subtype) A T := by
  let B := K.map H.subtype
  let J := Diagonal.localGroup B A T
  let K₀ := B.subgroupOf J
  let S := (T : Subgroup G).subgroupOf J
  let I := intrinsicSignalizerModule B
  have hBJ : B ≤ J := le_sup_left.trans le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hJH : J ≤ H := sup_le (sup_le (map_subtype_le _) hAH) hTH
  have hJN : J ≤ normalizer (B : Set G) := hJH.trans hHN
  let : K₀.Normal := normal_subgroupOf_of_le_normalizer hJN
  have hp : IsPPerfect 2 K := by
    let := hK.perfect
    intro N hn hp
    let := hn
    let := hp.isNilpotent
    exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)
  have hUI : U ≤ I := by
    have hi := map_mono (f := H.subtype)
      (subnormal_omega_commutator_le_intrinsicModule K hK.subnormal hp)
    rw [map_commutator, ← intrinsicSignalizerModule_map_of_injective H.subtype
      H.subtype_injective, ← omegaOneCenterAmbient_map_injective H.subtype
      H.subtype_injective] at hi
    exact hgenU.symm.le.trans ((commutator_mono hUQ hAK).trans hi)
  have hcore : J.pCoreIn 2 ≤ centralizer (U : Set G) := by
    have hQB : J.pCoreIn 2 ≤ normalizer (B : Set G) := (pCoreIn_le 2 J).trans hJN
    have hBQ : B ≤ normalizer (J.pCoreIn 2 : Set G) :=
      hBJ.trans (J.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore J))
    have hcomm : ⁅B,J.pCoreIn 2⁆ ≤ B.pCoreIn 2 :=
      (le_inf (le_normalizer_iff_commutator_le_left.mp hQB)
        (le_normalizer_iff_commutator_le_right.mp hBQ)).trans (inf_pCoreIn_le_of_le 2 hBJ)
    have hcommU : ⁅A,J.pCoreIn 2⁆ ≤ centralizer (U : Set G) :=
      (commutator_mono hAK le_rfl).trans
        ((commutator_le_centralizer_intrinsicModule B _ hcomm).trans (centralizer_le hUI))
    have hQT : J.pCoreIn 2 ≤ (T : Subgroup G) := by
      have ht := pCoreIn_le_sylow J (T.subtype hTJ)
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTJ] using ht
    have hm : ⁅U,A⁆ ≠ ⊥ := by
      rw [hgenU]
      intro he
      rw [he,card_bot] at hU
      omega
    exact centralizes_elementary_eight_of_commuting_cubic_section U A (J.pCoreIn 2)
      hU hA hA3 hAU (hQT.trans hTU) (isPGroup_pCoreIn 2 J) hcommU hm
  have hK₀ : K₀.IsCComponent := by
    have hh : (B.subgroupOf H).IsCComponent := by
      change ((K.map H.subtype).comap H.subtype).IsCComponent
      rwa [comap_map_eq_self_of_injective H.subtype_injective]
    exact hh.subgroupOf_of_le hBJ hJH
  let := hqK
  let c : K ≃* K₀ := (K.equivMapOfInjective H.subtype H.subtype_injective).trans
    (subgroupOfEquivOfLe hBJ).symm
  let : IsQuasisimple (K₀ ⧸ pCore 2 K₀) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ c (pCore_map_iso 2 c))
  have hgen : K₀ ⊔ S = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hBJ,map_subgroupOf_eq_of_le hTJ,
      ←MonoidHom.range_eq_map,range_subtype]
    change B ⊔ (T : Subgroup G) = (B ⊔ A) ⊔ (T : Subgroup G)
    rw [sup_eq_left.mpr hAK]
  have hIJ : I ≤ J := (intrinsicModule_le_self B).trans hBJ
  let : (I.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (hJN.trans (normalizer_le_normalizer_intrinsicModule B))
  let : IsElementaryAbelian 2 I := signalizerModule_elementaryAbelian B _
    (B.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore B))
  let : IsElementaryAbelian 2 (I.subgroupOf J) := IsElementaryAbelian.subgroupOf hIJ
  have hUJ : U ≤ J := hUI.trans hIJ
  have hc₀ : pCore 2 J ≤ centralizer (U.subgroupOf J : Set J) := by
    intro q hq u hu
    apply Subtype.ext
    exact hcore (mem_map_of_mem J.subtype hq) u hu
  have hm : ⁅U.subgroupOf J,K₀⁆ ≠ ⊥ := by
    intro he
    have hh := congrArg (fun D : Subgroup J => D.map J.subtype) he
    rw [map_commutator,map_subgroupOf_eq_of_le hUJ,
      map_subgroupOf_eq_of_le hBJ,Subgroup.map_bot] at hh
    have hu : U = ⊥ := le_bot_iff.mp (hgenU.symm.le.trans
      ((commutator_mono le_rfl hAK).trans hh.le))
    rw [hu,card_bot] at hU
    omega
  have hred := seed_le_reduced_of_component_supplement K₀ S (I.subgroupOf J)
    (U.subgroupOf J) hK₀ T.isPGroup'.comap_subtype hgen (comap_mono hUI) hc₀ hm
  have hUW : U ≤ Diagonal.reducedModule B A T := by
    have hh := map_mono (f := J.subtype) hred
    rwa [map_subgroupOf_eq_of_le hUJ] at hh
  exact hgenU.symm.le.trans (commutator_mono hUW hAK)
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
