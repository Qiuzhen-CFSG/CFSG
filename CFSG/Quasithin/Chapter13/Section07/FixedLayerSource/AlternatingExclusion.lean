module
public import CFSG.Quasithin.Chapter13.Section07.FixedLayerSource.DoubleThree
public import CFSG.Quasithin.Chapter13.Section07.FixedLayerSource.AlternatingSixRows

/-!
# Alternating component exclusion in the original fixed-layer argument

The moved tilde module has two noncentral layers and therefore is not Irr⁺.
For an alternating-five component, the actual offender overgroup has a
2-group quotient and trivial 2-core. The complete adequate rank-one
classification gives Irr⁺: its only other row has an SL₃ binary-field
actor, whose order is divisible by eight, unlike 60. This contradicts the
original two-layer extraction on the same component and quotient action.
For the alternating-six row, the same overgroup has trivial component
centralizer; the full order-360 FF classification likewise gives Irr⁺.

The source-facing theorem retains the original conjugator and selected
component; no constituent marking or extra classification premise is added.
Source: Aschbacher–Smith 13.7.16(2), printed p.944, using B.5.6 and B.5.1(1).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section07
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem alternatingFive_irrPlus_of_component_rows
    (ρ : Representation (ZMod 2) G V) {E : Subgroup G} {C : Subgroup E}
    [C.Normal] [IsQuasisimple C]
    (hfaith : Function.Injective ρ) (hcore : pCore 2 E = ⊥)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple E)
    (hCN : C ≤ offenderSubgroup (ρ.comp E.subtype)) (hr : primeRank 3 E ≤ 1)
    (hwhole : moved (ρ.comp E.subtype) C = ⊤) (hcard : Nat.card C = 60) :
    IsIrrPlus (ρ.comp E.subtype) C ⊤ := by
  let σ := ρ.comp E.subtype
  let N := offenderSubgroup σ
  let L := C.subgroupOf N
  obtain ⟨c,hc⟩ := PlusAction.OddFFRows.component_rankOne_rows σ
    (hfaith.comp E.subtype_injective) hcore cover hCN hr
  let s := c.sectionData
  have hspace : s.space.toSubmodule = ⊤ := by
    rw [s.space_eq]
    change subspaceCommutator (σ.comp N.subtype) ⊤ L = ⊤
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hCN]
    exact hwhole
  cases hc with
  | irreducible hi _ _ _ _ =>
    have hi' : IsIrrPlus (σ.comp N.subtype) L ⊤ := hspace ▸ hi
    exact (IsIrrPlus.subgroupOf_iff σ C N hCN ⊤).mp hi'
  | doubleThree F _ _ e _ _ =>
    have hcardL : Nat.card L = 60 :=
      (Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv).trans hcard
    have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) = 60 :=
      (Nat.card_congr e.groupEquiv.toEquiv).symm.trans hcardL
    have hd := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card
    rw [Matrix.PSL3.LinearThree.card_unipotentSL,F.card_eq,hSL,←pow_mul] at hd
    have he : 8 ∣ 60 := (Nat.pow_dvd_pow 2
      (show 3 ≤ F.degree * 3 by have := F.degree_pos; omega)).trans hd
    norm_num at he

theorem alternatingFive_irrPlus_of_component_overgroup
    {V₀ : Type*} [AddCommGroup V₀] [Module (ZMod 2) V₀]
    [FiniteDimensional (ZMod 2) V₀]
    (σ : Representation (ZMod 2) G V) (hf : Function.Injective σ)
    (σ₀ : Representation (ZMod 2) G V₀) (hf₀ : Function.Injective σ₀)
    (cover : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple G)
    {J D : Subgroup G} [J.Normal] [IsSimpleGroup J]
    (hi : IsIrrPlus σ₀ J ⊤) (hJ : IsComponent G J)
    (hc : Nat.card J = 60) (hD2 : IsPGroup 2 D)
    (hD : IsBestOffender σ D) (hcomm : ⁅J,D⁆ = J)
    (hm : moved σ J = ⊤) :
    IsIrrPlus σ J ⊤ := by
  let E := J ⊔ D
  let C := J.subgroupOf E
  have hJE : J ≤ E := le_sup_left
  have hDE : D ≤ E := le_sup_right
  let : C.Normal := inferInstance
  let : IsQuasisimple J := hJ.2
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hJE).symm
  have hcore := component_overgroup_twoCore_eq_bot σ₀ hf₀ hi hJ E hJE
  have hC : IsComponent E C := hJ.subgroupOf hJE
  have hD' := hD.subgroupOf σ hDE
  have hcomm' : ⁅C,D.subgroupOf E⁆ = C := by
    apply Subgroup.map_injective E.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hJE,map_subgroupOf_eq_of_le hDE,hcomm]
  have hCN := (ChapterB.SourceInduction.moved_component_in_offenderSubgroup
    (σ.comp E.subtype) (hf.comp E.subtype_injective) hC hD' hcomm').1
  have hquot : IsPGroup 2 (E ⧸ C) := by
    apply isPGroup_quotient_of_sup_eq_top C (D.subgroupOf E) hD2.comap_subtype
    rw [← Subgroup.subgroupOf_sup hJE hDE, Subgroup.subgroupOf_self]
  have hc' : Nat.card C = 60 :=
    (Nat.card_congr (subgroupOfEquivOfLe hJE).toEquiv).trans hc
  have hrC : primeRank 3 C ≤ 1 := by
    obtain ⟨P,_,hPc⟩ := exists_elementaryAbelian_card_primeRank (G := C) (p := 3)
    have hd : 3 ^ primeRank 3 C ∣ Nat.card C := hPc ▸ P.card_subgroup_dvd_card
    by_contra hn'
    have h9 : 9 ∣ Nat.card C :=
      (Nat.pow_dvd_pow 3 (show 2 ≤ primeRank 3 C by omega)).trans hd
    norm_num [hc'] at h9
  have hr : primeRank 3 E ≤ 1 :=
    (primeRank_le_of_normal_two_quotient C hquot 3 (by decide)).trans hrC
  have hm' : moved (σ.comp E.subtype) C = ⊤ := by
    change subspaceCommutator (σ.comp E.subtype) ⊤ C = ⊤
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hJE]
    exact hm
  exact (IsIrrPlus.subgroupOf_iff σ J E hJE ⊤).mp
    (alternatingFive_irrPlus_of_component_rows σ hf hcore
      (cover.subgroup E) hCN hr hm' hc')

theorem component_tilde_alternatingFive_false
    {V₀ : Type*} [AddCommGroup V₀] [Module (ZMod 2) V₀]
    [FiniteDimensional (ZMod 2) V₀]
    (ρ : Representation (ZMod 2) G V)
    (σ₀ : Representation (ZMod 2) G V₀) (hf₀ : Function.Injective σ₀)
    (cover : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple G)
    {J D : Subgroup G} [J.Normal] [IsSimpleGroup J]
    (hi : IsIrrPlus σ₀ J ⊤) (hJ : IsComponent G J) (hc : Nat.card J = 60)
    (hp : ∀ k : G, (∀ v ∈ subspaceCommutator ρ ⊤ J,ρ k v = v) → k = 1)
    (hn : ¬ IsIrrPlus ρ J (subspaceCommutator ρ ⊤ J))
    (hD : IsBestOffender (subspaceImageRepresentation ρ (subspaceCommutator ρ ⊤ J))
      (restrictedSubgroup ρ (subspaceCommutator ρ ⊤ J) D))
    (hD2 : IsPGroup 2 D) (hDne : D ≠ ⊥)
    (hDC : D ⊓ centralizer (J : Set G) = ⊥) : False := by
  let I := subspaceCommutator ρ ⊤ J
  have hs : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ I :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) (by rw [J.normalizer_eq_top])
  let τ := wholeSubspaceAction ρ I hs
  have hf := wholeSubspaceAction_faithful ρ I hs hp
  have hDτ := wholeSubspaceAction_bestOffender ρ I hs hp hD
  let : IsQuasisimple J := hJ.2
  let : Group.IsPerfect J := inferInstance
  have hm : moved τ J = ⊤ := by
    apply Submodule.map_injective_of_injective I.subtype_injective
    have hh := subspaceCommutator_map_embedding ρ τ (MonoidHom.id G)
      I.subtype (fun g v => (wholeSubspaceAction_apply ρ I hs g v).symm) J ⊤
    simpa only [Subgroup.map_id,Submodule.map_top,Submodule.range_subtype, I,
      subspaceCommutator_idempotent_of_perfect] using hh.symm
  have hnτ : ¬ IsIrrPlus τ J ⊤ := by
    intro hι
    apply hn
    have hι' : IsIrrPlus τ (J.map (MonoidHom.id G)) ⊤ := by
      simpa only [Subgroup.map_id] using hι
    have hh := IsIrrPlus.map_embedding ρ τ (MonoidHom.id G) I.subtype
      I.subtype_injective (fun g v => (wholeSubspaceAction_apply ρ I hs g v).symm) J ⊤ hι'
    simpa only [Submodule.map_top,Submodule.range_subtype] using hh
  have hcomm := simple_component_commutator_of_faithful_two_actor hDne hDC
  exact hnτ (alternatingFive_irrPlus_of_component_overgroup τ hf σ₀ hf₀ cover hi hJ hc
    hD2 hDτ hcomm hm)

end CFSG.Quasithin.Chapter13.Section07

namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup ChapterB.QuasisimpleSource
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
theorem source_no_fixed_layer_alternatingFive
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (B : Subgroup (H ⧸ pCore 2 H)) (hB : IsMinimalBestOffender σ B)
    (hBA : B ≤ ((conjugate (Section08.Source.VH H V) (g : G) ⊓
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H)))
    (K : Subgroup H) (hKC : K.IsCComponent) (hK : IsComponent (H ⧸ pCore 2 H)
      (K.map (QuotientGroup.mk' (pCore 2 H))))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2)
    (hcomm : ⁅K.map (QuotientGroup.mk' (pCore 2 H)),B⁆ = K.map (QuotientGroup.mk' (pCore 2 H)))
    (hm : ⁅PlusAction.fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H),
      K.map H.subtype⁆ ≠ ⊥)
    (ha : Chapter1.Section02.LocalModels.IsAlternating (K.map (QuotientGroup.mk' (pCore 2 H))) 5) : False := by
  obtain ⟨hE,ρ,_c,_,_hcoord,hpoint,hnot,D,hDle,hD,_,hDimage,_⟩ :=
    source_tilde_component_FF_of_fixed_layer_movement d h hU hV hne g hs hout
      σ s B hB hBA K hKC hK hk hcomm hm
  let := hE
  let π := QuotientGroup.mk' (pCore 2 H)
  let J := K.map π
  have hnK := source_plus_component_normal d h hU hV hne g hs hout
    σ s B hB hBA K hKC hK hk hcomm
  let : J.Normal := Subgroup.Normal.map hnK π (QuotientGroup.mk'_surjective _)
  obtain ⟨eJ⟩ := ha
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup J := eJ.isSimpleGroup
  have hc : Nat.card J = 60 := by
    rw [Nat.card_congr eJ.toEquiv,nat_card_alternatingGroup]
    norm_num
  have hi := (source_plus_component_irrPlus_and_actor d h hU hV hne g hs hout
    σ s B hB hBA K hK hk hcomm).1
  have hwhole := source_plus_component_whole d h hU hV hne g hs hout
    σ s B hB hBA K hKC hK hk hcomm
  rw [hwhole] at hi
  obtain ⟨hUgA,_,_,_⟩ := pair_conjugate_seed_quotient_nontrivial d h hU hV g hs hout
  have hUgT : conjugate (Section08.Source.UH H V₃) (g : G) ≤ (T : Subgroup G) :=
    hUgA.trans inf_le_right |>.trans (h.sylow_centralizer.symm.le.trans inf_le_left)
  have hDS : D ≤ ((T : Subgroup G).subgroupOf H).map π :=
    hDle.trans (map_mono (comap_mono hUgT))
  have hcS := source_plus_sylow_centralizer_eq_bot d h hU hV hne g hs hout
    σ s B hB hBA K hKC hK hk hcomm
  have hDC : D ⊓ centralizer (J : Set (H ⧸ pCore 2 H)) = ⊥ := by
    apply bot_unique
    rw [← hcS]
    exact inf_le_inf_right _ hDS
  exact component_tilde_alternatingFive_false ρ σ
    (source_plus_faithful_of_kernel_eq σ s hk) (source_plus_sqtk_cover d h)
    hi hK hc hpoint hnot hDimage hD.1.2.isPGroup hD.1.1 hDC


theorem source_no_fixed_layer_alternatingSix
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (B : Subgroup (H ⧸ pCore 2 H)) (hB : IsMinimalBestOffender σ B)
    (hBA : B ≤ ((conjugate (Section08.Source.VH H V) (g : G) ⊓
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H)))
    (K : Subgroup H) (hKC : K.IsCComponent) (hK : IsComponent (H ⧸ pCore 2 H)
      (K.map (QuotientGroup.mk' (pCore 2 H))))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2)
    (hcomm : ⁅K.map (QuotientGroup.mk' (pCore 2 H)),B⁆ = K.map (QuotientGroup.mk' (pCore 2 H)))
    (hm : ⁅PlusAction.fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H),
      K.map H.subtype⁆ ≠ ⊥)
    (ha : Chapter1.Section02.LocalModels.IsAlternating (K.map (QuotientGroup.mk' (pCore 2 H))) 6) : False := by
  obtain ⟨hE,ρ,_c,_,_hcoord,hpoint,hnot,D,hDle,hD,_,hDimage,_⟩ :=
    source_tilde_component_FF_of_fixed_layer_movement d h hU hV hne g hs hout
      σ s B hB hBA K hKC hK hk hcomm hm
  let := hE
  let π := QuotientGroup.mk' (pCore 2 H)
  let J := K.map π
  have hnK := source_plus_component_normal d h hU hV hne g hs hout
    σ s B hB hBA K hKC hK hk hcomm
  let : J.Normal := Subgroup.Normal.map hnK π (QuotientGroup.mk'_surjective _)
  obtain ⟨eJ⟩ := ha
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup J := eJ.isSimpleGroup
  have hc : Nat.card J = 360 := by
    rw [Nat.card_congr eJ.toEquiv,nat_card_alternatingGroup]
    norm_num
  have hi := (source_plus_component_irrPlus_and_actor d h hU hV hne g hs hout
    σ s B hB hBA K hK hk hcomm).1
  have hwhole := source_plus_component_whole d h hU hV hne g hs hout
    σ s B hB hBA K hKC hK hk hcomm
  rw [hwhole] at hi
  exact component_tilde_alternatingSix_false ρ σ
    (source_plus_faithful_of_kernel_eq σ s hk) (source_plus_sqtk_cover d h)
    hi hK hc hpoint hnot hDimage hD.1.2.isPGroup

end CFSG.Quasithin.Chapter13.Section07
