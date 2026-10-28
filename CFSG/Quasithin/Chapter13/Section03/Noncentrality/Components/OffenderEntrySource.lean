module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Components.ReducedQuotientSource
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedImages
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.GroupTheory.CComponent.QuasisimpleImage
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Intrinsic
public import Theory.GroupTheory.CentralPChiefFactorsOddQuotient

/-!
# The selected component in the reduced offender quotient

For W=R₂(J), the true centralizer quotient J/C_J(W) acts faithfully on W.
Thompson generation [K,J(T)]=K places the image of K in its offender subgroup.
A nontrivial intrinsic module ensures that this image survives as an ordinary
component, so the trivial B.5 alternative is excluded. All other full B.5
alternatives, including augmentation-core rows, are retained.

The coordinate comparison identifies the original ambient commutator
[W.map J.subtype,K] with the moved subspace of the literal quotient action.
Its linear equivalence preserves each underlying element of the original
ambient group. The natural-source consumer obtains SQTK from the prescribed
point normalizer; it assumes neither faithfulness nor a trivial two-core for J.

The generation premise is the exact earlier input from genuine 3.1.8(3).
Guarded 3.1.8(1) does not supply it. Selection of the final single-module or
repeated L₃ row remains a subsequent source step.
Source: Aschbacher–Smith, 13.3.14(f–g), printed pp.892–893, and B.5.6.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G]

theorem thompson_generated_image_le_offender
    (T : Sylow 2 G) (K : Subgroup G)
    (hgen : ⁅K,elementaryAbelianMaxJ (T : Subgroup G)⁆ = K) :
    let W := reducedTwoSubgroup G
    let := (isPReduced_reducedPSubgroup (p := 2) (G := G)).elementary
    let C := centralizer (W : Set G)
    let q := QuotientGroup.mk' C
    K.map q ≤ offenderSubgroup
      (NormalElementaryQuotient.representation W q
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)) := by
  let W := reducedTwoSubgroup G
  let := (isPReduced_reducedPSubgroup (p := 2) (G := G)).elementary
  let C := centralizer (W : Set G)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  have hW : W ≤ (T : Subgroup G) :=
    (reducedPSubgroup_le_pCore 2 G).trans (pCore_isPGroup.le_sylow_of_normal T)
  have hJT := ChapterB.RankOneBaumann.thompson_image_le_offender_layer T W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) hW (offenderSubgroup ρ) le_rfl
  have hn := offenderSubgroup_normal ρ
  let : (offenderSubgroup ρ).Normal := hn
  change K.map q ≤ offenderSubgroup ρ
  rw [←hgen,map_commutator]
  exact (commutator_mono le_rfl hJT).trans (commutator_le_right _ _)

theorem faithful_component_reduced_image
    (K : Subgroup G) [K.Normal] (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K)) (hfaith : intrinsicSignalizerModule K ≠ ⊥) :
    IsComponent (G ⧸ centralizer (reducedTwoSubgroup G : Set G))
      (K.map (QuotientGroup.mk' (centralizer (reducedTwoSubgroup G : Set G)))) := by
  let W := reducedTwoSubgroup G
  let C := centralizer (W : Set G)
  let := hqK
  have hchief : HasCentralPChiefFactorsAbove 2 (pCore 2 K) := by
    apply (hasCentralPChiefFactorsAbove_iff_quotient (pCore 2 K)).mpr
    apply hasCentralTwoChiefFactors_of_odd_normal_quasisimple_quotient
      (⊥ : Subgroup (K ⧸ pCore 2 K)) (by simp)
    exact IsQuasisimple.of_mulEquiv QuotientGroup.quotientBot.symm
  let := hK.perfect
  have hpK : IsPPerfect 2 K := by
    intro N hN hp
    let := hN
    by_contra hne
    let : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsNilpotent (K ⧸ N) := hp.isNilpotent
    exact Group.IsPerfect.not_isSolvable (K ⧸ N) inferInstance
  have hm := reduced_commutator_ne_bot_of_intrinsicModule_ne_bot K hK.subnormal
    hpK hchief hfaith
  apply hK.isComponent_map_of_twoCore_killed hqK (QuotientGroup.mk' C)
    (QuotientGroup.mk'_surjective C)
  · rw [QuotientGroup.ker_mk']
    exact normal_pCore_le_centralizer_reducedPSubgroup 2 K
  · intro he
    have hc : K ≤ C := by
      simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff K).mp he
    exact hm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))

theorem component_reduced_offender_entry
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (K : Subgroup G) [K.Normal] (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K)) (hfaith : intrinsicSignalizerModule K ≠ ⊥)
    (hgen : ⁅K,elementaryAbelianMaxJ (T : Subgroup G)⁆ = K) :
    let W := reducedTwoSubgroup G
    let := (isPReduced_reducedPSubgroup (p := 2) (G := G)).elementary
    let C := centralizer (W : Set G)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let N := offenderSubgroup ρ
    K.map q ≤ N ∧ IsComponent N ((K.map q).subgroupOf N) ∧
      ChapterB.SourceInduction.NontrivialAdequateAlternative (ρ.comp N.subtype) := by
  let W := reducedTwoSubgroup G
  let := (isPReduced_reducedPSubgroup (p := 2) (G := G)).elementary
  let C := centralizer (W : Set G)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let N := offenderSubgroup ρ
  have hKN : K.map q ≤ N := thompson_generated_image_le_offender T K hgen
  have hcomp := (faithful_component_reduced_image K hK hqK hfaith).subgroupOf hKN
  let : Nontrivial ((K.map q).subgroupOf N) :=
    (nontrivial_iff_ne_bot _).mpr hcomp.isCComponent.ne_bot
  let : Nontrivial N := Function.Injective.nontrivial
    (f := ((K.map q).subgroupOf N).subtype) Subtype.val_injective
  have ha := ChapterB.offender_restriction_classification ρ
    ChapterB.SourceInduction.adequateClassification_knownSimple
    (NormalElementaryQuotient.representation_injective W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C))
    (isPReduced_reducedPSubgroup (p := 2) (G := G)).quotient_pCore_eq_bot
    ⟨{ Cover := G, kernel := C, sqtk := hG, equiv := MulEquiv.refl _ }⟩
  exact ⟨hKN,hcomp,ha.of_nontrivial _⟩

omit [Finite G] in
theorem reduced_image_commutator_le
    (J K : Subgroup G) (hKJ : K ≤ J) :
    ⁅(reducedTwoSubgroup J).map J.subtype,K⁆ ≤ (reducedTwoSubgroup J).map J.subtype := by
  have hm := map_mono (f := J.subtype)
    (commutator_le_left (reducedTwoSubgroup J) (K.subgroupOf J))
  rwa [map_commutator,map_subgroupOf_eq_of_le hKJ] at hm

omit [Finite G] in
theorem ambient_reduced_moved_coordinates
    (J K : Subgroup G) (hKJ : K ≤ J) :
    let W := reducedTwoSubgroup J
    letI := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
    let Wg := W.map J.subtype
    letI : IsElementaryAbelian 2 Wg := IsElementaryAbelian.map J.subtype
    let WK := ⁅Wg,K⁆
    letI : IsElementaryAbelian 2 WK := IsElementaryAbelian.of_le (reduced_image_commutator_le J K hKJ)
    let C := centralizer (W : Set J)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∃ e : Additive WK ≃ₗ[ZMod 2] subspaceCommutator ρ ⊤ ((K.subgroupOf J).map q),
      ∀ w, (((e w).val.toMul : J) : G) = (w.toMul : G) := by
  let W := reducedTwoSubgroup J
  let := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
  let Wg := W.map J.subtype
  let : IsElementaryAbelian 2 Wg := IsElementaryAbelian.map J.subtype
  let WK := ⁅Wg,K⁆
  let : IsElementaryAbelian 2 WK := IsElementaryAbelian.of_le (reduced_image_commutator_le J K hKJ)
  let C := centralizer (W : Set J)
  let q := QuotientGroup.mk' C
  let K₀ := K.subgroupOf J
  let A := ⁅W,K₀⁆
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (commutator_le_left W K₀)
  have hm : A.map J.subtype = WK := by
    change (⁅W,K.subgroupOf J⁆).map J.subtype = WK
    rw [map_commutator,map_subgroupOf_eq_of_le hKJ]
  let f : A ≃* WK := (A.equivMapOfInjective J.subtype J.subtype_injective).trans
    (MulEquiv.subgroupCongr hm)
  let e := (f.symm.toAdditive.toLinearEquiv (fun c w =>
    ZMod.map_smul f.symm.toAdditive.toAddMonoidHom c w)).trans
    (NormalElementaryQuotient.movedEquiv W q (QuotientGroup.mk'_surjective C)
      (QuotientGroup.ker_mk' C) K₀)
  refine ⟨e,?_⟩
  intro w
  exact congrArg (fun z : WK => (z : G)) (f.apply_symm_apply w.toMul)

theorem original_component_offender_entry
    {T : Sylow 2 G} {L V P E U M H : Subgroup G}
    (d : Section08.SourceCompletion.NaturalSetup T L V P E U M H)
    (J K : Subgroup G) (hJH : J ≤ H) (hKJ : K ≤ J)
    (hKN : J ≤ normalizer (K : Set G))
    (hK : (K.subgroupOf J).IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hfaith : intrinsicSignalizerModule K ≠ ⊥)
    (hTJ : (T : Subgroup G) ≤ J)
    (hgen : ⁅K,elementaryAbelianMaxJ (T : Subgroup G)⁆ = K) :
    let W := reducedTwoSubgroup J
    letI := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
    let C := centralizer (W : Set J)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let N := offenderSubgroup ρ
    (K.subgroupOf J).map q ≤ N ∧
      IsComponent N (((K.subgroupOf J).map q).subgroupOf N) ∧
      ChapterB.SourceInduction.NontrivialAdequateAlternative (ρ.comp N.subtype) := by
  let K₀ := K.subgroupOf J
  let S : Sylow 2 J := T.subtype hTJ
  let : K₀.Normal := normal_subgroupOf_of_le_normalizer hKN
  let eK : K₀ ≃* K := subgroupOfEquivOfLe hKJ
  have hq₀ : IsQuasisimple (K₀ ⧸ pCore 2 K₀) :=
    IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).symm
  have hfaith₀ : intrinsicSignalizerModule K₀ ≠ ⊥ := by
    intro hz
    apply hfaith
    have hm := intrinsicSignalizerModule_map_of_injective J.subtype J.subtype_injective K₀
    rw [map_subgroupOf_eq_of_le hKJ,hz,Subgroup.map_bot] at hm
    exact hm
  have hjmap : (elementaryAbelianMaxJ (S : Subgroup J)).map J.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le hTJ
  have hgen₀ : ⁅K₀,elementaryAbelianMaxJ (S : Subgroup J)⁆ = K₀ := by
    apply map_injective J.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hKJ,hjmap,hgen]
  have hne : P ≠ ⊥ := by intro he; have hc := d.line_card; simp [he] at hc
  have htwo : IsTwoLocal H := by
    rw [d.first_normalizer]
    exact ⟨P,hne,IsPGroup.of_card (n := 1) (by simpa using d.line_card),rfl⟩
  have hH : IsSQTK KnownSimple.IsKnownSimple H := d.counterexample.qtke.twoLocal_sqtk htwo
  have hJ : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJH)).mp (hH.subgroup (J.subgroupOf H))
  exact component_reduced_offender_entry hJ S K₀ hK hq₀ hfaith₀ hgen₀

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
