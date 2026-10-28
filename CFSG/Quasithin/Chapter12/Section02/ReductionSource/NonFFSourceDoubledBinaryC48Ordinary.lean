module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48Native
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpOrdinary
public import Theory.Representation.BinaryNaturalDual.FirstCohomology

/-!
# Central quotients of the original doubled-binary ordinary component

The original intersection residual acts on the whole six-dimensional orbit
as the natural module plus its dual. Its fixed subgroup is therefore trivial.
Consequently the whole orbit embeds in every containing ordinary component
modulo its full center, giving two-rank at least six. The same central quotient
retains the literal residual's SL₃(2) section and its two-group kernel.

These two facts exclude all odd, alternating, small sporadic, binary-linear-two,
Suzuki and binary-linear-four rows in the ordinary C.4.8 branch. The remaining
ordinary families and the constrained parabolic module calculation remain
separate obligations. No center-free component or abstract replacement orbit
is assumed.

Source: Aschbacher--Smith C.3.2--5 and C.4.8, printed pp.149--154,
applied to the original Chapter 12 non-FF doubled orbit.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open Chapter4.Section04.NormalizedRankOneOddControl
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original covering residual has no fixed point on the complete
natural-plus-dual orbit, independently of any classification of its overgroup. -/
theorem sourceOrbit_binary_witness_fixed_eq_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    D.sourceOrbit ⊓ centralizer (LH : Set G) = ⊥ := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  obtain ⟨_,_,_,_,_,_,e,_,E,hE,_,_⟩ :=
    D.sourceOrbit_binary_witness_coordinates h hd F hF hmodel hw
  apply bot_unique
  intro x hx
  let v : Additive D.sourceOrbit := Additive.ofMul ⟨x,hx.1⟩
  have hv : E v ∈ OneCohomology.fixed
      (BinaryNaturalDual.naturalDualRepresentation
        (V := BinaryLinear.OuterCyclic.Space 3)) := by
    intro g
    obtain ⟨k,rfl⟩ := (BinaryLinear.OuterCyclic.slEquivLinear 3).surjective g
    obtain ⟨l,hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 LH))) k
    rw [BinaryLinearThree.NaturalDual.naturalDualRepresentation_slEquivLinear,←hl]
    change BinaryLinearThree.NaturalDual.action (e (QuotientGroup.mk' (pCore 2 LH) l))
      (E v) = E v
    rw [←hE]
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G) * x * (l : G)⁻¹ = x
    exact mul_inv_eq_iff_eq_mul.mpr (hx.2 l l.property)
  have hz : E v = 0 := by
    simpa only [BinaryNaturalDual.naturalDual_fixed_eq_bot (by decide : 2 ≤ 3),
      Submodule.mem_bot] using hv
  have hv0 : v = 0 := E.map_eq_zero_iff.mp hz
  exact congrArg (fun z : Additive D.sourceOrbit => (z.toMul : G)) hv0

/-- The actual ordinary component's full central quotient has rank six and
retains the original intersection residual as a binary-three section. -/
theorem sourceOrbit_binary_witness_ordinary_quotient
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : IsComponent H K) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    6 ≤ primeRank 2 (K ⧸ center K) ∧
      ∃ j : LH →* K ⧸ center K, IsPGroup 2 j.ker ∧
        ∃ f : j.range →* BinaryLinearThree.Group, Function.Surjective f := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  have hLH : LH ≤ H := hc.component_le.trans hc.local_le
  have hLK : LH ≤ K.map H.subtype := by
    intro l hl
    exact ⟨⟨l,hLH hl⟩,hc.ordinary_component_contains_original K hK hl,rfl⟩
  have hWL : D.sourceOrbit ≤ LH := by
    have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
      hw.2.2.2.2.2.2.2.2.1
    have he : conjugateSpanBy LH (H ⊓ normalizer (L : Set G)) = LH :=
      le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy _ _)
    exact he ▸ hc.module_le
  let a : K.map H.subtype ≃* K := (K.equivMapOfInjective H.subtype H.subtype_injective).symm
  let z := QuotientGroup.congr (center (K.map H.subtype)) (center K) a
    (FixedElementary.map_center a)
  have hr : primeRank 2 D.sourceOrbit ≤ primeRank 2 (K ⧸ center K) := by
    rw [←primeRank_congr 2 z]
    exact rank_le_central_quotient_of_fixed_eq_bot hLK hWL
      (D.sourceOrbit_binary_witness_fixed_eq_bot h hd F hF hmodel hw)
  have hcard : Nat.card D.sourceOrbit = 2^6 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.sourceOrbit)
    rw [Nat.card_congr Additive.toMul,Nat.card_zmod,
      D.sourceOrbit_binary_dimension h hd F hF hmodel] at hh
    exact hh
  have hrank := IsElementaryAbelian.log_card_eq_primeRank (p := 2) D.sourceOrbit
  rw [hcard,Nat.log_pow (by decide : 1 < (2 : ℕ))] at hrank
  refine ⟨hrank ▸ hr,?_⟩
  obtain ⟨_,_,_,_,_,_,e,_,_⟩ := D.sourceOrbit_binary_witness_coordinates h hd F hF hmodel hw
  let i : LH →* K := a.toMonoidHom.comp (inclusion hLK)
  have hi : Function.Injective i := a.injective.comp (inclusion_injective hLK)
  let j := (QuotientGroup.mk' (center K)).comp i
  have hk := DoubledBinaryOddPlacement.central_kernel_le_twoCore e i hi
  let b := QuotientGroup.quotientKerEquivRange j
  let f : j.range →* BinaryLinearThree.Group := e.toMonoidHom.comp
    ((QuotientGroup.map j.ker (pCore 2 LH) (MonoidHom.id LH) hk).comp b.symm.toMonoidHom)
  refine ⟨j,pCore_isPGroup.to_le hk,f,?_⟩
  intro g
  obtain ⟨l,hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 LH))) g
  refine ⟨j.rangeRestrict l,?_⟩
  have hb : b.symm (j.rangeRestrict l) = QuotientGroup.mk' j.ker l :=
    b.injective (by rw [b.apply_symm_apply]; rfl)
  change e (QuotientGroup.map j.ker (pCore 2 LH) (MonoidHom.id LH) hk
    (b.symm (j.rangeRestrict l))) = g
  rw [hb]
  exact hl

/-- Original C.4.8 ordinary components satisfy the reduced model list, with
all odd rows excluded by the full orbit and the binary rank-one rows excluded
by the actual residual section. No model or quotient-marking premise is added. -/
theorem sourceOrbit_binary_witness_ordinary_remaining_models
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : IsComponent H K) :
    ¬ ChapterA.Section02.IsTheoremBOddModel (K ⧸ center K) ∧
      DoubledBinaryPlacedModels.RemainingPlacedModel (K ⧸ center K) := by
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  obtain ⟨hr,j,_,f,hf⟩ :=
    D.sourceOrbit_binary_witness_ordinary_quotient h hd F hF hmodel hw hWJ hJC K hK
  let := hK.2
  have hb := ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple
    (hc.sqtk.subgroup K).stronglyQuasithin.quasithin (hc.sqtk.isKGroup.subgroup K)
  exact ⟨DoubledBinaryOddRanks.no_odd_model_of_rank_six hr,
    DoubledBinaryPlacedModels.remaining_placed_models hr hb ⟨j.range,f,hf⟩⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
