module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedPlacement
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.LinearNormalizer
public import Theory.Representation.BinaryRadicalFlag.PositiveRank

/-!
# The literal radical normalizer in the constrained binary five-space

The original residual lies in the selected component. Its actual star image
normalizes the original radical intersection and is normal in that intersection's
full normalizer, because C.2.7 places the normalizer in the original marked
intersection. The solvable star kernel preserves the factor 168 from LH/O2(LH).
Consequently the canonical fixed filtration gives a positive-rank proper
partial flag for this literal normalizer in SL5(2).

This identifies the radical normalizer, not yet the whole marked intersection
or its residual. The final fixed-space module calculation remains separate.
Source: Aschbacher--Smith C.2.7 and C.4.5--8, pp.145--147,152--154.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Chapter4.Section04.NormalizedRankOneOddControl
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original SL5 star has an actual positive-rank radical-normalizer flag,
with the original perfect residual image normal there and retaining order 168. -/
theorem sourceOrbit_binary_witness_constrained_five_flag
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃* SL(5,ZMod 2)) :
    let Kg := K.map H.subtype
    let R := J.pCoreIn 2
    let C := starImage Kg R Kg
    let P := (starImage Kg R R).subgroupOf C
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let B := (LH.subgroupOf Kg).map (toStarImage Kg R)
    IsPRadical 2 P ∧
      normalizer (P : Set C) ≤ (starM Kg R (H ⊓ normalizer (L : Set G))).subgroupOf C ∧
      B ≤ normalizer (P : Set C) ∧
      (B.subgroupOf (normalizer (P : Set C))).Normal ∧
      Group.IsPerfect B ∧ 168 ∣ Nat.card B ∧
      ∃ (k : ℕ) (W : Fin k → Submodule (ZMod 2) (Fin 5 → ZMod 2)),
        0 < k ∧ k ≤ 3 ∧ StrictMono W ∧
        (∀ i, W i ≠ ⊥ ∧ W i ≠ ⊤) ∧
        (normalizer (P : Set C)).map e.toMonoidHom =
          ⨅ i, Matrix.HigherLinear.parabolicSL (W i) := by
  let Kg := K.map H.subtype
  let R := J.pCoreIn 2
  let C := starImage Kg R Kg
  let M := H ⊓ normalizer (L : Set G)
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let P := (starImage Kg R R).subgroupOf C
  let B := (LH.subgroupOf Kg).map (toStarImage Kg R)
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  have hspan := hc.normalized_span_eq hn
  have hi := hc.constrained_source_input K hK hq hout hfK
  obtain ⟨hKn,hLK⟩ := D.sourceOrbit_binary_witness_constrained_linear_placement
    h hd F hF hmodel hw hWJ hJC K hK hq hout hfK (Or.inr ⟨e⟩)
  let := hKn
  have hLKg : LH ≤ Kg := by
    intro x hx
    exact ⟨⟨x,hc.component_le.trans hc.local_le hx⟩,hLK hx,rfl⟩
  let : Group.IsPerfect LH := by
    have hh := hc.span_perfect
    rwa [hspan] at hh
  let : Group.IsPerfect (LH.subgroupOf Kg) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLKg).symm.toMonoidHom)
    (subgroupOfEquivOfLe hLKg).symm.surjective
  let : Group.IsPerfect B := Group.IsPerfect.map _
  have hlarge : 40320 < Nat.card C := by
    rw [Nat.card_congr (e.trans ((BinaryLinear.OuterCyclic.slEquivLinear 5).trans
      (BinaryLinear.OuterCyclic.matrixEquivLinear 5).symm)).toEquiv, Matrix.card_GL_field]
    decide
  obtain ⟨hP,hPM⟩ := ChapterC.C27Source.star_intersection_placement_from_source_of_large_order hi hlarge
  let : (Kg.subgroupOf (Kg ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le Kg.le_normalizer hi.normalizes)
  have hPimage : (R.subgroupOf Kg).map (toStarImage Kg R) = P :=
    ChapterC.C27Source.component_intersection_star_eq_of_normal_input
      (ChapterC.C27Source.source_join_input hi)
  have hLR : LH ≤ normalizer (R : Set G) := by
    simpa only [hspan] using hc.span_normalizes_radical
  have hBP : B ≤ normalizer (P : Set C) := by
    rw [←hPimage]
    apply (map_mono (show LH.subgroupOf Kg ≤ normalizer (R.subgroupOf Kg : Set Kg) from ?_)).trans
      ((R.subgroupOf Kg).le_normalizer_map (toStarImage Kg R))
    intro x hx r
    exact hLR hx (r : G)
  have hNB : normalizer (P : Set C) ≤ normalizer (B : Set C) := by
    intro z hz
    obtain ⟨x,hx,hxz⟩ := hPM hz
    let xk : Kg := ⟨x,hx.2⟩
    have hxe : toStarImage Kg R xk = z := Subtype.ext hxz
    rw [←hxe]
    apply (LH.subgroupOf Kg).le_normalizer_map (toStarImage Kg R)
    refine ⟨xk,?_,rfl⟩
    intro l
    exact hn hx.1 (l : G)
  let : (B.subgroupOf (normalizer (P : Set C))).Normal :=
    normal_subgroupOf_of_le_normalizer hNB
  let f : LH →* C := (toStarImage Kg R).comp (inclusion hLKg)
  have hfr : f.range = B := by
    ext z
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨inclusion hLKg x,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  let j : f.ker →* (toStarImage Kg R).ker :=
    ((inclusion hLKg).comp f.ker.subtype).codRestrict _ (fun x => x.property)
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : (toStarImage Kg R).ker => ((z : Kg) : G)) he))
  let : Group.IsSolvable (toStarImage Kg R).ker := ChapterC.C27Source.toStarImage_ker_solvable_from_source hi
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective hj
  let : Group.IsSolvable f.rangeRestrict.ker := (MonoidHom.ker_rangeRestrict f).symm ▸ inferInstance
  obtain ⟨_,_,_,_,_,_,a,_⟩ := D.sourceOrbit_binary_witness_coordinates h hd F hF hmodel hw
  let q := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 LH))
  have hqsur : Function.Surjective q := a.surjective.comp (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup BinaryLinearThree.Group := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : Group.IsPerfect BinaryLinearThree.Group := Atlas.sl_perfect 3 (by decide)
  have h168 : 168 ∣ Nat.card B := by
    have hh := SimpleSection.card_dvd_of_solvable_representation
      (Group.IsPerfect.not_isSolvable BinaryLinearThree.Group) q hqsur f.rangeRestrict
    rwa [Matrix.PSL3Two.card_SL,hfr] at hh
  have hnot : ¬ IsPGroup 2 (normalizer (P.map e.toMonoidHom : Set SL(5,ZMod 2))) := by
    intro hp
    rw [←map_equiv_normalizer_eq] at hp
    obtain ⟨n,hnc⟩ := hp.exists_card_eq
    have hdvd := (by decide : 7 ∣ 168).trans (h168.trans (card_dvd_of_le hBP))
    have hm : Nat.card ((normalizer (P : Set C)).map e.toMonoidHom) =
        Nat.card (normalizer (P : Set C)) := card_map_of_injective e.injective
    rw [←hm,hnc] at hdvd
    have hh := (by decide : Nat.Prime 7).dvd_of_dvd_pow hdvd
    norm_num at hh
  have hρ : Function.Injective (specialLinearNatural (k := ZMod 2) 5) := by
    intro g j hg
    apply Matrix.SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    exact LinearMap.congr_fun hg
  obtain ⟨k,W,hk,hk3,hm,hW,hflag⟩ := BinaryRadical.exists_positiveRank_flag_normalizer
    (specialLinearNatural (k := ZMod 2) 5) hρ (P.map e.toMonoidHom) (hP.map_equiv e) hnot
  refine ⟨hP,hPM,hBP,inferInstance,inferInstance,h168,k,W,hk,?_,hm,hW,?_⟩
  · simpa using hk3
  · rw [map_equiv_normalizer_eq]
    exact hflag

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
