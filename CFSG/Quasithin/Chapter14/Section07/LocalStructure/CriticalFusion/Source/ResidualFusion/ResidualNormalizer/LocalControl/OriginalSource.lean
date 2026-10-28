module

public import CFSG.Quasithin.Chapter14.Section03.Prelim.ThompsonSource.Marking
public import CFSG.Quasithin.ChapterC.Section01.NaturalPointControl.MSReduction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl.BaumannSource
public import Theory.GroupTheory.PCoreOvergroup
public import Stellmacher.BaumannMap

/-!
# The original natural-point reduction for 14.7.10

The flag marking of the original action on V identifies C_LT(V) with O₂(LT).
Since this kernel lies in R₁, the full inverse image of the marked point
radical is precisely R₁. This constructs the literal input to the natural-point
Baumann argument, including its conjugation action, rather than choosing an
unrelated isomorphic group.

The two-residual of LT is the original L. The natural-point MS reduction thus
produces a genuine binary MS input in L Baum(R₁), unless a nontrivial
characteristic subgroup of Baum(R₁) is normal in LT. The latter alternative
implies the source normalizer bound by uniqueness. Explicit inclusion formulas
identify the group, component and radical of the MS input with these original
ambient subgroups.

This is the reduction to C.1.34, not its classification or the chief-factor
bound. Task qt-d-14710-baumann retains those deductions and the universal
Earlier14710 assembly; qt-rank-two-ms93 owns the independent C.1.34 classifier.
Structural1222 is the earlier input owned by qt-d-1222-source. The actual
Rudvalis application, with uniqueness supplied by known-simple A/C, is in
SourceEndgame/SourceAssembly/OriginalInputs/LocalAlternatives/OriginalBaumann.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), Lemma 14.7.10,
printed p.1045, and the natural-point case of C.1.37, pp.141--143.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter12.Section02 ChapterC.NaturalPointControl
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag
namespace ResidualNormalizer.LocalControl.OriginalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {κ : GroupClass.{u}}

/-- The actual seed is normal in LT. -/
theorem seed_normal (h : HigherRankHypothesis κ T L V 3)
    (structural : Structural1222 κ) :
    (V.subgroupOf (L ⊔ (T : Subgroup G))).Normal :=
  (normal_subgroupOf_iff_le_normalizer (h.chosen.le_sylow.trans le_sup_right)).mpr
    (sup_le h.chosen.normalizes (h.sylow_normalizes_seed structural))

/-- The chosen source seed remains elementary in LT. -/
theorem seed_elementary (h : HigherRankHypothesis κ T L V 3) :
    IsElementaryAbelian 2 (V.subgroupOf (L ⊔ (T : Subgroup G))) := by
  let := h.chosen.elementary
  exact IsElementaryAbelian.subgroupOf (h.chosen.le_sylow.trans le_sup_right)

/-- Construct the marked natural action whose full point-radical preimage is R₁. -/
theorem exists_naturalPointAction (h : HigherRankHypothesis κ T L V 3)
    (structural : Structural1222 κ) (F : InvariantFlag T V 3) :
    let := seed_normal h structural
    let := seed_elementary h
    ∃ d : NaturalAction (V.subgroupOf (L ⊔ (T : Subgroup G))),
      d.R = (F.Ri L 1).subgroupOf (L ⊔ (T : Subgroup G)) := by
  let := seed_normal h structural
  let := seed_elementary h
  obtain ⟨e, q, hq, _, ha, hk, _, hR⟩ :=
    Chapter14.Section03.ThompsonSource.exists_marking h F structural
  let H := L ⊔ (T : Subgroup G)
  let E := V.subgroupOf H
  have hVH : V ≤ H := h.chosen.le_sylow.trans le_sup_right
  let a : E ≃* V := subgroupOfEquivOfLe hVH
  let c : E ≃* Model := a.trans e.symm
  have hker : q.ker = pCore 2 H := by
    apply map_injective H.subtype_injective
    rw [hk, subgroupOf_map_subtype, inf_comm]
    exact h.centralizer_LT structural
  let d : NaturalAction E := {
    q := q
    onto := hq
    kernel := hker
    coordinates := c
    action := by
      intro g v
      have hc : c (MulAut.conjNormal g v) = slAut (q g) (c v) := by
        apply e.injective
        apply Subtype.ext
        rw [ha]
        simp only [c, MulEquiv.trans_apply, e.apply_symm_apply]
        rfl
      exact (congrArg Multiplicative.toAdd hc).trans (slAut_apply _ _) }
  refine ⟨d, ?_⟩
  change MarkedAutomorphisms.pointV.comap q = (F.Ri L 1).subgroupOf H
  rw [← hR, comap_map_eq_self]
  rw [hker]
  let P := (F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf H
  have hPH : F.Li L 1 ⊔ (T : Subgroup G) ≤ H :=
    sup_le_sup ((F.Li_le L 1).trans inf_le_left) le_rfl
  have hPC : P.pCoreIn 2 = (F.Ri L 1).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hPH]
    exact (map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans hPH)).symm
  rw [← hPC]
  exact pCore_le_map_of_sylow_le (T.subtype le_sup_right) P
    (subgroupOf_mono H le_sup_right)


/-- The source component is exactly the two-residual of LT. -/
theorem residual_eq (h : HigherRankHypothesis κ T L V 3)
    (structural : Structural1222 κ) :
    pResidual 2 (L ⊔ (T : Subgroup G) : Subgroup G) =
      L.subgroupOf (L ⊔ (T : Subgroup G)) := by
  let H := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf H
  let S := (T : Subgroup G).subgroupOf H
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer (h.sylow_normalizes structural))
  have hp : IsPPerfect 2 A :=
    ((pResidual_eq_top_iff 2 L).mp h.residual).of_surjective
      (subgroupOfEquivOfLe (show L ≤ H from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show L ≤ H from le_sup_left)).symm.surjective
  apply pResidual_eq_of_isPPerfect_sup A S hp T.isPGroup'.comap_subtype
  rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]

/-- The residual retains the original C-component property. -/
theorem residual_component (h : HigherRankHypothesis κ T L V 3)
    (structural : Structural1222 κ) :
    (pResidual 2 (L ⊔ (T : Subgroup G) : Subgroup G)).IsCComponent := by
  rw [residual_eq h structural]
  exact h.source.maximal_faithful.1.1.1

/-- LT inherits SQTK inside the two-local normalizer of the chosen seed. -/
theorem local_sqtk (h : HigherRankHypothesis κ T L V 3)
    (structural : Structural1222 κ) : IsSQTK κ (L ⊔ (T : Subgroup G) : Subgroup G) := by
  let := h.chosen.elementary
  have hs := h.source.simpleQTKE.twoLocal_sqtk
    (show IsTwoLocal (normalizer (V : Set G)) from
      ⟨V, h.chosen.ne_bot, IsElementaryAbelian.isPGroup 2 V, rfl⟩)
  let f := inclusion (sup_le h.chosen.normalizes (h.sylow_normalizes_seed structural))
  exact ⟨hs.1.of_injective f (inclusion_injective _),
    hs.2.of_injective f (inclusion_injective _)⟩


section Maps
variable [(V.subgroupOf (L ⊔ (T : Subgroup G))).Normal]

omit [Finite G] in
/-- The native Baumann subgroup is the original ambient one under inclusion. -/
theorem baumann_map (F : InvariantFlag T V 3)
    (d : NaturalAction (V.subgroupOf (L ⊔ (T : Subgroup G))))
    (hd : d.R = (F.Ri L 1).subgroupOf (L ⊔ (T : Subgroup G))) :
    d.B.map (L ⊔ (T : Subgroup G)).subtype = ChapterB.baumann (F.Ri L 1) := by
  have hRH : F.Ri L 1 ≤ L ⊔ (T : Subgroup G) :=
    (pCoreIn_le 2 _).trans (sup_le_sup ((F.Li_le L 1).trans inf_le_left) le_rfl)
  change (ChapterB.baumann d.R).map _ = _
  simp only [ChapterB.baumann, ChapterB.thompsonAlpha]
  rw [Stellmacher.baumann_map_injective _ (L ⊔ (T : Subgroup G)).subtype_injective,
    hd, map_subgroupOf_eq_of_le hRH]

/-- The MS group is literally L Baum(R₁), embedded in the original LT. -/
theorem msGroup_map (h : HigherRankHypothesis κ T L V 3)
    (structural : Structural1222 κ) (F : InvariantFlag T V 3)
    (d : NaturalAction (V.subgroupOf (L ⊔ (T : Subgroup G))))
    (hd : d.R = (F.Ri L 1).subgroupOf (L ⊔ (T : Subgroup G))) :
    d.J.map (L ⊔ (T : Subgroup G)).subtype = L ⊔ ChapterB.baumann (F.Ri L 1) := by
  change (pResidual 2 (L ⊔ (T : Subgroup G) : Subgroup G) ⊔ d.B).map _ = _
  rw [Subgroup.map_sup, residual_eq h structural, map_subgroupOf_eq_of_le le_sup_left,
    baumann_map F d hd]

/-- The component in the MS input maps to the original L. -/
theorem msComponent_map (h : HigherRankHypothesis κ T L V 3)
    (structural : Structural1222 κ)
    (d : NaturalAction (V.subgroupOf (L ⊔ (T : Subgroup G)))) :
    (d.LJ.map d.J.subtype).map (L ⊔ (T : Subgroup G)).subtype = L := by
  rw [map_subgroupOf_eq_of_le (show pResidual 2 (L ⊔ (T : Subgroup G) : Subgroup G) ≤
    d.J from le_sup_left), residual_eq h structural, map_subgroupOf_eq_of_le le_sup_left]

omit [Finite G] in
/-- The radical in the MS input maps to the original Baum(R₁). -/
theorem msRadical_map (F : InvariantFlag T V 3)
    (d : NaturalAction (V.subgroupOf (L ⊔ (T : Subgroup G))))
    (hd : d.R = (F.Ri L 1).subgroupOf (L ⊔ (T : Subgroup G))) :
    (d.BJ.map d.J.subtype).map (L ⊔ (T : Subgroup G)).subtype =
      ChapterB.baumann (F.Ri L 1) := by
  rw [map_subgroupOf_eq_of_le (show d.B ≤ d.J from le_sup_right)]
  exact baumann_map F d hd

end Maps

private theorem characteristic_map_equiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (C : Subgroup X) (hC : C.Characteristic) :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y, hy, rfl⟩ := hx
  let b : MulAut X := e.trans (a.trans e.symm)
  refine ⟨b y, (characteristic_iff_le_comap.mp hC b) hy, ?_⟩
  exact e.apply_symm_apply _

omit [Finite G] in
private theorem characteristic_transport {H : Subgroup G} {B : Subgroup H}
    {S : Subgroup G} (he : B.map H.subtype = S)
    (C : Subgroup B) (hc : C.Characteristic) (hne : C ≠ ⊥)
    (hn : (C.map B.subtype).Normal) :
    ∃ D : Subgroup S, D.Characteristic ∧ D ≠ ⊥ ∧
      ((D.map S.subtype).subgroupOf H).Normal := by
  let e : B ≃* S := (B.equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr he)
  let D := C.map e.toMonoidHom
  refine ⟨D, characteristic_map_equiv e C hc,
    fun hz => hne ((C.map_eq_bot_iff_of_injective e.injective).mp hz), ?_⟩
  have hm : D.map S.subtype = (C.map B.subtype).map H.subtype := by
    rw [map_map, map_map]
    rfl
  rw [hm]
  change (((C.map B.subtype).map H.subtype).comap H.subtype).Normal
  rw [comap_map_eq_self_of_injective H.subtype_injective]
  exact hn

/-- The characteristic branch gives the source normalizer bound; otherwise
all hypotheses of the binary MS theorem hold on the original local groups. -/
theorem normalizer_or_msInput (h : HigherRankHypothesis κ T L V 3)
    (structural : Structural1222 κ) (uniqueness : Uniqueness127 κ)
    (F : InvariantFlag T V 3) :
    letI := seed_normal h structural
    letI := seed_elementary h
    normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G) ∨
      ∃ d : NaturalAction (V.subgroupOf (L ⊔ (T : Subgroup G))),
        d.R = (F.Ri L 1).subgroupOf (L ⊔ (T : Subgroup G)) ∧
        Nonempty (ChapterC.BinaryMS.Input κ d.LJ d.BJ) := by
  let := seed_normal h structural
  let := seed_elementary h
  obtain ⟨d, hd⟩ := exists_naturalPointAction h structural F
  rcases d.characteristic_or_msInput (local_sqtk h structural)
    (residual_component h structural) with hc | hm
  · left
    obtain ⟨C, hC, hne, hn⟩ := hc
    have hb := baumann_map F d hd
    obtain ⟨D, hD, hDne, hDn⟩ := characteristic_transport hb C hC hne hn
    exact baumann_normalizer_le_of_characteristic_normal h structural uniqueness F
      D hD hDne hDn
  · exact Or.inr ⟨d, hd, hm⟩

/-- When normalizer control fails, the original source constructs every MS
hypothesis on the same marked action, without a classification assumption. -/
theorem msInput_of_normalizer_escape (h : HigherRankHypothesis κ T L V 3)
    (structural : Structural1222 κ) (uniqueness : Uniqueness127 κ)
    (F : InvariantFlag T V 3)
    (escape : ¬ normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤
      normalizer (L : Set G)) :
    letI := seed_normal h structural
    letI := seed_elementary h
    ∃ d : NaturalAction (V.subgroupOf (L ⊔ (T : Subgroup G))),
      d.R = (F.Ri L 1).subgroupOf (L ⊔ (T : Subgroup G)) ∧
      Nonempty (ChapterC.BinaryMS.Input κ d.LJ d.BJ) :=
  (normalizer_or_msInput h structural uniqueness F).resolve_left escape

end ResidualNormalizer.LocalControl.OriginalSource
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
