module
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.NaturalAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl.OriginalSource.NaturalPointMSChiefBound
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.Marking

/-!
# Baumann control at the original G,T

Mark the original natural action by its point and plane. The characteristic
alternative controls the Baumann normalizer by maximal two-local uniqueness.
Otherwise the checked natural-point MS theorem bounds every chief series of
L₁ by three factors, contradicting the four factors constructed on the same
L₁. This reuses the natural-point classification and its chief-count proof;
only its original ambient structural input is localized.
Source: AS C.1.37, p.143; 14.7.10 and 14.7.67(4), pp.1045,1070.
Final earlier-source discharge remains with qt-d-14775-source.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section03.ThompsonSourceAt
open Chapter12.Section08 Chapter12.Section02 Matrix.PSL3Two
open Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
  (F : InvariantFlag T V 3) (structural : Structural1222At KnownSimple.IsKnownSimple T)

omit [Finite G] in
private theorem stabilizer_iff_normalizer
    (H : Subgroup G) (hn : H ≤ normalizer (V : Set G))
    (e : Model ≃* V) (q : H →* SL)
    (ha : ∀ g v, (e (slAut (q g) v) : G) = (g : G) * (e v : G) * (g : G)⁻¹)
    (A : Subgroup G) (hAV : A ≤ V) (P : Subgroup Model)
    (he : P.map e.toMonoidHom = A.subgroupOf V) (g : H) :
    slAut (q g) ∈ MulAction.stabilizer (MulAut Model) P ↔
      (g : G) ∈ normalizer (A : Set G) := by
  have hm (v : Model) : (e v : G) ∈ A ↔ v ∈ P := by
    change e v ∈ A.subgroupOf V ↔ _
    rw [← he]
    exact mem_map_iff_mem e.injective
  rw [stabilizer_iff, mem_normalizer_iff]
  constructor
  · intro hg x
    constructor
    · intro hx
      obtain ⟨v, hv⟩ := e.surjective ⟨x, hAV hx⟩
      have hev : (e v : G) = x := congrArg Subtype.val hv
      have hh := (hm (slAut (q g) v)).mpr ((hg v).mpr ((hm v).mp (hev ▸ hx)))
      rwa [ha, hev] at hh
    · intro hx
      have hxV : x ∈ V := (mem_normalizer_iff.mp (hn g.property) x).mpr (hAV hx)
      obtain ⟨v, hv⟩ := e.surjective ⟨x, hxV⟩
      have hev : (e v : G) = x := congrArg Subtype.val hv
      apply hev ▸ (hm v).mpr
      apply (hg v).mp
      apply (hm (slAut (q g) v)).mp
      rwa [ha, hev]
  · intro hg v
    rw [← hm, ← hm, ha]
    exact (hg (e v)).symm

include h structural in
theorem exists_marking :
    ∃ (e : Model ≃* V) (q : ↥(L ⊔ (T : Subgroup G)) →* SL),
      Function.Surjective q ∧ IsPGroup 2 q.ker ∧
      (∀ g v, (e (slAut (q g) v) : G) = (g : G) * (e v : G) * (g : G)⁻¹) ∧
      q.ker = (centralizer (V : Set G)).subgroupOf (L ⊔ (T : Subgroup G)) ∧
      ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))).map q = borelSL ∧
      ((F.Ri L 1).subgroupOf (L ⊔ (T : Subgroup G))).map q =
        MarkedAutomorphisms.pointV := by
  let := h.chosen.elementary
  have hc1 : Nat.card ((F.Vi 1).subgroupOf V) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (F.le_seed 1)).toEquiv]
    simpa using F.card 1 (by decide)
  have hc2 : Nat.card ((F.Vi 2).subgroupOf V) = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (F.le_seed 2)).toEquiv]
    simpa using F.card 2 (by decide)
  obtain ⟨e, he1, he2⟩ := coordinates (by simpa using h.seed_card)
    ((F.Vi 1).subgroupOf V) ((F.Vi 2).subgroupOf V) hc1 hc2
    (subgroupOf_mono _ (F.monotone (by decide : 1 ≤ 2)))
  let H := L ⊔ (T : Subgroup G)
  let hn : H ≤ normalizer (V : Set G) :=
    sup_le h.chosen.normalizes (h.sylow_normalizes_seed_at structural)
  let f := setupSeedAction H V hn
  let q : H →* SL := slAut.symm.toMonoidHom.comp ((MulAut.congr e.symm).toMonoidHom.comp f)
  have hq : Function.Surjective q := slAut.symm.surjective.comp
    ((MulAut.congr e.symm).surjective.comp (h.full_LT_action_at structural))
  have hk : q.ker = (centralizer (V : Set G)).subgroupOf H := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _ slAut.symm.injective,
      MonoidHom.ker_comp_of_injective _ _ (MulAut.congr e.symm).injective]
    exact setupSeedAction_ker H V hn
  have hk2 : IsPGroup 2 q.ker := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _ slAut.symm.injective,
      MonoidHom.ker_comp_of_injective _ _ (MulAut.congr e.symm).injective]
    exact h.action_kernel_isPGroup_at structural
  have ha (g : H) (v : Model) :
      (e (slAut (q g) v) : G) = (g : G) * (e v : G) * (g : G)⁻¹ := by
    change (e (slAut (slAut.symm ((MulAut.congr e.symm) (f g))) v) : G) = _
    rw [slAut.apply_symm_apply]
    change (e (e.symm (f g (e v))) : G) = _
    rw [e.apply_symm_apply]
    rfl
  have hp (g : H) : q g ∈ pointParabolicSL ↔ (g : G) ∈ F.Gi 1 := by
    rw [← point_stabilizer]
    exact stabilizer_iff_normalizer H hn e q ha (F.Vi 1) (F.le_seed 1) point he1 g
  have hl (g : H) : q g ∈ lineParabolicSL ↔ (g : G) ∈ F.Gi 2 := by
    rw [← plane_stabilizer]
    exact stabilizer_iff_normalizer H hn e q ha (F.Vi 2) (F.le_seed 2) plane he2 g
  have hT : ((T : Subgroup G).subgroupOf H).map q = borelSL := by
    let S : Sylow 2 H := T.subtype le_sup_right
    let P : Sylow 2 SL := S.mapSurjective (f := q) hq
    have hP : (P : Subgroup SL) ≤ borelSL := by
      rintro x ⟨g, hg, rfl⟩
      exact ⟨(hp g).mpr (F.invariant 1 hg), (hl g).mpr (F.invariant 2 hg)⟩
    exact (P.is_maximal' (IsPGroup.of_card (n := 3) card_borelSL) hP).symm
  let iL : L →* H := inclusion le_sup_left
  have hLq : Function.Surjective (q.comp iL) := by
    intro a
    obtain ⟨l, hl, he⟩ := h.full_L_action (MulAut.congr e (slAut a))
    refine ⟨⟨l, hl⟩, ?_⟩
    apply slAut.injective
    apply MulEquiv.ext
    intro v
    apply e.injective
    apply Subtype.ext
    change (e (slAut (q (iL ⟨l, hl⟩)) v) : G) = _
    rw [ha]
    exact (he (e v)).trans (by
      change (e ((slAut a) (e.symm (e v))) : G) = _
      rw [e.symm_apply_apply])
  have hN : ((L ⊓ F.Gi 1).subgroupOf H).map q = pointParabolicSL := by
    ext a
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hp g).mpr hg.2
    · intro ha
      obtain ⟨l, he⟩ := hLq a
      refine ⟨iL l, ⟨l.property, (hp (iL l)).mp ?_⟩, he⟩
      change q (iL l) = a at he
      exact he ▸ ha
  let N := (L ⊓ F.Gi 1).subgroupOf H
  let D := (pResidual 2 N).map N.subtype
  have hDmap : D.map q = MarkedAutomorphisms.pointA := by
    rw [map_embedded_pResidual, hN]
    exact MarkedAutomorphisms.point_residual
  have hDG : D.map H.subtype = F.Li L 1 := by
    rw [map_embedded_pResidual, map_subgroupOf_eq_of_le
      (inf_le_left.trans le_sup_left)]
    simp only [InvariantFlag.Li, show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide,
      ↓reduceIte]
  have hDL : D = (F.Li L 1).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hDG, map_subgroupOf_eq_of_le ((F.Li_le L 1).trans (inf_le_left.trans le_sup_left))]
  have hjoin : (D ⊔ (T : Subgroup G).subgroupOf H).map q = pointParabolicSL := by
    rw [Subgroup.map_sup, hDmap, hT, ← MarkedAutomorphisms.point_residual]
    exact MarkedProduct.residual_sup_borel
  have hR : ((D ⊔ (T : Subgroup G).subgroupOf H).pCoreIn 2).map q =
      MarkedAutomorphisms.pointV := by
    rw [map_pCoreIn_of_ker_isPGroup q hk2, hjoin,
      MarkedProduct.pointParabolic_core]
  have hRG : ((D ⊔ (T : Subgroup G).subgroupOf H).pCoreIn 2).map H.subtype = F.Ri L 1 := by
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective,
      Subgroup.map_sup, hDG, map_subgroupOf_eq_of_le le_sup_right]
    rfl
  have hRsub : (D ⊔ (T : Subgroup G).subgroupOf H).pCoreIn 2 =
      (F.Ri L 1).subgroupOf H := by
    rw [← hRG]
    exact (comap_map_eq_self_of_injective H.subtype_injective _).symm
  exact ⟨e, q, hq, hk2, ha, hk, hT, hRsub ▸ hR⟩

end CFSG.Quasithin.Chapter14.Section03.ThompsonSourceAt
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G}

/-- The actual source characteristic obstruction gives the normalizer
conclusion of 14.7.10, without a local normalizer-bound premise. -/
theorem baumann_normalizer_le_of_characteristic_normal_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3)
    (C : Subgroup (ChapterB.baumann (F.Ri L 1)))
    (hC : C.Characteristic) (hne : C ≠ ⊥)
    (hn : ((C.map (ChapterB.baumann (F.Ri L 1)).subtype).subgroupOf
      (L ⊔ (T : Subgroup G))).Normal) :
    normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G) := by
  let S := ChapterB.baumann (F.Ri L 1)
  let D := C.map S.subtype
  have hDLT : D ≤ L ⊔ (T : Subgroup G) := by
    apply (map_subtype_le C).trans
    apply (show S ≤ F.Ri L 1 from inf_le_left).trans
    exact (pCoreIn_le 2 _).trans (sup_le_sup ((F.Li_le L 1).trans inf_le_left) le_rfl)
  have hLN : L ⊔ (T : Subgroup G) ≤ normalizer (D : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hDLT).mp hn
  have hN : normalizer (D : Set G) ≤ normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G))
    · intro M hM hLM
      exact Set.mem_singleton_iff.mp ((h.maximal_unique_at structural).2 ▸
        show M ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
          from ⟨hM, hLM⟩)
    · exact (((isPGroup_pCoreIn 2 _).to_le (show S ≤ F.Ri L 1 from inf_le_left)).to_subgroup C).map S.subtype
    · exact fun hz => hne ((C.map_eq_bot_iff_of_injective S.subtype_injective).mp hz)
    · exact hLN
  let := hC
  exact (normalizer_le_normalizer_characteristic_image S C).trans hN

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter12.Section02 ChapterC.NaturalPointControl
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag
namespace ResidualNormalizer.LocalControl.OriginalSourceAt
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}


/-- The actual seed is normal in LT. -/
theorem seed_normal (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    (V.subgroupOf (L ⊔ (T : Subgroup G))).Normal :=
  (normal_subgroupOf_iff_le_normalizer (h.chosen.le_sylow.trans le_sup_right)).mpr
    (sup_le h.chosen.normalizes (h.sylow_normalizes_seed_at structural))

/-- The chosen source seed remains elementary in LT. -/
theorem seed_elementary (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) :
    IsElementaryAbelian 2 (V.subgroupOf (L ⊔ (T : Subgroup G))) := by
  let := h.chosen.elementary
  exact IsElementaryAbelian.subgroupOf (h.chosen.le_sylow.trans le_sup_right)

/-- Construct the marked natural action whose full point-radical preimage is R₁. -/
theorem exists_naturalPointAction (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (F : InvariantFlag T V 3) :
    let := seed_normal h structural
    let := seed_elementary h
    ∃ d : NaturalAction (V.subgroupOf (L ⊔ (T : Subgroup G))),
      d.R = (F.Ri L 1).subgroupOf (L ⊔ (T : Subgroup G)) := by
  let := seed_normal h structural
  let := seed_elementary h
  obtain ⟨e, q, hq, _, ha, hk, _, hR⟩ :=
    Chapter14.Section03.ThompsonSourceAt.exists_marking h F structural
  let H := L ⊔ (T : Subgroup G)
  let E := V.subgroupOf H
  have hVH : V ≤ H := h.chosen.le_sylow.trans le_sup_right
  let a : E ≃* V := subgroupOfEquivOfLe hVH
  let c : E ≃* Model := a.trans e.symm
  have hker : q.ker = pCore 2 H := by
    apply map_injective H.subtype_injective
    rw [hk, subgroupOf_map_subtype, inf_comm]
    exact h.centralizer_LT_at structural
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
theorem residual_eq (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    pResidual 2 (L ⊔ (T : Subgroup G) : Subgroup G) =
      L.subgroupOf (L ⊔ (T : Subgroup G)) := by
  let H := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf H
  let S := (T : Subgroup G).subgroupOf H
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer (h.sylow_normalizes_at structural))
  have hp : IsPPerfect 2 A :=
    ((pResidual_eq_top_iff 2 L).mp h.residual).of_surjective
      (subgroupOfEquivOfLe (show L ≤ H from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show L ≤ H from le_sup_left)).symm.surjective
  apply pResidual_eq_of_isPPerfect_sup A S hp T.isPGroup'.comap_subtype
  rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]

/-- The residual retains the original C-component property. -/
theorem residual_component (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    (pResidual 2 (L ⊔ (T : Subgroup G) : Subgroup G)).IsCComponent := by
  rw [residual_eq h structural]
  exact h.source.maximal_faithful.1.1.1

/-- LT inherits SQTK inside the two-local normalizer of the chosen seed. -/
theorem local_sqtk (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) : IsSQTK KnownSimple.IsKnownSimple (L ⊔ (T : Subgroup G) : Subgroup G) := by
  let := h.chosen.elementary
  have hs := h.source.simpleQTKE.twoLocal_sqtk
    (show IsTwoLocal (normalizer (V : Set G)) from
      ⟨V, h.chosen.ne_bot, IsElementaryAbelian.isPGroup 2 V, rfl⟩)
  let f := inclusion (sup_le h.chosen.normalizes (h.sylow_normalizes_seed_at structural))
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
theorem msGroup_map (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (F : InvariantFlag T V 3)
    (d : NaturalAction (V.subgroupOf (L ⊔ (T : Subgroup G))))
    (hd : d.R = (F.Ri L 1).subgroupOf (L ⊔ (T : Subgroup G))) :
    d.J.map (L ⊔ (T : Subgroup G)).subtype = L ⊔ ChapterB.baumann (F.Ri L 1) := by
  change (pResidual 2 (L ⊔ (T : Subgroup G) : Subgroup G) ⊔ d.B).map _ = _
  rw [Subgroup.map_sup, residual_eq h structural, map_subgroupOf_eq_of_le le_sup_left,
    baumann_map F d hd]

/-- The component in the MS input maps to the original L. -/
theorem msComponent_map (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
theorem normalizer_or_msInput (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) :
    letI := seed_normal h structural
    letI := seed_elementary h
    normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G) ∨
      ∃ d : NaturalAction (V.subgroupOf (L ⊔ (T : Subgroup G))),
        d.R = (F.Ri L 1).subgroupOf (L ⊔ (T : Subgroup G)) ∧
        Nonempty (ChapterC.BinaryMS.Input KnownSimple.IsKnownSimple d.LJ d.BJ) := by
  let := seed_normal h structural
  let := seed_elementary h
  obtain ⟨d, hd⟩ := exists_naturalPointAction h structural F
  rcases d.characteristic_or_msInput (local_sqtk h structural)
    (residual_component h structural) with hc | hm
  · left
    obtain ⟨C, hC, hne, hn⟩ := hc
    have hb := baumann_map F d hd
    obtain ⟨D, hD, hDne, hDn⟩ := characteristic_transport hb C hC hne hn
    exact baumann_normalizer_le_of_characteristic_normal_at h structural F
      D hD hDne hDn
  · exact Or.inr ⟨d, hd, hm⟩

/-- When normalizer control fails, the original source constructs every MS
hypothesis on the same marked action, without a classification assumption. -/
theorem msInput_of_normalizer_escape (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3)
    (escape : ¬ normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤
      normalizer (L : Set G)) :
    letI := seed_normal h structural
    letI := seed_elementary h
    ∃ d : NaturalAction (V.subgroupOf (L ⊔ (T : Subgroup G))),
      d.R = (F.Ri L 1).subgroupOf (L ⊔ (T : Subgroup G)) ∧
      Nonempty (ChapterC.BinaryMS.Input KnownSimple.IsKnownSimple d.LJ d.BJ) :=
  (normalizer_or_msInput h structural F).resolve_left escape

end ResidualNormalizer.LocalControl.OriginalSourceAt
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 ChapterC.NaturalPointControl
namespace ResidualNormalizer.LocalControl.OriginalSourceAt
open NoncentralChiefRefinement
open ResidualNormalizer.LocalControl.OriginalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}


/-- Apply cubic movement to the actual L₁ inclusion into L Baum(R₁).
The natural-point theorem supplies its small commutator core. -/
theorem chief_count_le_of_naturalPointMS (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) :
    letI := seed_normal h structural
    letI := seed_elementary h
    ∀ a : NaturalAction (V.subgroupOf (L ⊔ (T : Subgroup G))),
      ChapterC.BinaryMS.Input KnownSimple.IsKnownSimple a.LJ a.BJ →
      ∀ s : ChiefSeries (F.Li L 1), s.head = ⊥ → s.last = ⊤ →
        s.noncentralTwoCount ≤ 3 := by
  let := seed_normal h structural
  let := seed_elementary h
  intro a input s h0 h1
  let : IsElementaryAbelian 2 ((V.subgroupOf (L ⊔ (T : Subgroup G))).subgroupOf a.J) :=
    IsElementaryAbelian.subgroupOf a.module_le_J
  obtain ⟨e,he⟩ := natural_or_double_of_msInput a input
  have hc := NaturalAction.core_card_le_of_models input e he
  have hLiL : F.Li L 1 ≤ L := (F.Li_le L 1).trans inf_le_left
  have hmem (l : F.Li L 1) :
      (⟨l,hLiL.trans le_sup_left l.property⟩ : ↥(L ⊔ (T : Subgroup G))) ∈
        pResidual 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
    rw [residual_eq h structural]
    exact hLiL l.property
  let f : F.Li L 1 →* a.J := {
    toFun := fun l => ⟨⟨l,hLiL.trans le_sup_left l.property⟩,
      (show pResidual 2 (L ⊔ (T : Subgroup G) : Subgroup G) ≤ a.J
        from le_sup_left) (hmem l)⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y heq
    exact Subtype.ext (congrArg (fun z : a.J => ((z : ↥(L ⊔ (T : Subgroup G))) : G)) heq)
  have hfL : f.range ≤ a.LJ := by
    rintro _ ⟨l,rfl⟩
    exact hmem l
  exact a.inMSGroup.chief_count_le_three input hc f hf hfL
    (pointResidual_quotient_card h F) s h0 h1

/-- The full source alternative, with only the earlier structural and
uniqueness inputs. -/
theorem chief_bound_or_baumann_normalizer_of_naturalPointMS (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) :
    (∀ s : ChiefSeries (F.Li L 1), s.head = ⊥ → s.last = ⊤ →
      s.noncentralTwoCount ≤ 3) ∨
    normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G) := by
  let := seed_normal h structural
  let := seed_elementary h
  rcases normalizer_or_msInput h structural F with hn | ⟨a,_,⟨hi⟩⟩
  · exact Or.inr hn
  · exact Or.inl (chief_count_le_of_naturalPointMS h structural F a hi)


end ResidualNormalizer.LocalControl.OriginalSourceAt
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
open Subgroup Chapter12.Section08 Chapter13.Section03.SourceCompletion
open ResidualNormalizer.LocalControl.OriginalSourceAt
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
include d
/-- Apply the natural-point alternative to the literal original residual. -/
theorem baumann_normalizer_from_original_modules_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (five : OriginalAlternatingFiveModules1332At T L) :
    normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G) := by
  rcases chief_bound_or_baumann_normalizer_of_naturalPointMS d.natural structural F with hb | hn
  · obtain ⟨s,h0,h1,hs⟩ := d.exists_residual_four_chief_factors_at structural five
    have := hb s h0 h1
    omega
  · exact hn
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
