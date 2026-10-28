module
public import CFSG.Quasithin.Chapter14.Section03.Prelim.ThompsonSource.Marking
import all CFSG.Quasithin.Chapter14.Section03.Prelim.ThompsonSource.Marking
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.NaturalAt

/-!
# The original natural flag marking at the same G,T

Replay the actual point/plane basis and quotient marking using only the
structural predecessor at the original Sylow. The action kernel, Sylow image
and original point radical are unchanged. Source: 14.3.9, pp.992–993.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section03.ThompsonSource
open Chapter12.Section08 Chapter12.Section02 Matrix.PSL3Two
open Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
  (F : InvariantFlag T V 3) (structural : Structural1222At KnownSimple.IsKnownSimple T)

include h structural in
theorem exists_marking_at :
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

end CFSG.Quasithin.Chapter14.Section03.ThompsonSource
