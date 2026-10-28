module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.Actor
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.Faithful
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# Selected source actors and the moving faithful residual

This combines the genuine supercritical selection with the actual binary-
tetrahedral action and its Sylow restriction. T is the original ambient
Sylow. Its normalization of L₊ constructs a full Sylow of L₊ on the exact
carrier T∩L₊; the resulting image, not the full ambient T-image, is Q₈.
The selected residual is the literal O²-preimage in H and has nontrivial
intrinsic signalizer module by A.4.8.

Source: Aschbacher–Smith 13.3.14(d), printed p.892. Two-perfectness and the
cubic quotient of the original L₊ are earlier parabolic inputs; the rank-one
centralizing-residual bound is reduction (b). No selected subgroup, actor
model, movement conclusion, or faithful signalizer premise is assumed.
-/

public section
open Subgroup

namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource

variable {G : Type*} [Group G] [Finite G]

private theorem sylow_intersection (T : Sylow 2 G) (L : Subgroup G)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ S : Sylow 2 L, (S : Subgroup L) = (T : Subgroup G).subgroupOf L := by
  let W := L ⊔ (T : Subgroup G)
  have hLW : L ≤ W := le_sup_left
  let : (L.subgroupOf W).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLW).mpr (sup_le L.le_normalizer hTL)
  obtain ⟨S, hS⟩ := (T.subtype (show (T : Subgroup G) ≤ W from le_sup_right)).exists_subgroupOf_eq_of_normal (L.subgroupOf W)
  let e := subgroupOfEquivOfLe hLW
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (S : Subgroup _).map e.toMonoidHom = _
  rw [hS]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro hx; exact ⟨⟨⟨x, hLW x.property⟩, x.property⟩, hx, rfl⟩

theorem source_selected_actors
    (T : Sylow 2 G) (H Lplus U : Subgroup G)
    (hH : H ∈ Chapter1.He G) (hLH : Lplus ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (Lplus : Set G))
    (hL : IsPPerfect 2 Lplus) (hL3 : Nat.card (Lplus ⧸ pCore 2 Lplus) = 3)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hr : primeRank p (Star H) ≤ 2)
    (hm : ¬ (star H Lplus hLH).pCoreIn 2 ≤ centralizer (pCore p (Star H) : Set (Star H)))
    (hU : U ≤ Stellmacher.omegaOneCenterAmbient (H.pCoreIn 2))
    (hY : primeRank p (centralizingResidual U) ≤ 1) :
    ∃ (D : Subgroup (Star H)) (hD : D.Characteristic),
      letI : D.Characteristic := hD
      let a := (MulAut.conjNormal : Star H →* MulAut D).comp (starMap H Lplus hLH)
      D ≤ pCore p (Star H) ∧ primeRank p D = 2 ∧ Chapter1.XiOddQuotient p D ∧
      (pCore 2 Lplus).map a ≠ ⊥ ∧
      Nonempty (a.range ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
      Nonempty ((((T : Subgroup G).subgroupOf Lplus).map a) ≃* QuaternionGroup 2) ∧
      ⁅U, (starResidual H D).map H.subtype⁆ ≠ ⊥ ∧
      ChapterA.Section04.IsFaithfulSignalizerType ((starResidual H D).map H.subtype) := by
  obtain ⟨D, hD, hle, hrD, hmodel, hmove, _, _, _, hmoved⟩ :=
    exists_moving_star_residual H Lplus U hLH hL hp hr hm hY
  let : D.Characteristic := hD
  let a := (MulAut.conjNormal : Star H →* MulAut D).comp (starMap H Lplus hLH)
  obtain ⟨S, hS⟩ := sylow_intersection T Lplus hTL
  have hfull := (actual_actor_models hp hmodel.isPGroup hrD.le hL hL3 a hmove).1
  have hsyl := actual_sylow_actor_model hp hmodel.isPGroup hrD.le hL hL3 a hmove S
  rw [hS] at hsyl
  exact ⟨D, hD, hle, hrD, hmodel, hmove, hfull, hsyl, hmoved,
    star_residual_faithful H U D hH hU hmoved⟩

end CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
