module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Basic

/-!
# The genuine L₃(2) quotient and its dual actions

The kernel of the point-stabilizer marking is the old O₂(L). Its two-group
kernel lets us pull back the geometric radical to the exact new O₂(P).
The action on the natural quotient by the marked line therefore identifies
P/O₂(P) with L₃(2). Evaluation identifies the annihilator action with the
contragredient of this quotient action, for the same original element of P.
The two-residual O²(P) is not identified with the two-core.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed pp.1129–1130 (PDF pp.1146–1147).
-/

@[expose] public section

open Subgroup BinaryLinear.OuterCyclic
open BinaryNaturalDual.VectorStabilizers BinaryNaturalDual.VectorStabilizers.Pure
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic

variable {G : Type*} [Group G] {d : LocalData G} {L : Subgroup G}

/-- The kernel of the parabolic marking is exactly the old component two-core. -/
theorem pointActor_ker (h : NaturalDual d L) (x : Space 4) :
    (pointActor h x).ker = (L.pCoreIn 2).subgroupOf (point h x) := by
  ext p
  change pointActor h x p = 1 ↔ (p : G) ∈ L.pCoreIn 2
  constructor
  · intro hp
    have he : linearAction (by decide) h.model ⟨p, point_le h x p.property⟩ = 1 :=
      congrArg (fun g : pointStabilizer x => g.val) hp
    have he' : QuotientGroup.mk' (pCore 2 L) ⟨p, point_le h x p.property⟩ = 1 := by
      apply h.model.map_eq_one_iff.mp
      apply (projectiveEquivLinear (by decide : 0 < 4)).map_eq_one_iff.mp
      exact he
    exact mem_map.mpr ⟨⟨p, point_le h x p.property⟩,
      (QuotientGroup.eq_one_iff (N := pCore 2 L) _).mp he', rfl⟩
  · rintro ⟨l, hl, he⟩
    apply Subtype.ext
    change linearAction (by decide) h.model ⟨p, point_le h x p.property⟩ = 1
    have hel : l = ⟨p, point_le h x p.property⟩ := Subtype.ext he
    rw [← hel]
    unfold linearAction
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [show QuotientGroup.mk' (pCore 2 L) l = 1 from
      (QuotientGroup.eq_one_iff (N := pCore 2 L) l).mpr hl, map_one, map_one]

/-- Quotient action on the three-dimensional quotient of the natural module. -/
noncomputable def quotientActor (h : NaturalDual d L) (x : Space 4) :
    point h x →* BinaryLinear.GL (pointQuotient x) :=
  (pointQuotientAction x).comp (pointActor h x)

theorem quotientActor_surjective (h : NaturalDual d L) (x : Space 4) :
    Function.Surjective (quotientActor h x) :=
  (Theory.LinearAlgebra.BinaryFivePointStabilizer.quotientAction_surjective x).comp
    (pointActor_surjective h x)

/-- The quotient action kills exactly the new parabolic two-core. -/
theorem quotientActor_ker [Finite G] (h : NaturalDual d L) (x : Space 4) :
    (quotientActor h x).ker = pCore 2 (point h x) := by
  let : Finite (BinaryLinear.GL (Space 4)) :=
    Finite.of_injective (fun g : BinaryLinear.GL (Space 4) => (g : Space 4 → Space 4))
      DFunLike.coe_injective
  have hk : IsPGroup 2 (pointActor h x).ker := by
    rw [pointActor_ker]
    exact (isPGroup_pCoreIn 2 L).of_equiv
      (subgroupOfEquivOfLe (componentCore_le_point h x)).symm
  have he := (pointActor h x).comap_pCore_of_ker_isPGroup
    (pointActor_surjective h x) hk
  rw [point_twoCore] at he
  exact he

/-- The original subgroup modulo its original two-core is genuinely L₃(2). -/
noncomputable def pointQuotientEquiv [Finite G] (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) :
    (point h x ⧸ pCore 2 (point h x)) ≃* Projective 3 :=
  ((QuotientGroup.quotientMulEquivOfEq (quotientActor_ker h x).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (quotientActor h x)
      (quotientActor_surjective h x))).trans
    ((quotientGroupCoordinates hx).trans (projectiveEquivLinear (by decide : 0 < 3)).symm)

/-- Conjugation on the marked three-dimensional dual annihilator. -/
noncomputable def annihilatorActor (h : NaturalDual d L) (x : Space 4) :
    point h x →* BinaryLinear.GL (annihilator x) :=
  (pointAnnihilatorAction x).comp (pointActor h x)

/-- The two three-dimensional actions are literal contragredients under the evaluation pairing. -/
theorem quotient_dual_compatibility (h : NaturalDual d L) (x : Space 4)
    (p : point h x) (q : annihilator x) :
    annihilatorQuotientDual x (annihilatorActor h x p q) =
      (quotientActor h x p).symm.dualMap (annihilatorQuotientDual x q) :=
  annihilator_quotient_compatibility x (pointActor h x p) q

theorem annihilatorActor_surjective (h : NaturalDual d L) (x : Space 4) :
    Function.Surjective (annihilatorActor h x) :=
  (pointAnnihilatorAction_surjective x).comp (pointActor_surjective h x)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic

end
