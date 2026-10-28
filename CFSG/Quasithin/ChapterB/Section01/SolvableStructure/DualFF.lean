module
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.SmallRatio

/-!
# Solvable dual-FF actions are FF

The solvable FF structure of the dual gives an order-two best offender.
The same involution has equal fixed codimension on the original module and
its dual, and hence is an offender on the original module. This removes the
dual-FF alternative in the literal ratio-two branch of Chapter15.
Source: Aschbacher--Smith B.1.8 and 15.1.7--8, printed pp.1088--1089.
-/

public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableDualFF
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

theorem isFFModule_of_dual
    (hs : Group.IsSolvable D) (hc : pCore 2 D = ⊥)
    (hf : Function.Injective ρ) (hff : IsFFModule ρ.dual) : IsFFModule ρ := by
  classical
  have hfd : Function.Injective ρ.dual := by
    intro g h he
    apply inv_injective
    apply hf
    ext v
    apply Module.eval_apply_injective (ZMod 2)
    ext f
    exact congrArg (fun T : Module.End (ZMod 2) (Module.Dual (ZMod 2) V) => T f v) he
  obtain ⟨d⟩ := solvableFFStructure_nonempty ρ.dual hs hc hfd hff
  let i : Fin d.count := ⟨0,d.count_pos⟩
  let S : Sylow 2 (d.factor i) := Classical.choice inferInstance
  let F := d.toSolvableFFFactors
  have hbest := F.factorSylow_best hfd d.ratio_one i S
  obtain ⟨t,ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (F.factorSylow_ne_bot i S)
  have ht2 : (t : D)^2 = 1 := by
    have hh := pow_card_eq_one' (x := t)
    rw [F.factorSylow_card i S] at hh
    exact congrArg Subtype.val hh
  have ht1 : (t : D) ≠ 1 := fun he => ht (Subtype.ext he)
  have ho : orderOf (t : D) = 2 := orderOf_eq_prime ht2 ht1
  have he : zpowers (t : D) = F.factorSylow i S := by
    apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr t.property)
    rw [Nat.card_zpowers,ho,F.factorSylow_card]
  refine ⟨zpowers (t : D), ?_, ?_⟩
  · exact (involution_actor_rank_and_fixedCodim ρ (t : D) ho).1
  · rw [← fixedCodim_zpowers_dual ρ (t : D),he]
    exact (hbest.isOffender ρ.dual).2
end CFSG.Quasithin.ChapterB.SolvableDualFF
