module

public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.SimpleRecognition.TripleRigidity.OrderReduction
public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.SimpleRecognition.TripleRigidity.OrderCases.FiveExclusion
public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.SimpleRecognition.TripleRigidity.OrderCases.TwoExclusion
public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.SimpleRecognition.TripleRigidity.OrderCases.ThreeExclusion

/-!
# The order alternatives for the simple degree-nine action

The triple stabilizer embeds into the symmetric group on the other six
points. Its order divides 720. A factor nine forces a three-cycle by Sylow
conjugacy. A factor two forces a double transposition, whose setwise pair
stabilizer has image S₇, forcing a factor five. Finally a five-cycle in the
proper primitive overgroup produces a three-cycle by Jordan's proved
multiple-primitivity criterion and an explicit conjugation. Jordan's
three-cycle theorem excludes these cases.

Thus the triple stabilizer has order one or three. The exact orbit–stabilizer
formula from `OrderReduction` gives group order 504 or 1512. Every extra
premise of the action helpers is discharged here. The separate exclusion of
order 1512 remains with the parent recognition argument.

Source context: condition K and the alternating case in Aschbacher–Smith,
*The Classification of Quasithin Groups*, `refs/quasithin.pdf`, printed
pp.4 and 482. This is an intermediate permutation-action contract for that
argument, independent of a primitive-group catalogue or model recognition.
-/

namespace CFSG.Quasithin.MainConverse.NineReduction
open MulAction

private theorem triple_remaining_card : ∀ n ∈ Nat.divisors 720,
    ¬ 2 ∣ n → ¬ 5 ∣ n → ¬ 9 ∣ n → n = 1 ∨ n = 3 := by decide +kernel

set_option linter.unusedVariables false in
/-- The simple normal subgroup in the specified triple-transitive action has order 504 or 1512.
The permutation argument proves this without needing its normality or simplicity assumptions. -/
public theorem primitive_simple_normal_nine_order_cases
    (H : Subgroup (alternatingGroup (Fin 9))) (hH : H ≠ ⊤)
    (hp : IsPreprimitive H (Fin 9))
    (N : Subgroup H) [N.Normal] [IsSimpleGroup N]
    (hna : ¬ IsMulCommutative N)
    (hthree : IsMultiplyPretransitive N (Fin 9) 3) :
    Nat.card N = 504 ∨ Nat.card N = 1512 := by
  have hfive : ¬ 5 ∣ Nat.card N := fun h =>
    primitive_nine_not_five_dvd_card H hH hp (h.trans N.card_subgroup_dvd_card)
  have heven (g : N) : toPermHom N (Fin 9) g ∈ alternatingGroup (Fin 9) := g.val.val.property
  have hno (g : N) : ¬ (toPermHom N (Fin 9) g).IsThreeCycle :=
    primitive_nine_not_isThreeCycle H hH hp g.val
  have htwo := nine_two_not_dvd_fixing_triple_card N hthree heven hfive
  have hnine := nine_not_dvd_fixing_triple_card N hno
  have hd := nine_fixing_triple_card_dvd N
  have hfiveD : ¬ 5 ∣ Nat.card (fixingSubgroup N ({0, 1, 2} : Set (Fin 9))) := fun h =>
    hfive (h.trans (fixingSubgroup N ({0, 1, 2} : Set (Fin 9))).card_subgroup_dvd_card)
  have hcases := triple_remaining_card _ (Nat.mem_divisors.mpr ⟨hd, by decide⟩) htwo hfiveD hnine
  have hc := nine_subgroup_card_eq_triple_fixing H N hthree 0 1 2
    (by decide) (by decide) (by decide)
  rcases hcases with h | h
  · left
    simpa [h] using hc.symm
  · right
    simpa [h] using hc.symm

end CFSG.Quasithin.MainConverse.NineReduction
