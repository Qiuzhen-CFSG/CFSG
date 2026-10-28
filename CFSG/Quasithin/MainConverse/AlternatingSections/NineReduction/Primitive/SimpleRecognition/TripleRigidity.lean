module

public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.SimpleRecognition.ActionBasics
public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.SimpleRecognition.TripleRigidity.OrderReduction
public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.SimpleRecognition.TripleRigidity.OrderCases
public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.SimpleRecognition.TripleRigidity.Exclude1512

/-!
# Three-point rigidity for the simple degree-nine action

In the given triple-transitive action, `OrderCases` restricts the simple
normal subgroup's order to 504 or 1512, and `Exclude1512` rules out 1512
using simplicity. Its order is therefore 504, so the orbit–stabilizer
formula from `OrderReduction` makes every pointwise triple stabilizer
trivial. The bound concerns elements of the simple normal subgroup.

Triple transitivity remains an explicit hypothesis of this action contract;
the parent recognition argument supplies it from seven-divisibility using
`primitive_simple_normal_three_pretransitive_of_seven`.

Application: condition K and the alternating case in Aschbacher–Smith,
*The Classification of Quasithin Groups*, `refs/quasithin.pdf`, printed
pp.4 and 482.
-/

namespace CFSG.Quasithin.MainConverse.NineReduction

/-- Every nonidentity element of the simple normal subgroup fixes at most two
points in the specified triple-transitive degree-nine action. -/
public theorem primitive_simple_normal_fixed_triple_bound
    (H : Subgroup (alternatingGroup (Fin 9))) (hH : H ≠ ⊤)
    (hp : MulAction.IsPreprimitive H (Fin 9))
    (N : Subgroup H) [N.Normal] [IsSimpleGroup N]
    (hna : ¬ IsMulCommutative N)
    (hthree : MulAction.IsMultiplyPretransitive N (Fin 9) 3) :
    ∀ g : N, g ≠ 1 → ∀ a b c : Fin 9,
      a ≠ b → a ≠ c → b ≠ c →
      ¬ (g • a = a ∧ g • b = b ∧ g • c = c) := by
  apply (nine_subgroup_fixed_triple_bound_iff_card H N hthree).mpr
  exact (primitive_simple_normal_nine_order_cases H hH hp N hna hthree).resolve_right
    (primitive_simple_normal_nine_order_ne_1512 H hH hp N hna hthree)

end CFSG.Quasithin.MainConverse.NineReduction
