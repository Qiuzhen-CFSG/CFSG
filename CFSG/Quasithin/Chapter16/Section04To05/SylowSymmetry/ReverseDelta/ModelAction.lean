module
public import Theory.SpecificGroups.SymmetricFiveProduct.AlternatingAction

/-!
# The symmetric-five action used in reverse Δ₀ membership

Re-export the intrinsic product-action obstruction at the active source boundary.
The actual proof, using perfectness and the concrete transposition action on A₅,
lives in `Theory.SpecificGroups.SymmetricFiveProduct.AlternatingAction`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of Lemma 16.4.11(2), printed p.1193.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta
export Theory.SymmetricFiveProduct (A5 C2 InnerCentralizerModel product_has_outer_actor)
end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta
