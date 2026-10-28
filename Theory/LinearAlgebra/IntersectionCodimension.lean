module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!+# Codimension of a finite intersection

The diagonal map embeds the quotient by an intersection into the product of
the individual quotients. Consequently its dimension is at most the sum of
their dimensions. Equality of the outer bounds forces any intervening
subspace to equal the intersection.

This is the linear algebra in Aschbacher–Smith, *The Classification of
Quasithin Groups*, Lemma B.2.17 (1 March 2004 manuscript, pp. 79–80).
-/

namespace Submodule

variable {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] [Fintype ι]

/-- The codimension of an intersection is bounded by the sum of codimensions. -/
public theorem finrank_quotient_iInf_le_sum (U : ι → Submodule F V) :
    Module.finrank F (V ⧸ ⨅ i, U i) ≤ ∑ i, Module.finrank F (V ⧸ U i) := by
  let f := LinearMap.pi fun i => (U i).mkQ
  have hker : LinearMap.ker f = ⨅ i, U i := by
    simp [f, LinearMap.ker_pi]
  let q := (⨅ i, U i).liftQ f hker.ge
  have hq : Function.Injective q := by
    apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le
  have h := LinearMap.finrank_le_finrank_of_injective hq
  simpa only [Module.finrank_pi_fintype] using h

/-- If an intermediate subspace has at least the sum of the codimensions,
all the dimension bounds are equalities. -/
public theorem eq_iInf_of_sum_quotient_finrank_le
    (U : ι → Submodule F V) (W : Submodule F V)
    (hUW : (⨅ i, U i) ≤ W)
    (hbound : (∑ i, Module.finrank F (V ⧸ U i)) ≤ Module.finrank F (V ⧸ W)) :
    W = ⨅ i, U i ∧
      Module.finrank F (V ⧸ W) = ∑ i, Module.finrank F (V ⧸ U i) := by
  have hsum := finrank_quotient_iInf_le_sum U
  have hmono := Submodule.finrank_mono hUW
  have hdimU := (⨅ i, U i).finrank_quotient_add_finrank
  have hdimW := W.finrank_quotient_add_finrank
  have heq : Module.finrank F ↥(⨅ i, U i) = Module.finrank F W := by omega
  exact ⟨(Submodule.eq_of_le_of_finrank_eq hUW heq).symm, by omega⟩

end Submodule
