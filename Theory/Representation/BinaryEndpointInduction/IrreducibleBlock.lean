module
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Invariant spaces in one irreducible companion block

An endomorphism annihilated by an irreducible polynomial of degree equal
to the ambient dimension has no proper nonzero invariant subspace. The
minimal polynomial on any such subspace still equals the irreducible
annihilator, so Cayley--Hamilton forces full dimension.
-/
public section
namespace BinaryEndpointInduction
open Polynomial Module
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

private theorem aeval_restrict_coe (a : Module.End F V) (U : Submodule F V)
    (hU : U ∈ a.invtSubmodule) (p : Polynomial F) (x : U) :
    ((aeval (a.restrict hU) p) x : V)=aeval a p x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add,LinearMap.add_apply]
    change ((aeval (a.restrict hU) p x : U) : V)+
      ((aeval (a.restrict hU) q x : U) : V)=aeval a p x+aeval a q x
    rw [hp,hq]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial,Module.End.mul_apply,Module.algebraMap_end_apply]
    rw [Module.End.pow_restrict n hU]
    rfl

/-- A single irreducible polynomial block has only zero and full invariant spaces. -/
theorem eq_bot_or_top_of_irreducible_annihilator [FiniteDimensional F V]
    (a : Module.End F V) (p : Polynomial F) (hp : Irreducible p)
    (ha : aeval a p=0) (hd : p.natDegree=Module.finrank F V)
    (U : Submodule F V) (hU : U ∈ a.invtSubmodule) : U=⊥ ∨ U=⊤ := by
  by_cases hz : U=⊥
  · exact Or.inl hz
  have : Nontrivial U := U.nontrivial_iff_ne_bot.mpr hz
  let r := a.restrict hU
  have hr : aeval r p=0 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [aeval_restrict_coe,ha]
    rfl
  have hm : p ∣ minpoly F r :=
    ((hp.dvd_iff.mp (minpoly.dvd F r hr)).resolve_left (minpoly.not_isUnit F r)).dvd
  have hdim : p.natDegree ≤ Module.finrank F U := by
    calc
      p.natDegree ≤ (minpoly F r).natDegree :=
        Polynomial.natDegree_le_of_dvd hm (minpoly.ne_zero (LinearMap.isIntegral r))
      _ ≤ r.charpoly.natDegree :=
        Polynomial.natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly r) (LinearMap.charpoly_monic r).ne_zero
      _ = Module.finrank F U := LinearMap.charpoly_natDegree r
  exact Or.inr (Submodule.eq_top_of_finrank_eq (le_antisymm U.finrank_le (hd ▸ hdim)))
end BinaryEndpointInduction
