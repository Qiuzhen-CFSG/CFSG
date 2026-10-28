module
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Module.Submodule.Invariant

/-!
# Projections from pairwise coprime block annihilators

A complete family of block projections preserves every invariant subspace
when the blocks have pairwise coprime polynomial annihilators. Bezout's
identity realizes each projection as a polynomial in the operator.
-/
public section
namespace BinaryEndpointInduction
open Polynomial Module
variable {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V] [Fintype ι]

private theorem aeval_zero_of_dvd (a : Module.End F V) {p q : F[X]}
    (h : p ∣ q) {x : V} (hx : aeval a p x=0) : aeval a q x=0 := by
  obtain ⟨r,rfl⟩ := h
  rw [mul_comm,map_mul,Module.End.mul_apply,hx,map_zero]

/-- Coprime annihilators make each complete block projection a polynomial
in the common operator, so it preserves every invariant subspace. -/
theorem projections_preserve_of_coprime_annihilators
    (a : Module.End F V) (p : ι → F[X])
    (hp : Pairwise fun i j => IsCoprime (p i) (p j))
    (E : ι → Submodule F V) (π : ι → Module.End F V)
    (hπ : ∀ i, LinearMap.range (π i) ≤ E i)
    (hsum : ∑ i, π i=LinearMap.id)
    (hann : ∀ i x, x ∈ E i → aeval a (p i) x=0)
    (U : Submodule F V) (hU : U ∈ a.invtSubmodule) :
    ∀ i x, x ∈ U → π i x ∈ U := by
  classical
  intro i x hx
  let q : F[X] := ∏ j ∈ Finset.univ.erase i, p j
  have hc : IsCoprime (p i) q := IsCoprime.prod_right fun j hj =>
    hp (Finset.ne_of_mem_erase hj).symm
  obtain ⟨u,v,hbez⟩ := hc
  have hact : ∀ j y, y ∈ E j → aeval a (v*q) y=if j=i then y else 0 := by
    intro j y hy
    by_cases hji : j=i
    · subst j
      have hh := congrArg (fun r : F[X] => aeval a r y) hbez
      simpa only [map_add,map_mul,map_one,LinearMap.add_apply,Module.End.mul_apply,
        hann i y hy,map_zero,zero_add,Module.End.one_apply,ite_true] using hh
    · have hd : p j ∣ q := Finset.dvd_prod_of_mem p (Finset.mem_erase.mpr ⟨hji,Finset.mem_univ j⟩)
      rw [map_mul,Module.End.mul_apply,aeval_zero_of_dvd a hd (hann j y hy),map_zero,if_neg hji]
  have heq : aeval a (v*q) x=π i x := by
    have hxsum : x=∑ j, π j x := by
      simpa only [LinearMap.sum_apply,LinearMap.id_apply] using (LinearMap.congr_fun hsum x).symm
    conv_lhs => rw [hxsum]
    rw [map_sum]
    simp only [hact _ _ (hπ _ ⟨x,rfl⟩),Finset.sum_ite_eq',Finset.mem_univ,if_pos]
  rw [←heq]
  exact Polynomial.aeval_apply_smul_mem_of_le_comap hx (v*q) a hU
end BinaryEndpointInduction
