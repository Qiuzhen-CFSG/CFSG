module

public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.QuasithinBasic
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Two-rank of automorphisms with cyclic outer quotient

For a finite centerless group S, inner automorphisms are isomorphic to S.
The elementary-subgroup kernel/image rank inequality and the cyclic outer
quotient therefore bound the two-rank of Aut(S) by the two-rank of S plus one.
This needs no classification of elementary subgroups in mixed outer cosets.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
G.9, printed p.356. The triality consumer only needs this coarse estimate
for exponents at least three.
-/

public section
open Subgroup
namespace Theory.GroupTheory

theorem automorphism_twoRank_le_of_cyclic_outer
    {S : Type*} [Group S] [Finite S] (hz : center S = ⊥)
    [IsCyclic (MulAut.Outer S)] :
    primeRank 2 (MulAut S) ≤ primeRank 2 S + 1 := by
  have hf : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply (MulAut.conj : S →* MulAut S).ker.eq_bot_iff_forall.mpr
    intro x hx
    have hx' : MulAut.conj x = 1 := hx
    have hc : x ∈ center S := by
      rw [mem_center_iff]
      intro y
      have hy := MulEquiv.congr_fun hx' y
      change x * y * x⁻¹ = y at hy
      exact (mul_inv_eq_iff_eq_mul.mp hy).symm
    simpa only [hz, mem_bot] using hc
  let e : S ≃* MulAut.innerSubgroup S := MonoidHom.ofInjective hf
  have hr := primeRank_le_ker_add
    (QuotientGroup.mk' (MulAut.innerSubgroup S)) (p := 2)
  rw [QuotientGroup.ker_mk', ← primeRank_equiv 2 e] at hr
  let P : Sylow 2 (MulAut.Outer S) := Classical.choice inferInstance
  have ho : primeRank 2 (MulAut.Outer S) ≤ 1 :=
    P.primeRank_le_one_of_isCyclic inferInstance
  change primeRank 2 (MulAut S) ≤
    primeRank 2 S + primeRank 2 (MulAut.Outer S) at hr
  exact hr.trans (Nat.add_le_add_left ho _)

end Theory.GroupTheory
