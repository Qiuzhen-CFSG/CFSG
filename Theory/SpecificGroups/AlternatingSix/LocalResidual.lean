module
public import Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.GroupTheory.CComponent.ThreeResidual
public import Theory.GroupTheory.PResidual.TwoThreeComparison
public import Theory.GroupTheory.PResidual.TwoKernelComparison

/-!
# Residuals in local overgroups of alternating six

A normal A₆ C-component in a group of three-rank at most two has index
prime to three: its quotient is centerless, has three-rank two, and has
outer automorphism group of order four. In the actual A₆, every proper
Sylow two-overgroup has order eight or twenty-four, so its two-residual
is its prime-to-three residual. Simplicity gives the same identity for A₆.

The source consumer restricts the ambient cubic residual to C_L(Ω₁Z(T))
and lifts this intrinsic comparison through its two-group kernel. Thus
these results remove the residual-identification premise in the A₆
case of Aschbacher–Smith 3.3.25(2), printed p.599; compare A.3.18, pp.51–52.
-/

public section
open Subgroup Theory.GroupTheory
namespace AlternatingSix.LocalResidual

/-- A normal A₆ C-component has index prime to three in a group of three-rank at most two. -/
theorem index_coprime_three {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [L.Normal] (hL : L.IsCComponent)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hr : primeRank 3 G ≤ 2) : Nat.Coprime 3 L.index := by
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have he := (centerCongr e ⟨z, hz⟩).property
    change e z ∈ center (alternatingGroup (Fin 6)) at he
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at he
    exact e.map_eq_one_iff.mp he
  have hrL : 2 ≤ primeRank 3 (L ⧸ pCore 2 L) := by
    rw [primeRank_congr 3 e]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  have ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (L ⧸ pCore 2 L))) := by
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv, ShadowLocal.outer_card]
    decide
  exact cComponent_index_coprime_three_of_quotient L hL hz hrL hr ho

private theorem whole_residuals :
    pResidual 2 (alternatingGroup (Fin 6)) = primeToResidual 3 (alternatingGroup (Fin 6)) := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have he : primeToResidual 3 (alternatingGroup (Fin 6)) = ⊤ := by
    rcases (inferInstance : (primeToResidual 3 (alternatingGroup (Fin 6))).Normal).eq_bot_or_eq_top with hz | ht
    · have hc := primeToResidual_index_coprime (G := alternatingGroup (Fin 6)) 3
      rw [hz, index_bot, nat_card_alternatingGroup] at hc
      norm_num [Nat.factorial] at hc
    · exact ht
  rw [he]
  apply le_antisymm le_top
  have h := primeToResidual_three_le_twoResidual (G := alternatingGroup (Fin 6))
  rw [he] at h
  exact h

/-- The two residuals agree in every overgroup of a full Sylow two-subgroup of A₆. -/
theorem sylow_overgroup_residuals (S : Sylow 2 (alternatingGroup (Fin 6)))
    (H : Subgroup (alternatingGroup (Fin 6))) (hSH : (S : Subgroup _) ≤ H) :
    pResidual 2 H = primeToResidual 3 H := by
  by_cases hH : H = ⊤
  · subst H
    have he := congrArg (fun U : Subgroup (alternatingGroup (Fin 6)) =>
      U.map (topEquiv.symm : alternatingGroup (Fin 6) ≃* (⊤ : Subgroup _)).toMonoidHom)
      whole_residuals
    rwa [map_pResidual_of_surjective 2 _ topEquiv.symm.surjective,
      map_primeToResidual topEquiv.symm] at he
  · have hc := ProperSylowOvergroups.card_eight_or_twentyFour S H hSH hH
    apply twoResidual_eq_primeToResidual_three
    apply (IsPiGroup_iff twoThreePrimes H).mpr
    intro p hp
    have hd : p.val ∣ 2 ^ 3 * 3 := hp.trans (by
      rcases hc with hc | hc <;> rw [hc] <;> decide)
    change p.val = 2 ∨ p.val = 3
    rcases p.property.dvd_mul.mp hd with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq p.property Nat.prime_two).mp
        (p.property.dvd_of_dvd_pow h2))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq p.property Nat.prime_three).mp h3)

end AlternatingSix.LocalResidual
