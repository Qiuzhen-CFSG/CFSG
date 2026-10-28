module

public import Theory.GroupTheory.CComponent.ThreeCore
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable
public import Theory.Alternating.PrimeRank
public import Theory.Alternating.Aut

/-!
# Prime-to-three residuals for the simple A₆ and A₇ rows

A normal C-component with two-core quotient A₆ or A₇ in three-rank at
most two is the prime-to-three residual. Both outer automorphism groups
are two-groups, so the centerless argument of A.3.18 applies. The final
lemma transports this calculation through the literal subgroup inclusion.
The hypothesis concerns the two-core quotient, not its central quotient:
the triple covers are not silently discarded.

Source: Aschbacher--Smith, A.3.18 and 3.3.22, printed pp.51--52 and 597.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup.IsCComponent
variable {G : Type*} [Group G] [Finite G]

private theorem alternating_outer_two {n : ℕ} (hn : n = 6 ∨ n = 7) :
    IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin n))) := by
  rcases hn with rfl | rfl
  · exact IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card
  · let A := alternatingGroup (Fin 7)
    have hcard : Nat.card (Equiv.Perm (Fin 7) ⧸ A) = 2 ^ 1 := by
      rw [← A.index_eq_card]
      exact alternatingGroup.index_eq_two
    apply (IsPGroup.of_card hcard).of_surjective (MulAut.outerAction A)
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
    obtain ⟨s, rfl⟩ :=
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
        (by decide) (by decide)).surjective a
    exact ⟨QuotientGroup.mk' A s, rfl⟩

/-- The simple alternating rows of the centerless A.3.18 argument. -/
theorem eq_primeToResidual_three_of_quotient_alternating
    {K : Subgroup G} (hK : K.IsCComponent) [K.Normal]
    [IsQuasisimple (K ⧸ pCore 2 K)] {n : ℕ} (hn : n = 6 ∨ n = 7)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin n))
    (hr : primeRank 3 G ≤ 2) : K = primeToResidual 3 G := by
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have he : e x ∈ center (alternatingGroup (Fin n)) :=
      (centerCongr e ⟨x, hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ n by omega)), mem_bot] at he
    exact e.map_eq_one_iff.mp he
  have hrK : 2 ≤ primeRank 3 (K ⧸ pCore 2 K) := by
    rw [primeRank_congr 3 e,
      GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime n 3 Nat.prime_three
        (by decide)]
    rcases hn with rfl | rfl <;> decide
  have ho : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K)) :=
    (alternating_outer_two hn).of_injective (MulAut.outerCongr e).toMonoidHom
      (MulAut.outerCongr e).injective
  exact hK.eq_primeToResidual_three_of_outer_twoGroup hz hrK hr ho

/-- The same residual identity with its original ambient embedding. -/
theorem map_primeToResidual_three_eq_of_quotient_alternating
    {H K : Subgroup G} (hK : (K.subgroupOf H).IsCComponent)
    (hle : K ≤ H) (hnorm : H ≤ normalizer (K : Set G))
    [IsQuasisimple (K ⧸ pCore 2 K)] {n : ℕ} (hn : n = 6 ∨ n = 7)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin n))
    (hr : primeRank 3 H ≤ 2) : (primeToResidual 3 H).map H.subtype = K := by
  let A := K.subgroupOf H
  let _ : A.Normal := normal_subgroupOf_of_le_normalizer hnorm
  let q : (A ⧸ pCore 2 A) ≃* (K ⧸ pCore 2 K) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hle) (pCore_map_iso 2 _)
  let _ : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv q.symm
  have he := hK.eq_primeToResidual_three_of_quotient_alternating hn (q.trans e) hr
  exact (congrArg (map H.subtype) he.symm).trans (map_subgroupOf_eq_of_le hle)

end Subgroup.IsCComponent
