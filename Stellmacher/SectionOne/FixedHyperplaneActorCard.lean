module
public import Stellmacher.SectionOne.QuadraticSubgroupFixedHyperplane

/-!
# Faithful quadratic actors with a common fixed hyperplane

Under the exact Section One hypotheses and Sylow-fixed generation assumption,
an actor whose common fixed subgroup has index two has order at most two.
The hereditary form of (1.2) supplies a subgroup of actor index at most two
whose fixed space escapes the common hyperplane. Its fixed space must be the
whole module, so faithfulness makes that subgroup trivial.

This does not assert rank reciprocity for arbitrary elementary actors: both
the faithful solvable action hypotheses and fixed-space generation are inputs.
-/

namespace Stellmacher.SectionOne
universe u v

/-- The genuine fixed-space generation hypothesis bounds a quadratic actor
with common fixed index two by order two. -/
public theorem quadratic_actor_card_le_two_of_fixed_index_two
    {G : Type u} {V : Type v} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hG : (⊤ : Subgroup G) = oddCore G ⊔ (S : Subgroup G))
    (hgenerate : (⊤ : Subgroup V) = actionClosure G V (FixedPoints.subgroup S V))
    (Y : Subgroup G) (hYS : Y ≤ (S : Subgroup G))
    (hquadratic : IsQuadraticAction Y V)
    (hindex : Nat.card V = 2 * Nat.card (FixedPoints.subgroup Y V)) :
    Nat.card Y ≤ 2 := by
  let R := FixedPoints.subgroup Y V
  have hRindex : R.index = 2 := by
    have hcard := R.card_mul_index
    have hpositive : 0 < Nat.card R := Nat.card_pos
    change Nat.card V = 2 * Nat.card R at hindex
    nlinarith
  have hR : R ≠ ⊤ := by
    intro heq
    simp [heq] at hRindex
  obtain ⟨Y₀, hY₀, hcard, hescape⟩ :=
    exists_fixed_hyperplane_of_quadratic_subgroup h S hG hgenerate
      Y hYS hquadratic R hR
  let U := FixedPoints.subgroup Y₀ V
  have hRU : R ≤ U := by
    intro vector hvector
    rw [FixedPoints.mem_subgroup] at hvector ⊢
    intro actor
    exact hvector ⟨actor, hY₀ actor.property⟩
  have hUindex : U.index ∣ 2 := hRindex ▸ Subgroup.index_dvd_of_le hRU
  have hUtop : U = ⊤ := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hUindex with hone | htwo
    · exact Subgroup.index_eq_one.mp hone
    · have hsame : R = U := by
        apply Subgroup.eq_of_le_of_card_ge hRU
        have hRcard := R.card_mul_index
        have hUcard := U.card_mul_index
        rw [hRindex] at hRcard
        rw [htwo] at hUcard
        omega
      exact (hescape hsame.ge).elim
  have hY₀bot : Y₀ = ⊥ := by
    apply le_bot_iff.mp
    intro actor hactor
    have hfixed : actor ∈ fixingSubgroup G (Set.univ : Set V) := by
      rw [mem_fixingSubgroup_iff]
      intro vector _
      have hvector : vector ∈ U := hUtop.ge (Subgroup.mem_top vector)
      exact ((FixedPoints.mem_subgroup _ _ _).mp hvector) ⟨actor, hactor⟩
    rwa [h.action_faithful] at hfixed
  simpa [hY₀bot] using hcard

end Stellmacher.SectionOne
