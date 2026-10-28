module
public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Tactic

/-!
# Large automorphism subgroups are transitive on an elementary four-group

Let K be an actual subgroup of the automorphism group of an elementary
two-group W of order four. If K has more than two elements, the K-orbit of
every nonidentity point contains every other nonidentity point. The action
is the literal automorphism-subgroup action, with no chosen Sylow or extra
transitivity hypothesis.

The Klein-four automorphism group has order six, so K has order three or six.
The stabilizer of a nonidentity point embeds in the automorphisms fixing
that point, whose order is at most two. Its orbit avoids the identity and
therefore has at most three points. Orbit-stabilizer forces exactly three
points, giving the desired transitivity.

This source-neutral finite-action argument supplies the residual quotient
orbit step in Stellmacher, Journal of Algebra 190 (1997), (10.1)(11), printed
p.62. The geometric consumer retains its actual residual quotient and the
supplied conjugation action, then lifts the orbit statement to a coset.
-/

namespace MulAction
public theorem nonidentity_mem_orbit_of_four_automorphism_subgroup
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (K : Subgroup (MulAut W)) (hK : 2 < Nat.card K)
    (x : W) (hx : x ≠ 1) : ∀ y : W, y ≠ 1 → y ∈ orbit K x := by
  classical
  let _ : Nontrivial W := (Finite.one_lt_card_iff_nontrivial).mp (by rw [hW]; decide)
  let _ : IsKleinFour W := ⟨hW,IsElementaryAbelian.exponent_eq_prime⟩
  have hdiv : Nat.card K ∣ 6 := (IsKleinFour.card_mulAut W) ▸ K.card_subgroup_dvd_card
  have hbound : Nat.card K ≤ 6 := Nat.le_of_dvd (by decide) hdiv
  have hcases : Nat.card K = 3 ∨ Nat.card K = 6 := by
    interval_cases hcardK : Nat.card K <;> norm_num at hdiv <;> omega
  let stab := stabilizer K x
  have hstab : Nat.card stab ≤ 2 := by
    have hh := card_mulAut_subgroup_le_two_of_fixed_point hW x hx (stab.map K.subtype) (by
      rintro _ ⟨s,hs,rfl⟩
      exact hs)
    rwa [Subgroup.card_map_of_injective K.subtype_injective] at hh
  have hsub : orbit K x ⊆ ({1} : Set W)ᶜ := by
    intro y hy
    obtain ⟨a,rfl⟩ := mem_orbit_iff.mp hy
    change (a : MulAut W) x ≠ 1
    intro heq
    exact hx ((a : MulAut W).injective (heq.trans (map_one (a : MulAut W)).symm))
  have hcompl : (({1} : Set W)ᶜ).ncard = 3 := by
    rw [Set.ncard_compl,hW,Set.ncard_singleton]
  have horbit : (orbit K x).ncard ≤ 3 := by
    simpa only [hcompl] using Set.ncard_le_ncard hsub
  have hcount : (orbit K x).ncard * Nat.card stab = Nat.card K := by
    change Nat.card (orbit K x) * Nat.card stab = Nat.card K
    rw [←Nat.card_prod]
    exact Nat.card_congr (orbitProdStabilizerEquivGroup K x)
  have hthree : (orbit K x).ncard = 3 := by
    interval_cases ho : (orbit K x).ncard <;> omega
  have heq : orbit K x = ({1} : Set W)ᶜ :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcompl,hthree])
  intro y hy
  rw [heq]
  exact hy
end MulAction
