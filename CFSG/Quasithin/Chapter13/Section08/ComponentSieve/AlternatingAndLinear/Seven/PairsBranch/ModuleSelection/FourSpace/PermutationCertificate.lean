module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.ModuleSelection.FourSpace.PermutationInput
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.PermutationOvergroups.Placement.Coverage

/-!
# The even pair-stabilizer permutation certificate

The even stabilizer of `{{0,1},{2,3},{4,5},{6}}` has order 24. Every even
permutation outside it has a right translate by the stabilizer of order five
or seven. This is the finite input to the four-dimensional plane obstruction.

We reuse the proved decomposition of S₇ into 98 double cosets of its standard
even Sylow subgroup. Six explicit stabilizer elements supply the required
right multipliers for the even representatives outside the pair stabilizer.
Both this finite check and the cardinality check use kernel reduction.
If `g = a * r * b` and `r * q` has the required order, the right multiplier
`b⁻¹ * q * a⁻¹` makes `g` conjugate to `r * q` after multiplication.

Source: the partition-stabilizer exclusion in Aschbacher–Smith,
*The Classification of Quasithin Groups*, 13.8.24, printed p.959/PDF p.976.
-/

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.ModuleSelection.FourSpace
open Equiv
open LocalGeometry.PermutationOvergroups
open PlacementCertificate

private def rightMultiplier : Fin 6 → S7 := ![
  ⟨![0, 1, 2, 3, 4, 5, 6], ![0, 1, 2, 3, 4, 5, 6], by decide, by decide⟩,
  ⟨![1, 0, 4, 5, 3, 2, 6], ![1, 0, 5, 4, 2, 3, 6], by decide, by decide⟩,
  ⟨![0, 1, 4, 5, 2, 3, 6], ![0, 1, 4, 5, 2, 3, 6], by decide, by decide⟩,
  ⟨![1, 0, 2, 3, 5, 4, 6], ![1, 0, 2, 3, 5, 4, 6], by decide, by decide⟩,
  ⟨![2, 3, 0, 1, 4, 5, 6], ![2, 3, 0, 1, 4, 5, 6], by decide, by decide⟩,
  ⟨![3, 2, 0, 1, 5, 4, 6], ![2, 3, 1, 0, 5, 4, 6], by decide, by decide⟩ ]

set_option maxRecDepth 10000 in
private theorem multiplier_mem :
    ∀ i, (rightMultiplier i).sign = 1 ∧ rightMultiplier i ∈ pairStabilizer := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem representative_witness :
    ∀ j : Fin 98, (rep j).sign = 1 → rep j ∉ pairStabilizer →
      ∃ i : Fin 6, rep j * rightMultiplier i ≠ 1 ∧
        ((rep j * rightMultiplier i) ^ 5 = 1 ∨ (rep j * rightMultiplier i) ^ 7 = 1) := by
  decide +kernel

-- Filter by partition preservation first, so signs are computed only for
-- the 48 permutations in the full pair stabilizer.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem even_count :
    Nat.card {g : S7 // g ∈ pairStabilizer ∧ g.sign = 1} = 24 := by
  let : Fintype S7 := fintypePerm
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem actual_even_count : Nat.card evenPairStabilizer = 24 := by
  let e : evenPairStabilizer ≃ {g : S7 // g ∈ pairStabilizer ∧ g.sign = 1} :=
    { toFun := fun g => ⟨g.val.val, g.property, g.val.property⟩
      invFun := fun g => ⟨⟨g.val, g.property.2⟩, g.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans even_count

private theorem symmetric_witness (g : S7) (heven : g.sign = 1)
    (hout : g ∉ pairStabilizer) :
    ∃ p : S7, p.sign = 1 ∧ p ∈ pairStabilizer ∧
      (orderOf (g * p) = 5 ∨ orderOf (g * p) = 7) := by
  obtain ⟨i, j, k, hg⟩ := decomposition g
  have ha : upper i ∈ pairStabilizer := (upper_mem i).1.2
  have hb : upper k ∈ pairStabilizer := (upper_mem k).1.2
  have hea : (upper i).sign = 1 := (upper_mem i).2
  have heb : (upper k).sign = 1 := (upper_mem k).2
  have her : (rep j).sign = 1 := by
    simpa only [hg, map_mul, hea, heb, one_mul, mul_one] using heven
  have hr : rep j ∉ pairStabilizer := by
    intro h
    exact hout (hg ▸ pairStabilizer.mul_mem (pairStabilizer.mul_mem ha h) hb)
  obtain ⟨l, hne, hpow⟩ := representative_witness j her hr
  let p := (upper k)⁻¹ * rightMultiplier l * (upper i)⁻¹
  refine ⟨p, ?_, ?_, ?_⟩
  · simp only [p, map_mul, map_inv, hea, heb, (multiplier_mem l).1, inv_one, mul_one]
  · exact pairStabilizer.mul_mem
      (pairStabilizer.mul_mem (pairStabilizer.inv_mem hb) (multiplier_mem l).2)
      (pairStabilizer.inv_mem ha)
  · have hconj : g * p = MulAut.conj (upper i) (rep j * rightMultiplier l) := by
      rw [hg, MulAut.conj_apply]
      dsimp [p]
      group
    rw [hconj, MulEquiv.orderOf_eq]
    rcases hpow with h | h
    · let : Fact (Nat.Prime 5) := ⟨by decide⟩
      exact Or.inl (orderOf_eq_prime h hne)
    · let : Fact (Nat.Prime 7) := ⟨by decide⟩
      exact Or.inr (orderOf_eq_prime h hne)

/-- The finite permutation calculation for the actual even pair stabilizer,
with no additional representation or classification premise. -/
public theorem permutationCertificate : PermutationCertificate := by
  refine ⟨actual_even_count, ?_⟩
  intro g hout
  obtain ⟨p, heven, hp, ho⟩ := symmetric_witness g.val g.property hout
  let p' : A7 := ⟨p, heven⟩
  refine ⟨p', hp, ?_⟩
  have horder : orderOf (g * p') = orderOf (g.val * p) :=
    (Subgroup.orderOf_coe (g * p')).symm
  rwa [horder]

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.ModuleSelection.FourSpace
