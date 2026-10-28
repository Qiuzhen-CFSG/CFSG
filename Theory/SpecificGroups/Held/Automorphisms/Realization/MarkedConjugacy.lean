module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedSubgroup
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.Conditions
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# A finite-calculation route to Held marked-subgroup conjugacy

The checked element `ab` has order 17. If its cyclic subgroup has index
prime to 17, Sylow conjugacy normalizes every automorphism's image of `ab`
to a power of `ab`. The image of `a` then determines that of `b`. A finite
check on these normalized pairs supplies a common fixed point of the three
marked words. Undoing the normalization gives a fixed point of the original
image subgroup.

The index hypothesis identifies the original marked subgroup with a point
stabilizer. Automorphisms preserve index, so the image subgroup equals its
point stabilizer as well. Transitivity now gives inner conjugacy.

The Sylow-index calculation and `NormalizedPairFixedPoint` remain unproved
inputs below. This module therefore does not yet prove the requested Held
conjugacy theorem. Neither a presentation isomorphism, subgroup-class
invariance, nor normalizer realization is assumed.

Sources: `Model/Source/HeG1-P1.M` and `HeG1-p2058B0`; the resulting
realization is needed for the full outer group in GLS3, Table 5.3p, as used
in Aschbacher--Smith, `refs/quasithin.pdf`, printed p.510.
-/

namespace Held.Realization.MarkedConjugacy

/-- Sylow conjugacy puts the product image in the sixteen nonidentity powers
(and hence in the displayed seventeen-element range). -/
public theorem exists_normalized_product
    (h17 : ¬ 17 ∣ (Subgroup.zpowers (a * b)).index) (f : MulAut He) :
    ∃ (g : He) (k : Fin 17), (MulAut.conj g * f) (a * b) = (a * b) ^ k.val := by
  classical
  let : Fact (Nat.Prime 17) := ⟨by decide⟩
  have hP : IsPGroup 17 (Subgroup.zpowers (a * b)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_ab, pow_one])
  let P : Sylow 17 He := hP.toSylow h17
  obtain ⟨y, hy⟩ := P.exists_isConj_of_orderOf_eq_prime_pow
    (x := f (a * b)) (n := 1) (by rw [f.orderOf_eq, orderOf_ab, pow_one])
  obtain ⟨g, hg⟩ := isConj_iff.mp hy
  have hymem : (y : He) ∈ Subgroup.zpowers (a * b) := y.property
  obtain ⟨k, hk, he⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hymem)
  refine ⟨g, ⟨k, ?_⟩, ?_⟩
  · simpa only [Finset.mem_range, orderOf_ab] using hk
  · exact hg.trans he.symm

/-- Normalize the product, apply the finite pair check, then undo the inner
conjugation on the resulting fixed point. -/
public theorem exists_fixedPoint_of_calculations
    (h17 : ¬ 17 ∣ (Subgroup.zpowers (a * b)).index)
    (hpair : NormalizedPairFixedPoint) (f : MulAut He) :
    ∃ p : Fin 2058, markedSubgroup.map f.toMonoidHom ≤ MulAction.stabilizer He p := by
  obtain ⟨g, k, hk⟩ := exists_normalized_product h17 f
  let f' : MulAut He := MulAut.conj g * f
  have hb : f' b = f' a * (a * b) ^ k.val := by
    rw [← hk]
    change f' b = f' a * f' (a * b)
    rw [← map_mul]
    congr 1
    rw [← mul_assoc, ← pow_two, a_sq, one_mul]
  have hr (i : Fin 7) : relationWord (f' a) (f' a * (a * b) ^ k.val) i = 1 := by
    rw [← hb]
    exact (map_relationWord f'.toMonoidHom a b i).symm.trans
      ((congrArg f' (relations i)).trans (map_one f'))
  obtain ⟨p, hp⟩ := hpair k (f' a) ((f'.orderOf_eq a).trans orderOf_a) hr
  rw [← hb] at hp
  have hle := map_le_stabilizer_of_pairFixes f' p hp
  refine ⟨g⁻¹ • p, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hh : f' x • p = p := hle (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have he := congrArg (fun q : Fin 2058 => g⁻¹ • q) hh
  change f x • (g⁻¹ • p) = g⁻¹ • p
  simpa only [f', MulAut.mul_apply, MulAut.conj_apply, mul_smul,
    inv_smul_smul] using he

/-- A fixed point of an automorphic marked subgroup gives the required
conjugacy: equal indices identify its stabilizer, and transitivity supplies
the conjugating group element. -/
public theorem map_conjugate_of_fixedPoint
    (hindex : markedSubgroup.index ≤ 2058) (f : MulAut He) (p : Fin 2058)
    (hle : markedSubgroup.map f.toMonoidHom ≤ MulAction.stabilizer He p) :
    ∃ g : He, markedSubgroup.map f.toMonoidHom =
      markedSubgroup.map (MulAut.conj g).toMonoidHom := by
  have hbase := markedSubgroup_eq_baseStabilizer_of_index_le hindex
  have hidx : (markedSubgroup.map f.toMonoidHom).index = 2058 := by
    rw [Subgroup.index_map_of_bijective f.bijective, hbase, baseStabilizer_index]
  have hidxp : (MulAction.stabilizer He p).index = 2058 := by
    rw [MulAction.index_stabilizer_of_transitive]
    simp
  have he : markedSubgroup.map f.toMonoidHom = MulAction.stabilizer He p := by
    apply le_antisymm hle
    by_contra hn
    have hi := Subgroup.index_strictAnti (lt_of_le_not_ge hle hn)
    rw [hidx, hidxp] at hi
    omega
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq He basePoint p
  refine ⟨g, ?_⟩
  rw [he, ← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj, hbase]

/-- Conditional assembly of marked-subgroup conjugacy. The two finite
calculations are still explicit obligations of this module's assembly owner. -/
public theorem map_conjugate_of_calculations
    (hindex : markedSubgroup.index ≤ 2058)
    (h17 : ¬ 17 ∣ (Subgroup.zpowers (a * b)).index)
    (hpair : NormalizedPairFixedPoint) (f : MulAut He) :
    ∃ g : He, markedSubgroup.map f.toMonoidHom =
      markedSubgroup.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨p, hp⟩ := exists_fixedPoint_of_calculations h17 hpair f
  exact map_conjugate_of_fixedPoint hindex f p hp

end Held.Realization.MarkedConjugacy
