module
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.Witness0
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.Witness1
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.Witness2
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.Reduction
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.TwoGroup

/-!
# Local normalizer lower bounds for the max4 entries

Each of three checked order-three words lies in the literal max4 subgroup and
normalizes its indicated Schreier closure. Under the relative index-two premise,
the fixed two-subgroup also normalizes that closure. Its order is a power of
two and at least 1024, so the local normalizer has at least 3072 elements.

The other four rows need only the fixed subgroup. Thus every lower bound needed
by the graph-cardinality assembly is supplied, using precisely the permitted
orbit-cardinality premise for the original representative. No exact Held order,
abstract local identification, or ambient normalizer catalogue is invoked.

Sources: GLS3 Table 5.3p; unchanged ATLAS max4/HeG1-p2058B0. The literal words
and kernel certificates are in `LocalWords` and `Witness0/1/2`.
-/

public section
open Subgroup
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4
open Held.LocalPairs.SylowGeometry.Calculations (representative representative_isPGroup)

theorem localWitness_conjugate_eq (i : Fin 3) (r : Fin 8) :
    localWitness i * schreierGenerator (largeRow i) r * (localWitness i)⁻¹ =
      evalSchreierWord (largeRow i) (conjugateWord i r) := by
  fin_cases i
  · exact Witness0.conjugate_eq r
  · exact Witness1.conjugate_eq r
  · exact Witness2.conjugate_eq r

theorem localWitness_order (i : Fin 3) : orderOf (localWitness i) = 3 := by
  have hc : localWitness i ^ 3 = 1 := by
    fin_cases i
    · exact Witness0.cube_eq_one
    · exact Witness1.cube_eq_one
    · exact Witness2.cube_eq_one
  have hn : localWitness i ≠ 1 := by
    fin_cases i
    · exact Witness0.ne_one
    · exact Witness1.ne_one
    · exact Witness2.ne_one
  exact (Nat.prime_three.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hc)).resolve_left
    (fun h => hn (orderOf_eq_one_iff.mp h))

theorem localWitness_mem_normalizer (i : Fin 3) :
    localWitness i ∈ normalizer (candidate (largeRow i) : Set He) := by
  have hc (r : Fin 8) :
      localWitness i * schreierGenerator (largeRow i) r * (localWitness i)⁻¹ ∈
        candidate (largeRow i) := by
    rw [localWitness_conjugate_eq]
    exact evalSchreierWord_mem _ _
  have hw (e : Bool) (j : Fin 4) :
      localWitness i * indexTwoGenerator (fixedGenerator true)
        (pivot (largeRow i)) (mask (largeRow i)) e j * (localWitness i)⁻¹ ∈
          candidate (largeRow i) := by
    cases e
    · fin_cases j
      · exact hc 0
      · exact hc 1
      · exact hc 2
      · exact hc 3
    · fin_cases j
      · exact hc 4
      · exact hc 5
      · exact hc 6
      · exact hc 7
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hle : (candidate (largeRow i)).map (MulAut.conj (localWitness i)).toMonoidHom ≤
      candidate (largeRow i) := by
    apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    rintro _ ⟨e, j, rfl⟩
    exact hw e j
  exact eq_of_le_of_card_ge hle
    (Nat.card_congr ((MulAut.conj (localWitness i)).subgroupMap (candidate (largeRow i))).toEquiv).le

theorem local_large_card_ge
    (horbits : ∀ x : Fin 2058,
      SylowGeometry.Calculations.InnerNormalizer.orbitSizeLabel x =
        Nat.card (MulAction.orbit representative x))
    (i : Fin 3) (hi : (candidate (largeRow i)).relIndex (fixedSubgroup true) = 2) :
    3072 ≤ Nat.card ↥(normalizer (candidate (largeRow i) : Set He) ⊓ localOvergroup true) := by
  let K := normalizer (candidate (largeRow i) : Set He) ⊓ localOvergroup true
  have hPK : fixedSubgroup true ≤ K :=
    le_inf (fixedSubgroup_le_normalizer (largeRow i) hi) (fixedSubgroup_le_localOvergroup true)
  have hP : Nat.card (fixedSubgroup true) ∣ Nat.card K := card_dvd_of_le hPK
  have h3 : 3 ∣ Nat.card K := by
    rw [← localWitness_order i]
    exact K.orderOf_dvd_natCard ⟨localWitness_mem_normalizer i, localWitness_mem i⟩
  have hp : IsPGroup 2 (fixedSubgroup true) := representative_isPGroup.map _
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hcop : Nat.Coprime 3 (Nat.card (fixedSubgroup true)) := by
    rw [hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  have hm : 3 * Nat.card (fixedSubgroup true) ∣ Nat.card K :=
    hcop.mul_dvd_of_dvd_of_dvd h3 hP
  exact (Nat.mul_le_mul_left 3 (fixedSubgroup_card_ge horbits)).trans
    (Nat.le_of_dvd Nat.card_pos hm)

/-- The extra lower bound required for each of the three large rows. -/
theorem local_normalizer_card_ge_3072
    (horbits : ∀ x : Fin 2058,
      SylowGeometry.Calculations.InnerNormalizer.orbitSizeLabel x =
        Nat.card (MulAction.orbit representative x))
    (j : Fin 7) (hj : bound j = 3072)
    (hi : (candidate j).relIndex (fixedSubgroup true) = 2) :
    3072 ≤ Nat.card ↥(normalizer (candidate j : Set He) ⊓ localOvergroup true) := by
  have hrows : ∀ r : Fin 7, bound r = 3072 → ∃ i : Fin 3, largeRow i = r := by
    decide +kernel
  obtain ⟨i, rfl⟩ := hrows j hj
  exact local_large_card_ge horbits i hi

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4
