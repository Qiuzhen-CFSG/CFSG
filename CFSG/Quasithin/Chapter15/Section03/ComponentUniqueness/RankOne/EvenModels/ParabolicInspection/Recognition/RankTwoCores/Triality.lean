module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.RankTwoCores.Transport
public import Theory.SpecificGroups.Triality.FullParabolicActions
public import Theory.SpecificGroups.Triality.ParabolicGeometry
public import Theory.SpecificGroups.Triality.ConcreteBruhat.CartanNormalizer

/-!
# Self-centralizing parabolic cores in genuine triality

The concrete rank-two Tits system classifies Borel overgroups by subsets of
its two simple reflections. Properness excludes the pair, so every such
overgroup lies in one of the full root parabolics. The established faithful
full-Levi actions give self-centralizing radicals there, and the exact
radical/core identity gives characteristic two. Sylow-overgroup inheritance
also covers the Borel, and conjugacy treats every specified Sylow subgroup.

The carrier is the central quotient of the elementary graph-field fixed
group, not the auxiliary coordinate-permutation model. The argument uses no
new order or simplicity assertion. Source: Aschbacher--Smith, A.2.4, p.33,
and the characteristic-two paragraph of 15.3.43, p.1140; GLS3 2.6.5.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
namespace TrialityCores
open Triality.Standard Triality.Standard.Parabolics

/-- Bruhat saturation puts every proper Borel overgroup in one of the two
full parabolics, also covering the Borel itself. -/
theorem overgroup_le_parabolic (P : Parameters) (hp : P.prime = 2)
    (Q : Subgroup (Carrier P)) (hBQ : borel P ≤ Q) (hQ : Q < ⊤) :
    ∃ a : Node, Q ≤ parabolic P a := by
  classical
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  let T := ConcreteBruhat.titsSystem n hn
  let s := ConcreteBruhat.simpleReflection n hn
  have he : Q = T.standardParabolic (T.simpleIndices Q) :=
    T.subgroup_eq_standardParabolic_simpleIndices Q hBQ
  have hS : T.S = {s .arms, s .central} := by
    ext w
    exact ConcreteBruhat.mem_titsSystem_S_iff n hn w
  have hnot : ¬ (s .arms ∈ T.simpleIndices Q ∧ s .central ∈ T.simpleIndices Q) := by
    rintro ⟨ha, hb⟩
    have hi : T.simpleIndices Q = T.S := by
      apply Set.Subset.antisymm (T.simpleIndices_subset Q)
      rw [hS]
      intro w hw
      rcases hw with rfl | rfl <;> assumption
    rw [hi, T.standardParabolic_S] at he
    exact hQ.ne he
  by_cases ha : s .arms ∈ T.simpleIndices Q
  · refine ⟨.arms, ?_⟩
    rw [ConcreteBruhat.parabolic_eq_standardParabolic, he]
    apply T.standardParabolic_mono
    intro w hw
    rcases (ConcreteBruhat.mem_titsSystem_S_iff n hn w).mp
      (T.simpleIndices_subset Q hw) with rfl | rfl
    · exact Set.mem_singleton _
    · exact (hnot ⟨ha, hw⟩).elim
  · refine ⟨.central, ?_⟩
    rw [ConcreteBruhat.parabolic_eq_standardParabolic, he]
    apply T.standardParabolic_mono
    intro w hw
    rcases (ConcreteBruhat.mem_titsSystem_S_iff n hn w).mp
      (T.simpleIndices_subset Q hw) with rfl | rfl
    · exact (ha hw).elim
    · exact Set.mem_singleton _

theorem parabolic_core (P : Parameters) (hp : P.prime = 2) (a : Node) :
    centralizer (pCore 2 (parabolic P a) : Set (parabolic P a)) ≤
      pCore 2 (parabolic P a) := by
  rw [parabolic_twoCore_eq P hp a]
  intro x hx
  apply parabolic_centralizer_radical_le P hp a
  refine ⟨x.property, ?_⟩
  intro y hy
  exact congrArg Subtype.val
    (hx ⟨y, radical_le_parabolic P a hy⟩ hy)

theorem borelOvergroupCores (P : Parameters) (hp : P.prime = 2) :
    BorelOvergroupCores (Carrier P) := by
  apply borelOvergroupCores_of_standard (unipotentSylow P hp)
  intro Q hBQ hQ
  have hB : borel P ≤ Q := by
    change normalizer (unipotent P : Set (Carrier P)) ≤ Q at hBQ
    simpa only [ConcreteBruhat.normalizer_unipotent_eq_borel P hp] using hBQ
  obtain ⟨a, hQP⟩ := overgroup_le_parabolic P hp Q hB hQ
  exact core_of_sylow_overgroup_le (unipotentSylow P hp) Q (parabolic P a)
    ((unipotentSylow P hp : Subgroup (Carrier P)).le_normalizer.trans hBQ)
    hQP (parabolic_core P hp a)

end TrialityCores

/-- The genuine triality model at the specified binary field order. -/
theorem triality_borelOvergroupCores {H : Type*} [Group H] [Finite H]
    {n : ℕ}
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) H) : BorelOvergroupCores H := by
  obtain ⟨P, hq, ⟨e⟩⟩ := hm
  have hp : P.prime = 2 := by
    apply (Nat.prime_dvd_prime_iff_eq P.prime_prime Nat.prime_two).mp
    apply P.prime_prime.dvd_of_dvd_pow
    rw [← hq]
    exact dvd_pow_self P.prime (Nat.ne_of_gt P.exponent_pos)
  exact borelOvergroupCores_of_mulEquiv e (TrialityCores.borelOvergroupCores P hp)

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
