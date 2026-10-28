module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.NormalGeneration
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.Words

/-!
# Odd-power tests for normal generation in the O'Nan model

The involution `a` normally generates the concrete matrix group. If `s` lies
in the normal closure of `r` and `a * s` has an odd power equal to one, then
killing `r` forces `a` to have both square and odd power one. Thus `r` also
normally generates. Conjugates and products of conjugates provide the words
`s` used by the explicit ATLAS representative certificates.

The representative words and their source attribution are in `Words.lean`;
this argument needs neither simplicity nor class coverage.
-/

namespace ONan.Simplicity

/-- A normal subgroup containing a normal generator is the whole group. -/
public theorem normal_eq_top_of_normalGenerator_mem {x : Model}
    (hx : Subgroup.normalClosure ({x} : Set Model) = ⊤)
    (N : Subgroup Model) [N.Normal] (h : x ∈ N) : N = ⊤ := by
  have hle : Subgroup.normalClosure ({x} : Set Model) ≤ N :=
    Subgroup.normalClosure_le_normal (by simpa using h)
  rw [hx] at hle
  exact top_unique hle

/-- An odd-power twist of the involution certifies normal generation. -/
public theorem normalClosure_eq_top_of_odd_twist {r s : Model} {n : ℕ}
    (hs : s ∈ Subgroup.normalClosure ({r} : Set Model))
    (hn : Odd n) (hpow : (generatorA * s) ^ n = 1) :
    Subgroup.normalClosure ({r} : Set Model) = ⊤ := by
  let N := Subgroup.normalClosure ({r} : Set Model)
  let q := QuotientGroup.mk' N
  have hqs : q s = 1 := (QuotientGroup.eq_one_iff _).mpr hs
  have ha2 : q generatorA ^ 2 = 1 := by simpa using congrArg q generatorA_pow_two
  have han : q generatorA ^ n = 1 := by simpa [hqs] using congrArg q hpow
  apply normal_eq_top_of_normalGenerator_mem normalClosure_generatorA_eq_top N
  exact (QuotientGroup.eq_one_iff _).mp
    ((pow_eq_one_iff_of_coprime hn.coprime_two_left).mp ⟨ha2, han⟩)

/-- It suffices to twist the involution by one conjugate of the representative. -/
public theorem normalClosure_eq_top_of_odd_conjugate {r : Model} (g : Model) {n : ℕ}
    (hn : Odd n) (hpow : (generatorA * (g * r * g⁻¹)) ^ n = 1) :
    Subgroup.normalClosure ({r} : Set Model) = ⊤ := by
  apply normalClosure_eq_top_of_odd_twist (s := g * r * g⁻¹) _ hn hpow
  exact Subgroup.Normal.conj_mem inferInstance r
    (Subgroup.subset_normalClosure (Set.mem_singleton r)) g

/-- A product with a conjugate gives a second short normal-generation test. -/
public theorem normalClosure_eq_top_of_odd_conjugate_product {r : Model}
    (g : Model) {n : ℕ} (hn : Odd n)
    (hpow : (generatorA * (r * (g * r * g⁻¹))) ^ n = 1) :
    Subgroup.normalClosure ({r} : Set Model) = ⊤ := by
  apply normalClosure_eq_top_of_odd_twist (s := r * (g * r * g⁻¹)) _ hn hpow
  exact Subgroup.mul_mem _ (Subgroup.subset_normalClosure (Set.mem_singleton r))
    (Subgroup.Normal.conj_mem inferInstance r
      (Subgroup.subset_normalClosure (Set.mem_singleton r)) g)

end ONan.Simplicity
