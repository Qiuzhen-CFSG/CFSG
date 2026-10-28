module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeNormalGeneration.Reduction
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeNormalGeneration.NineteenRelation

/-!
# Normal generation by the prime representative words

The checked relations close the representatives labelled 2A, 11A, 19ABC,
and 31AB. In a quotient killing `ab²`, the elements `ab` and `b⁻¹` agree,
so the fourth and eleventh powers of `b` force it to vanish. Killing `ab`
instead leaves `b` with fourth and nineteenth powers one. Finally the
31AB word is `c²d²`, where `c = ab` and `d = ab²`; its vanishing forces
`c²` to have both eleventh and nineteenth powers one, and hence `c = 1`.

The remaining four cases are isolated by the finite assembly theorem below.
Representative source: the ATLAS program preserved and attributed in
`ProjectiveSimplicity/Words.lean`.
-/

namespace ONan.Simplicity

public theorem normalClosure_primeRepresentative_zero_eq_top :
    Subgroup.normalClosure ({primeRepresentative 0} : Set Model) = ⊤ :=
  normalClosure_generatorA_eq_top

public theorem normalClosure_primeRepresentative_five_eq_top :
    Subgroup.normalClosure ({primeRepresentative 5} : Set Model) = ⊤ := by
  let N := Subgroup.normalClosure ({primeRepresentative 5} : Set Model)
  let q := QuotientGroup.mk' N
  have hc : q (generatorA * generatorB) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure (Set.mem_singleton _))
  have hb4 : q generatorB ^ 4 = 1 := by simpa using congrArg q generatorB_pow_four
  have hb19 : q generatorB ^ 19 = 1 := by
    simpa only [pow_two, ← mul_assoc, map_mul, hc, one_mul, map_pow, map_one]
      using congrArg q generatorAB2_pow_nineteen
  apply normal_eq_top_of_normalGenerator_mem normalClosure_generatorB_eq_top N
  exact (QuotientGroup.eq_one_iff _).mp
    ((pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 4 19)).mp ⟨hb4, hb19⟩)

public theorem normalClosure_primeRepresentative_six_eq_top :
    Subgroup.normalClosure ({primeRepresentative 6} : Set Model) = ⊤ := by
  let N := Subgroup.normalClosure ({primeRepresentative 6} : Set Model)
  let q := QuotientGroup.mk' N
  have hd : q ((generatorA * generatorB) * generatorB) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure (Set.mem_singleton _))
  have hc : q (generatorA * generatorB) = (q generatorB)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa only [map_mul] using hd)
  have hb4 : q generatorB ^ 4 = 1 := by simpa using congrArg q generatorB_pow_four
  have hb11 : q generatorB ^ 11 = 1 := by
    simpa only [map_pow, hc, map_one, inv_pow, inv_eq_one]
      using congrArg q generatorAB_pow_eleven
  apply normal_eq_top_of_normalGenerator_mem normalClosure_generatorB_eq_top N
  exact (QuotientGroup.eq_one_iff _).mp
    ((pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 4 11)).mp ⟨hb4, hb11⟩)

public theorem normalClosure_primeRepresentative_seven_eq_top :
    Subgroup.normalClosure ({primeRepresentative 7} : Set Model) = ⊤ := by
  let N := Subgroup.normalClosure ({primeRepresentative 7} : Set Model)
  let q := QuotientGroup.mk' N
  let c := q (generatorA * generatorB)
  let d := q (generatorA * generatorB ^ 2)
  have hword : primeRepresentative 7 =
      (generatorA * generatorB) ^ 2 * (generatorA * generatorB ^ 2) ^ 2 := by
    change ((generatorA * generatorB) *
      ((generatorA * generatorB) * ((generatorA * generatorB) * generatorB))) *
      ((generatorA * generatorB) * generatorB) = _
    simp only [pow_two, mul_assoc]
  have hcd : c ^ 2 * d ^ 2 = 1 := by
    have hq : q (primeRepresentative 7) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure (Set.mem_singleton _))
    simpa only [hword, map_mul, map_pow, c, d] using hq
  have hc11 : c ^ 11 = 1 := by simpa [c] using congrArg q generatorAB_pow_eleven
  have hd19' : d ^ 19 = 1 := by simpa [d] using congrArg q generatorAB2_pow_nineteen
  have hc2_19 : (c ^ 2) ^ 19 = 1 := by
    rw [eq_inv_of_mul_eq_one_left hcd, inv_pow, ← pow_mul,
      Nat.mul_comm 2 19, pow_mul, hd19', one_pow, inv_one]
  have hc2_11 : (c ^ 2) ^ 11 = 1 := by
    rw [← pow_mul, Nat.mul_comm 2 11, pow_mul, hc11, one_pow]
  have hc2 : c ^ 2 = 1 :=
    (pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 11 19)).mp ⟨hc2_11, hc2_19⟩
  have hc : c = 1 :=
    (pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 2 11)).mp ⟨hc2, hc11⟩
  apply normal_eq_top_of_normalGenerator_mem normalClosure_primeRepresentative_five_eq_top N
  exact (QuotientGroup.eq_one_iff _).mp hc

/-- Four remaining normal-generation certificates suffice for the full list. -/
public theorem normalClosure_primeRepresentative_eq_top_of_remaining
    (h1 : Subgroup.normalClosure ({primeRepresentative 1} : Set Model) = ⊤)
    (h2 : Subgroup.normalClosure ({primeRepresentative 2} : Set Model) = ⊤)
    (h3 : Subgroup.normalClosure ({primeRepresentative 3} : Set Model) = ⊤)
    (h4 : Subgroup.normalClosure ({primeRepresentative 4} : Set Model) = ⊤)
    (i : Fin 8) : Subgroup.normalClosure ({primeRepresentative i} : Set Model) = ⊤ := by
  fin_cases i
  · exact normalClosure_primeRepresentative_zero_eq_top
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact normalClosure_primeRepresentative_five_eq_top
  · exact normalClosure_primeRepresentative_six_eq_top
  · exact normalClosure_primeRepresentative_seven_eq_top

end ONan.Simplicity
