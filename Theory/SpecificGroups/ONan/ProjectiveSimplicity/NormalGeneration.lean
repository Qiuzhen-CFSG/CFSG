module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.Reduction
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.Relations

/-!
# Normal generation by the O'Nan standard generators

Killing either defining generator leaves an element whose order divides two
coprime integers: 4 and 11, or 2 and 11. The certified concrete relations
therefore show that either generator normally generates the matrix model.
The same relations give exact orders 2 and 11 for a and ab, using the existing
noncommutativity witness to exclude the identity.
-/

namespace ONan

/-- The first standard generator normally generates the concrete model. -/
public theorem normalClosure_generatorA_eq_top :
    Subgroup.normalClosure ({generatorA} : Set Model) = ⊤ :=
  normalClosure_generatorA_of_relations generatorB_pow_four generatorAB_pow_eleven

/-- The second standard generator normally generates the concrete model. -/
public theorem normalClosure_generatorB_eq_top :
    Subgroup.normalClosure ({generatorB} : Set Model) = ⊤ := by
  let N := Subgroup.normalClosure ({generatorB} : Set Model)
  have hbN : generatorB ∈ N := Subgroup.subset_normalClosure (Set.mem_singleton _)
  apply subgroup_eq_top_of_generators_mem N _ hbN
  let q := QuotientGroup.mk' N
  have hqb : q generatorB = 1 := (QuotientGroup.eq_one_iff _).mpr hbN
  have hqa2 : q generatorA ^ 2 = 1 := by simpa using congrArg q generatorA_pow_two
  have hqa11 : q generatorA ^ 11 = 1 := by
    simpa [hqb] using congrArg q generatorAB_pow_eleven
  exact (QuotientGroup.eq_one_iff _).mp
    ((pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 2 11)).mp ⟨hqa2, hqa11⟩)

/-- The first standard generator has order exactly two. -/
public theorem orderOf_generatorA : orderOf generatorA = 2 := by
  apply orderOf_eq_prime generatorA_pow_two
  intro h
  exact generatorA_mul_generatorB_ne (by simp [h])

/-- The standard product has order exactly eleven in the projective group. -/
public theorem orderOf_generatorAB : orderOf (generatorA * generatorB) = 11 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  apply orderOf_eq_prime generatorAB_pow_eleven
  intro h
  exact generatorA_mul_generatorB_ne (h.trans (mul_eq_one_comm.mp h).symm)

end ONan
