module
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.BruhatCoverage.SplitCoverage.Collection
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.BruhatCoverage.SplitCoverage.WeylAction
public import Theory.AlgebraicGroup.BNPair.SimpleLiftCoverage

/-!
# Two-cell exchange from actual binary root relations

Collect the chosen simple root last. Its Weyl word preserves all other
positive roots. The parameter zero stays in the original Weyl cell; at one,
the rank-one word and the sign of the conjugated root select one of two cells.
This proves the exchange step of GLS3 1.11.1(d)(1) from 1.12.1(b,h),
`refs/KGroup/GLS3/Chapter1.tex`. The two root relations remain explicit inputs.
-/

public section
noncomputable section
namespace ReeF4.Parabolics.Binary.FixedGeometry.BruhatCoverage
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RadicalCoordinates LargeLocalSeeds Subgroup
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem root_zero (r : F4Chevalley.Root) :
    rootGeneratorInGroup 0 r 0 = 1 := by
  apply Subtype.ext
  exact F4Chevalley.rootCurve_zero r

private theorem root_add (r : F4Chevalley.Root) (a b : CoefficientField 0) :
    rootGeneratorInGroup 0 r a * rootGeneratorInGroup 0 r b =
      rootGeneratorInGroup 0 r (a + b) := by
  apply Subtype.ext
  exact (F4Chevalley.rootCurve_add r a b).symm

private def rootSubgroup (r : F4Chevalley.Root) : Subgroup (SplitGroup 0) where
  carrier := Set.range (rootGeneratorInGroup 0 r)
  one_mem' := ⟨0, root_zero r⟩
  mul_mem' := by
    rintro a b ⟨t, rfl⟩ ⟨v, rfl⟩
    exact ⟨t + v, (root_add r t v).symm⟩
  inv_mem' := by
    rintro a ⟨t, rfl⟩
    refine ⟨-t, ?_⟩
    apply Subtype.ext
    exact (F4Chevalley.rootCurve_inv r t).symm

/-- The actual binary simple Weyl words are involutions. -/
theorem simpleWord_mul_self (i : Fin 4) : simpleWord 0 [i] * simpleWord 0 [i] = 1 := by
  simpa [torusWord, simpleWord, CharTwo.neg_eq] using
    torusWord_zero (typeF4SimpleRootIndex i) (1 : (CoefficientField 0)ˣ)

private theorem simpleWord_mul_root (i : Fin 4) :
    simpleWord 0 [i] * rootGeneratorInGroup 0 (typeF4SimpleRootIndex i) 1 =
      rootGeneratorInGroup 0 (typeF4SimpleRootIndex i) 1 *
        rootGeneratorInGroup 0 (-typeF4SimpleRootIndex i) 1 := by
  have hxx : rootGeneratorInGroup 0 (typeF4SimpleRootIndex i) 1 *
      rootGeneratorInGroup 0 (typeF4SimpleRootIndex i) 1 = 1 := by
    rw [root_add, CharTwo.add_self_eq_zero, root_zero]
  simp only [simpleWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, weylWord, inv_one, CharTwo.neg_eq, mul_assoc, hxx]

private theorem simple_positive_factorization (hswap : BinaryPositiveRootExchanges)
    (hconj : BinarySimpleRootConjugation) (i : Fin 4)
    {u : SplitGroup 0} (hu : u ∈ splitUnipotent 0) :
    ∃ a ∈ splitUnipotent 0,
      simpleWord 0 [i] * a * (simpleWord 0 [i])⁻¹ ∈ splitUnipotent 0 ∧
      ∃ t : CoefficientField 0, u = a * rootGeneratorInGroup 0 (typeF4SimpleRootIndex i) t := by
  let A := splitUnipotent 0 ⊓
    (splitUnipotent 0).comap (MulAut.conj (simpleWord 0 [i])).toMonoidHom
  have hpartition (r : Root .positive) :
      (∀ t, rootGeneratorInGroup 0 r.val t ∈ A) ∨
      (∀ t, rootGeneratorInGroup 0 r.val t ∈ rootSubgroup (typeF4SimpleRootIndex i)) := by
    by_cases hr : r.val = typeF4SimpleRootIndex i
    · exact Or.inr (fun t => ⟨t, by rw [hr]⟩)
    · refine Or.inl (fun t => ⟨subset_closure ⟨r.val, t, r.property, rfl⟩, ?_⟩)
      change simpleWord 0 [i] * rootGeneratorInGroup 0 r.val t * (simpleWord 0 [i])⁻¹ ∈ splitUnipotent 0
      rw [hconj]
      exact subset_closure ⟨_, t,
        r.property.reflectionPerm (typeF4RootPairing_baseEquiv i).property hr, rfl⟩
  obtain ⟨a, ha, b, hb, he⟩ := positive_factorization_of_root_partition hswap
    A (rootSubgroup (typeF4SimpleRootIndex i)) hpartition hu
  obtain ⟨t, rfl⟩ := hb
  exact ⟨a, ha.1, ha.2, t, he⟩

/-- Positive root collection and the simple matrix conjugation relation imply
exactly the local two-cell exchange law. -/
theorem simpleLiftExchange_of_root_relations (hswap : BinaryPositiveRootExchanges)
    (hconj : BinarySimpleRootConjugation) :
    BruhatGeneration.SimpleLiftExchange (splitUnipotent 0) splitWeylSubgroup
      (Set.range fun i : Fin 4 => simpleWord 0 [i]) := by
  rintro s ⟨i, rfl⟩ u hu n hn
  obtain ⟨a, ha, hsa, t, rfl⟩ := simple_positive_factorization hswap hconj i hu
  have ht : t = 0 ∨ t = 1 := by
    apply eq_zero_or_one_of_sq_eq_self
    simpa using field_pow 0 t
  rcases ht with rfl | rfl
  · refine ⟨simpleWord 0 [i] * a * (simpleWord 0 [i])⁻¹, 1, hsa,
      (splitUnipotent 0).one_mem, Or.inl ?_⟩
    rw [root_zero]
    group
  · obtain ⟨σ, hneg, hσ⟩ := weyl_root_conjugation_of_simple hconj
      (splitWeylSubgroup.inv_mem hn)
    have hp : rootGeneratorInGroup 0 (typeF4SimpleRootIndex i) 1 ∈ splitUnipotent 0 :=
      subset_closure ⟨_, 1,
        typeF4RootPairing_base.isPos_of_mem_support (typeF4RootPairing_baseEquiv i).property, rfl⟩
    by_cases hr : typeF4RootPairing_base.IsPos (σ (typeF4SimpleRootIndex i))
    · refine ⟨simpleWord 0 [i] * a * (simpleWord 0 [i])⁻¹,
        rootGeneratorInGroup 0 (σ (typeF4SimpleRootIndex i)) 1, hsa,
        subset_closure ⟨_, 1, hr, rfl⟩, Or.inl ?_⟩
      calc
        _ = (simpleWord 0 [i] * a * (simpleWord 0 [i])⁻¹) * (simpleWord 0 [i] * n) *
            (n⁻¹ * rootGeneratorInGroup 0 (typeF4SimpleRootIndex i) 1 * (n⁻¹)⁻¹) := by group
        _ = _ := by rw [hσ]
    · have hnr := (RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base _).mpr hr
      refine ⟨(simpleWord 0 [i] * a * (simpleWord 0 [i])⁻¹) *
          rootGeneratorInGroup 0 (typeF4SimpleRootIndex i) 1,
        rootGeneratorInGroup 0 (-σ (typeF4SimpleRootIndex i)) 1,
        (splitUnipotent 0).mul_mem hsa hp, subset_closure ⟨_, 1, hnr, rfl⟩, Or.inr ?_⟩
      calc
        _ = (simpleWord 0 [i] * a * (simpleWord 0 [i])⁻¹) *
            (simpleWord 0 [i] * rootGeneratorInGroup 0 (typeF4SimpleRootIndex i) 1) * n := by group
        _ = _ := by
          rw [simpleWord_mul_root]
          have he := hσ (-typeF4SimpleRootIndex i) 1
          rw [hneg, inv_inv] at he
          rw [← he]
          group

end ReeF4.Parabolics.Binary.FixedGeometry.BruhatCoverage
