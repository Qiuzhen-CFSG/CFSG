module

public import Theory.SpecificGroups.Monster.Construction.NOctad.Coordinates

/-!
# The 64-dimensional source block and its coefficients

Every signed octad vector is a signed class vector with its literal even
subset. Thus the 64 orthonormal class vectors span the source block, giving
its basis, dimension, and the coefficient formula by pairing with gamma.
The resulting expansion is on complement classes and does not depend on a
choice of subset representatives.

Source: Aschbacher, *Sporadic Groups*, 29.13(4) and the coordinate expansion
in 30.1, printed pp. 160–163. No triality-transform coefficients are assumed.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NOctad
open LocalC LocalC.ShortFamilies TrialitySpin
open Atlas.Codes Atlas.Fischer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Restrict the actual subset of a source parameter to its octad support. -/
def subsetOfParameters (p : OctadParameters) : EvenSubset (parameterOctad p) :=
  ⟨fun i => p.J i.val, by
    change (∑ i : Support (parameterOctad p), p.J i.val) = 0
    calc
      _ = ∑ i ∈ Finset.univ.filter (fun i => p.c.1.val i ≠ 0), p.J i :=
        (Finset.sum_subtype (p := fun i => p.c.1.val i ≠ 0)
          (F := (inferInstance : Fintype (Support (parameterOctad p))))
          (Finset.univ.filter (fun i => p.c.1.val i ≠ 0))
          (by intro i; simp) p.J).symm
      _ = ∑ i, p.J i := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i _ hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
        exact not_not.mp (mt (p.supported i) (not_not.mpr hi))
      _ = 0 := (even_weight_iff p.J).mp p.even⟩

theorem subsetWord_subsetOfParameters (p : OctadParameters) :
    subsetWord (parameterOctad p) (subsetOfParameters p) = p.J := by
  funext i
  by_cases hi : p.c.1.val i = 0
  · have hj : p.J i = 0 := not_not.mp (mt (p.supported i) (not_not.mpr hi))
    simp [subsetWord, parameterOctad, hi, hj]
  · simp [subsetWord, parameterOctad, subsetOfParameters, hi]

/-- Recovery uses the same subset and the same Parker-loop sign. -/
theorem vector_recover (p : OctadParameters) :
    vector p = classVector (parameterOctad p) p.c.2
      (subsetClass (parameterOctad p) (subsetOfParameters p)) := by
  rw [classVector_mk]
  apply (vector_eq_iff _ _).mpr
  exact ⟨rfl, Or.inl (subsetWord_subsetOfParameters p).symm⟩

theorem span_classVector (c : Octad) :
    Submodule.span ℝ (Set.range (classVector c 0)) = block c := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact classVector_mem_block c 0 a
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    have hc : c = parameterOctad p := Subtype.ext hp.symm
    subst c
    rw [vector_recover]
    rcases bit_cases p.c.2 with hs | hs
    · rw [hs]
      exact Submodule.subset_span ⟨_, rfl⟩
    · rw [hs, classVector_sign]
      apply Submodule.neg_mem
      exact Submodule.subset_span ⟨_, rfl⟩

/-- The standard positively signed vector, in the literal block submodule. -/
def blockVector (c : Octad) (a : SubsetClass c) : block c :=
  ⟨classVector c 0 a, classVector_mem_block c 0 a⟩

theorem blockVector_linearIndependent (c : Octad) : LinearIndependent ℝ (blockVector c) :=
  ((block c).subtype.linearIndependent_iff (v := blockVector c)
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)).mp (classVector_linearIndependent c 0)

theorem span_blockVector (c : Octad) : Submodule.span ℝ (Set.range (blockVector c)) = ⊤ :=
  (Submodule.span_range_subtype_eq_top_iff (block c) (classVector_mem_block c 0)).mpr
    (span_classVector c)

/-- The source orthonormal basis indexed by even subsets modulo complement. -/
def blockBasis (c : Octad) : Module.Basis (SubsetClass c) ℝ (block c) :=
  Module.Basis.mk (blockVector_linearIndependent c) (span_blockVector c).ge

@[simp] theorem blockBasis_apply (c : Octad) (a : SubsetClass c) :
    blockBasis c a = blockVector c a := Module.Basis.mk_apply _ _ a

/-- The dimension in 29.13(4), proved on the actual block in the fixed carrier. -/
theorem block_finrank (c : Octad) : Module.finrank ℝ (block c) = 64 :=
  (Module.finrank_eq_nat_card_basis (blockBasis c)).trans (subsetClass_card c)

theorem gamma_blockVector (c : Octad) (a b : SubsetClass c) :
    gamma (blockVector c a).val (blockVector c b).val = if a = b then 1 else 0 :=
  gamma_classVector c 0 a b

/-- Coefficients of a block vector are its pairings with the actual class vectors. -/
theorem blockBasis_repr (c : Octad) (v : block c) (a : SubsetClass c) :
    (blockBasis c).repr v a = gamma (classVector c 0 a) v.val := by
  have h := congrArg (fun w : block c => gamma (classVector c 0 a) w.val)
    ((blockBasis c).sum_repr v)
  simpa only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
    blockBasis_apply, blockVector, gamma_classVector, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] using h

/-- The exact source-coordinate expansion on the 64 complement classes. -/
theorem block_expansion (c : Octad) (v : Space) (hv : v ∈ block c) :
    v = ∑ a : SubsetClass c, gamma (classVector c 0 a) v • classVector c 0 a := by
  have h := congrArg Subtype.val ((blockBasis c).sum_repr (⟨v, hv⟩ : block c))
  simpa only [Submodule.coe_sum, Submodule.coe_smul, blockBasis_repr,
    blockBasis_apply, blockVector] using h.symm

end Sporadic.Monster.Construction.NOctad
