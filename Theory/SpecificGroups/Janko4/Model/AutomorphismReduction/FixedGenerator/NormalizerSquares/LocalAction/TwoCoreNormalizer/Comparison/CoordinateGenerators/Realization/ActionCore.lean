module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CoordinateGenerators.Realization.NormalClosure
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CoordinateGenerators.Realization.ActionCore.Irreducible
public import Theory.GroupAction.IrreducibleTwoCoreKernel

/-!
# The local two-core acts trivially on the max2 central quotient

Let H be the concrete `localSubgroup`, N its seed normal closure and t its
central involution. The constructed coordinates on N/⟨t⟩ intertwine the
actual left-conjugation action of H with the raw matrices X and Y. The
rank-one matrix certificate in `ActionCore.Irreducible` proves this action
irreducible, so every normal two-subgroup of H fixes the whole quotient.
In particular O₂(H) lies in the kernel of the actual quotient action.

The proof uses the nonzero fixed-vector theorem for two-groups in
characteristic two, followed by invariance of their fixed subgroup under H.
No identification of N with O₂(H), full-centralizer generation, recognition,
or faithfulness assumption is needed.

Source motivation: GLS3, Table 5.3i, printed p.270, the 2A centralizer and
note 1, `refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreComparison.CoordinateGenerators.Realization
open TwoCoreCentralizerData

/-- The actual action on N/⟨t⟩ has no proper nontrivial invariant subgroup. -/
public theorem quotientAction_irreducible (D : Subgroup OuterImageComparison.CentralQuotient)
    (hinv : ∀ g : OuterImageComparison.quotientAction.range,
      ∀ w, w ∈ D → g • w ∈ D) : D = ⊥ ∨ D = ⊤ := by
  let e := OuterImageComparison.coordinates
  let U : Submodule (ZMod 2) (Fin 12 → ZMod 2) :=
    { carrier := {v | e.symm (Multiplicative.ofAdd v) ∈ D}
      zero_mem' := by change e.symm 1 ∈ D; rw [map_one]; exact D.one_mem
      add_mem' := by
        intro v w hv hw
        change e.symm (Multiplicative.ofAdd v * Multiplicative.ofAdd w) ∈ D
        rw [map_mul]
        exact D.mul_mem hv hw
      smul_mem' := by
        intro a v hv
        have hb : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
        rcases hb a with rfl | rfl
        · simp only [zero_smul, Set.mem_ofPred_eq]
          change e.symm 1 ∈ D
          rw [map_one]
          exact D.one_mem
        · simpa only [one_smul] using hv }
  have stable (g : localSubgroup) (M : TwoCoreLinearModel.Matrix12)
      (ha : ∀ n : localNormalClosure,
        M *ᵥ (e (OuterImageComparison.projection n)).toAdd =
          (e (OuterImageComparison.projection (localNormalClosureAction g n))).toAdd) :
      ∀ v ∈ U, M *ᵥ v ∈ U := by
    have hq (q : OuterImageComparison.CentralQuotient) :
        Multiplicative.ofAdd (M *ᵥ (e q).toAdd) =
          e (OuterImageComparison.quotientAction g q) := by
      obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective OuterImageComparison.centralPowers q
      exact congrArg Multiplicative.ofAdd (ha n)
    intro v hv
    change e.symm (Multiplicative.ofAdd (M *ᵥ v)) ∈ D
    have he := hq (e.symm (Multiplicative.ofAdd v))
    rw [e.apply_symm_apply] at he
    change Multiplicative.ofAdd (M *ᵥ v) = _ at he
    rw [he, e.symm_apply_apply]
    exact hinv ⟨OuterImageComparison.quotientAction g, ⟨g, rfl⟩⟩ _ hv
  rcases ActionCore.raw_invariant_submodule U
    (stable subgroupX rawMatrixX normalClosure_actionX)
    (stable subgroupY rawMatrixY normalClosure_actionY) with hb | ht
  · left
    apply le_bot_iff.mp
    intro q hq
    have hu : (e q).toAdd ∈ U := by
      change e.symm (e q) ∈ D
      rwa [e.symm_apply_apply]
    rw [hb, Submodule.mem_bot] at hu
    apply e.injective
    change e q = e 1
    rw [map_one]
    exact congrArg Multiplicative.ofAdd hu
  · right
    apply top_unique
    intro q _
    have hu : (e q).toAdd ∈ U := by rw [ht]; trivial
    change e.symm (e q) ∈ D at hu
    rwa [e.symm_apply_apply] at hu

/-- The native two-core of H acts trivially on the actual quotient N/⟨t⟩. -/
public theorem localTwoCore_le_quotientAction_ker :
    pCore 2 localSubgroup ≤ OuterImageComparison.quotientAction.ker := by
  let e := OuterImageComparison.coordinates
  let _ : Nontrivial OuterImageComparison.CentralQuotient := e.surjective.nontrivial
  let _ : IsElementaryAbelian 2 OuterImageComparison.CentralQuotient :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := by
        apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        intro q
        apply e.injective
        rw [map_pow, map_one]
        change (2 : ℕ) • (e q).toAdd = 0
        rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
        exact zero_smul (ZMod 2) (e q).toAdd }
  exact irreducible_range_core_le_ker OuterImageComparison.quotientAction
    quotientAction_irreducible

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreComparison.CoordinateGenerators.Realization
