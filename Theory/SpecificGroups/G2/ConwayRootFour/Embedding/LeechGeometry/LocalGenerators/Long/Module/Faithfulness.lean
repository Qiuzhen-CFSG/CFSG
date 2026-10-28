module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Setup
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Module.Model
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Octonion
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Faithfulness of the long local action on the Leech fixed space

For an actual `LocalEmbedding`, the restricted-action kernel has exponent
at most four. Its intersection with the Peirce SL₃(4) block is normal.
Perfectness and simplicity of PSL₃(4) put every proper normal subgroup in
the scalar center, whose elements have cube one; the whole block is excluded
by its permutation matrix of order three. Thus the action is injective on
this block.

The exact octonion graph word gives a two-coset normal form. A nontrivial
cubic scalar is central in the block, while the graph word sends it to its
square. Consequently the graph action cannot coincide with any block action,
which excludes the other coset from the kernel. The proof uses neither
coordinates on the Leech fixed space nor a representation classification.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
the faithfulness step preceding the natural-plus-dual module identification.
The concrete octonion formulas and SL/PSL results are reused from the existing
attributed ATLAS ports; no additional upstream source is copied here.
-/

open Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long
open OctonionLocals
open PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight
@[expose] public noncomputable section

private def twoCosets : Subgroup (Model F) where
  carrier := {g | ∃ A : SL(3,F), g = BlockRealization.blockHom A ∨
    g = BlockRealization.blockHom A * graph}
  one_mem' := ⟨1, Or.inl (map_one _).symm⟩
  mul_mem' := by
    rintro _ _ ⟨A, rfl | rfl⟩ ⟨B, rfl | rfl⟩
    · exact ⟨A * B, Or.inl (map_mul _ _ _).symm⟩
    · exact ⟨A * B, Or.inr (by rw [map_mul, mul_assoc])⟩
    · exact ⟨A * graphTwist B, Or.inr (by rw [map_mul, mul_assoc, graph_block, ← mul_assoc])⟩
    · refine ⟨A * graphTwist B, Or.inl ?_⟩
      rw [map_mul, mul_assoc, ← mul_assoc graph, graph_block, mul_assoc,
        graph_square, mul_one]
  inv_mem' := by
    rintro _ ⟨A, rfl | rfl⟩
    · exact ⟨A⁻¹, Or.inl (map_inv _ _).symm⟩
    · refine ⟨graphTwist A⁻¹, Or.inr ?_⟩
      rw [_root_.mul_inv_rev, inv_eq_of_mul_eq_one_right (graph_square (K := F)), ← map_inv, graph_block]

private theorem normal_form (k : longLocal (F := F)) :
    ∃ A : SL(3,F), k = ModuleModel.blockIn A ∨
      k = ModuleModel.blockIn A * ModuleModel.graphIn := by
  have h : longLocal (F := F) ≤ twoCosets := by
    apply sup_le
    · rintro _ ⟨A, rfl⟩
      exact ⟨A, Or.inl rfl⟩
    · apply Subgroup.zpowers_le.mpr
      exact ⟨1, Or.inr (by rw [map_one, one_mul])⟩
  obtain ⟨A, hA | hA⟩ := h k.property
  · exact ⟨A, Or.inl (Subtype.ext hA)⟩
  · exact ⟨A, Or.inr (Subtype.ext hA)⟩

private theorem blockIn_injective : Function.Injective (ModuleModel.blockIn (F := F)) := by
  intro A B h
  exact block_injective (congrArg Subtype.val h)

private theorem central_cube (A : SL(3,F)) (hA : A ∈ Subgroup.center SL(3,F)) :
    A ^ 3 = 1 := by
  obtain ⟨a, ha, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← he, ← map_pow]
  simpa using congrArg (Matrix.scalar (Fin 3)) ha

private def cycleThree : SL(3,F) :=
  ⟨!![0,1,0;0,0,1;1,0,0], by simp [Matrix.det_fin_three]⟩

private theorem cycleThree_cube : cycleThree ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycleThree, pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val]

private theorem cycleThree_ne : cycleThree ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(3,F) => A.val 0 1) h
  exact one_ne_zero this

private theorem block_kernel_trivial (E : LocalEmbedding) (A : SL(3,F))
    (hA : E.action (ModuleModel.blockIn A) = 1) : A = 1 := by
  let ρ := E.action.comp ModuleModel.blockIn
  let : Theory.GroupTheory.IsQuasisimple SL(3,F) :=
    { toIsPerfect := Atlas.sl_perfect 3 (by omega)
      simple := Atlas.psl_simple_high_rank 3 (by omega) }
  have hp (B : SL(3,F)) (hB : B ∈ ρ.ker) : B ^ 4 = 1 := by
    apply blockIn_injective
    rw [map_pow, map_one]
    exact E.action_kernel_pow_four _ hB
  rcases Theory.GroupTheory.IsQuasisimple.normal_le_center_or_eq_top ρ.ker with hc | ht
  · have h3 := central_cube A (hc hA)
    have h4 := hp A hA
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, h3, one_mul] at h4
    exact h4
  · have h4 := hp cycleThree (by rw [ht]; trivial)
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, cycleThree_cube, one_mul] at h4
    exact (cycleThree_ne h4).elim

private theorem block_action_injective (E : LocalEmbedding) :
    Function.Injective (E.action.comp ModuleModel.blockIn) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  exact fun A hA => block_kernel_trivial E A hA

private def scalarElement (a : F) (ha : a ^ 3 = 1) : SL(3,F) :=
  ⟨Matrix.scalar (Fin 3) a, by simpa using ha⟩

private theorem scalarElement_central (a : F) (ha : a ^ 3 = 1) :
    scalarElement a ha ∈ Subgroup.center SL(3,F) := by
  exact Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨a, by simpa using ha, rfl⟩

private theorem scalarElement_twist (a : F) (ha : a ^ 3 = 1) :
    (ModuleModel.graphTwist (scalarElement a ha)).val = Matrix.scalar (Fin 3) (a ^ 2) := by
  rw [ModuleModel.graphTwist_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarElement, ModuleModel.flip, BlockRealization.cofactor,
      Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.scalar_apply, pow_two]

private theorem exists_cubic_scalar : ∃ a : F, a ≠ 0 ∧ a ≠ 1 ∧ a ^ 3 = 1 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hc : Nat.card Fˣ = 3 := by
    rw [Nat.card_units, show Nat.card F = 4 from GaloisField.card 2 2 (by decide)]
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rw [hc])
  refine ⟨u, u.ne_zero, ?_, ?_⟩
  · intro h
    have he : u = 1 := Units.ext h
    simp [he] at hu
  · have he := pow_orderOf_eq_one u
    rw [hu] at he
    exact congrArg Units.val he

private theorem graph_action_not_block (E : LocalEmbedding) :
    E.action ModuleModel.graphIn ∉ (E.action.comp ModuleModel.blockIn).range := by
  rintro ⟨A, hA⟩
  obtain ⟨a, ha0, ha1, ha3⟩ := exists_cubic_scalar
  let z := scalarElement a ha3
  have hz : A * z = z * A :=
    Subgroup.mem_center_iff.mp (scalarElement_central a ha3) A
  have he := congrArg E.action (ModuleModel.blockIn_graphIn z)
  simp only [map_mul] at he
  rw [← hA] at he
  have he' : z * A = A * ModuleModel.graphTwist z := by
    apply block_action_injective E
    simpa only [MonoidHom.comp_apply, map_mul] using he
  have hzt : z = ModuleModel.graphTwist z := mul_left_cancel (hz.trans he')
  have hscalar := congrArg (fun B : SL(3,F) => B.val 0 0) hzt
  rw [scalarElement_twist] at hscalar
  change a = a ^ 2 at hscalar
  have heq : a * 1 = a * a := by simpa only [mul_one, pow_two] using hscalar
  exact ha1 (mul_left_cancel₀ ha0 heq).symm

/-- The genuine restricted Leech action of the long local subgroup is faithful. -/
theorem LocalEmbedding.action_injective (E : LocalEmbedding) : Function.Injective E.action := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro k hk
  obtain ⟨A, rfl | rfl⟩ := normal_form k
  · rw [block_kernel_trivial E A hk, map_one]
  · exfalso
    apply graph_action_not_block E
    refine ⟨A⁻¹, ?_⟩
    change E.action (ModuleModel.blockIn A * ModuleModel.graphIn) = 1 at hk
    rw [map_mul] at hk
    change E.action (ModuleModel.blockIn A⁻¹) = E.action ModuleModel.graphIn
    rw [map_inv, map_inv]
    exact inv_eq_of_mul_eq_one_right hk

end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long
