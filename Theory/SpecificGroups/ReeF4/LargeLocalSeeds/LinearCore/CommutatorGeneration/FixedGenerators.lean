module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.FixedRootFactorization
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.BlockProduct
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates

/-!
# Fixed generators of the linear Ree radical

The linear radical omits the end-node pair from the positive root blocks.
Unique split coordinates make its fixed equation blockwise. The B₂ product
law then eliminates the central parameters, leaving seven main curves.
This establishes generation of the actual fixed subgroup for every local
input, rather than inferring it from generation before taking fixed points.

Source: the root construction underlying Aschbacher–Smith F.1.12(I)(5),
printed pp.263–264; GLS3 §2.3 and Table 2.4.
-/

@[expose] public section
noncomputable section
namespace ReeF4.LargeLocalSeeds.LinearCommutators
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Parabolics Parabolics.RadicalCoordinates Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration Subgroup

private def pairIndex : Fin 3 → Fin 8 := ![1, 5, 3]
private def quartetIndex : Fin 4 → Fin 8 := ![0, 4, 6, 2]

private theorem pair_long (j : Fin 3) :
    ((rootBlocks (.radical .linear)).roots (.inl (j, 0))).val = longRoot (pairIndex j) := by
  apply Subtype.ext
  rw [rootBlocks_roots_val, MatrixRelations.longRoot_eq_sum]
  fin_cases j
  · change (![ 0,1,1,0 ] : Vec 4) = ∑ i : Fin 4, (![ 1,2,2,0 ] : Fin 4 → ℕ) i • typeF4SimpleRoot i
    ext k; fin_cases k <;> norm_num [Fin.sum_univ_four, typeF4SimpleRoot,
      Matrix.cons_val_two, Matrix.cons_val_three]
  · change (![ 1,0,0,-1 ] : Vec 4) = ∑ i : Fin 4, (![ 1,2,2,2 ] : Fin 4 → ℕ) i • typeF4SimpleRoot i
    ext k; fin_cases k <;> norm_num [Fin.sum_univ_four, typeF4SimpleRoot,
      Matrix.cons_val_two, Matrix.cons_val_three]
  · change (![ 1,0,0,1 ] : Vec 4) = ∑ i : Fin 4, (![ 1,2,4,2 ] : Fin 4 → ℕ) i • typeF4SimpleRoot i
    ext k; fin_cases k <;> norm_num [Fin.sum_univ_four, typeF4SimpleRoot,
      Matrix.cons_val_two, Matrix.cons_val_three]


private theorem quartet_long (j : Fin 4) :
    ((rootBlocks (.radical .linear)).roots (.inr (j, 0))).val = longRoot (quartetIndex j) := by
  apply Subtype.ext
  rw [rootBlocks_roots_val, MatrixRelations.longRoot_eq_sum]
  fin_cases j
  · change (![ 0,0,1,-1 ] : Vec 4) = ∑ i : Fin 4, (![ 0,1,0,0 ] : Fin 4 → ℕ) i • typeF4SimpleRoot i
    ext k; fin_cases k <;> norm_num [Fin.sum_univ_four, typeF4SimpleRoot,
      Matrix.cons_val_two, Matrix.cons_val_three]
  · change (![ 1,-1,0,0 ] : Vec 4) = ∑ i : Fin 4, (![ 0,1,2,2 ] : Fin 4 → ℕ) i • typeF4SimpleRoot i
    ext k; fin_cases k <;> norm_num [Fin.sum_univ_four, typeF4SimpleRoot,
      Matrix.cons_val_two, Matrix.cons_val_three]
  · change (![ 0,1,0,-1 ] : Vec 4) = ∑ i : Fin 4, (![ 1,1,0,0 ] : Fin 4 → ℕ) i • typeF4SimpleRoot i
    ext k; fin_cases k <;> norm_num [Fin.sum_univ_four, typeF4SimpleRoot,
      Matrix.cons_val_two, Matrix.cons_val_three]
  · change (![ 0,1,0,1 ] : Vec 4) = ∑ i : Fin 4, (![ 1,1,2,0 ] : Fin 4 → ℕ) i • typeF4SimpleRoot i
    ext k; fin_cases k <;> norm_num [Fin.sum_univ_four, typeF4SimpleRoot,
      Matrix.cons_val_two, Matrix.cons_val_three]


/-- The linear radical consists of three paired blocks and four B₂ blocks. -/
private def layout : RootWordLayout (.radical .linear) := by
  let B := rootBlocks (.radical .linear)
  have hp (j) : (B.roots (.inl (j, 1))).val = shortRoot (pairIndex j) := by
    rw [shortRoot, ← pair_long j, B.pair_dual]
  have hq (j) : (B.roots (.inr (j, 1))).val = shortRoot (quartetIndex j) := by
    rw [shortRoot, ← quartet_long j, B.quartet_dual_zero]
  refine
    { blocks := B, pairIndex := pairIndex, quartetIndex := quartetIndex
      pair_odd := by intro j; fin_cases j <;> decide
      quartet_even := by intro j; fin_cases j <;> decide
      pair_long := pair_long, pair_short := hp
      pair_mixed := ?_, pair_high := ?_
      quartet_long := quartet_long, quartet_short := hq
      quartet_mixed := ?_, quartet_high := ?_ }
  · intro j
    rw [mixedRoot, ← pair_long j, ← hp j]
    apply typeF4RootPairing.reflectionPerm_eq_of_pairing_eq_zero'
    rw [typeF4RootPairing_pairing, B.pair_dot, mul_zero]
  · intro j
    rw [highRoot, ← pair_long j, ← hp j]
    apply typeF4RootPairing.reflectionPerm_eq_of_pairing_eq_zero
    rw [typeF4RootPairing_pairing, B.pair_dot, mul_zero]
  · intro j
    apply Subtype.ext
    rw [MatrixRelations.mixedRoot_eq_add _ (by fin_cases j <;> decide),
      ← quartet_long j, ← hq j]
    exact B.quartet_add j
  · intro j
    apply Subtype.ext
    rw [MatrixRelations.highRoot_eq_add_two _ (by fin_cases j <;> decide),
      ← quartet_long j, ← hq j]
    exact B.quartet_add_two j

private theorem pair_ne_seven (j : Fin 3) : layout.pairIndex j ≠ 7 := by
  fin_cases j <;> decide
private theorem quartet_ne_seven (j : Fin 4) : layout.quartetIndex j ≠ 7 := by
  fin_cases j <;> decide
private theorem covers (i : Fin 8) (hi : i ≠ 7) :
    (∃ j, layout.pairIndex j = i) ∨ (∃ j, layout.quartetIndex j = i) := by
  fin_cases i
  · exact Or.inr ⟨(0 : Fin 4), rfl⟩
  · exact Or.inl ⟨(0 : Fin 3), rfl⟩
  · exact Or.inr ⟨(3 : Fin 4), rfl⟩
  · exact Or.inl ⟨(2 : Fin 3), rfl⟩
  · exact Or.inr ⟨(1 : Fin 4), rfl⟩
  · exact Or.inl ⟨(1 : Fin 3), rfl⟩
  · exact Or.inr ⟨(2 : Fin 4), rfl⟩
  · exact (hi rfl).elim

/-- Every retained main curve lies in the specified split radical. -/
theorem rootWord_mem_radical (m : ℕ) (i : Fin 8) (hi : i ≠ 7) (t : CoefficientField m) :
    rootWord m i t ∈ splitRadical m .linear := by
  rcases covers i hi with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact (layout.pair_root_fixed_mem m (mixedRootCommutation m) j t).2
  · exact (layout.quartet_root_fixed_mem m (mixedRootCommutation m) (b2RootSwap m) j t).2

/-- The eight main words as elements of the actual fixed linear seed. -/
def rootElement {m : ℕ} (d : LocalBlockInput m) (i : Fin 8) (t : CoefficientField m) :
    standardSeed d .linear := by
  have h := positiveRootWordLayout.words_fixed_mem m positiveRootWordLayout.positive_covers
    (mixedRootCommutation m) (b2RootSwap m) i t
  exact ⟨⟨rootWord m i t, (DFunLike.congr_fun d.twist_toMonoidHom_eq _).trans h.1.1⟩,
    splitUnipotent_le_splitSeed m .linear h.1.2⟩

/-- The central parameters, also retained as concrete seed elements. -/
def centralElement {m : ℕ} (d : LocalBlockInput m) (i : Fin 8) (t : CoefficientField m) :
    standardSeed d .linear := by
  have h := positiveRootWordLayout.words_fixed_mem m positiveRootWordLayout.positive_covers
    (mixedRootCommutation m) (b2RootSwap m) i t
  exact ⟨⟨centralWord m i t, (DFunLike.congr_fun d.twist_toMonoidHom_eq _).trans h.2.1⟩,
    splitUnipotent_le_splitSeed m .linear h.2.2⟩

theorem rootElement_mem_radical {m : ℕ} (d : LocalBlockInput m)
    (i : Fin 8) (hi : i ≠ 7) (t : CoefficientField m) :
    rootElement d i t ∈ seedRadical d .linear := rootWord_mem_radical m i hi t

private theorem central_mem_closure (m : ℕ) (i : Fin 8) (hi : i ≠ 7)
    (he : i.val % 2 = 0) (t : CoefficientField m) :
    centralWord m i t ∈ closure {z | ∃ i : Fin 8, i ≠ 7 ∧
      ∃ t : CoefficientField m, z = rootWord m i t} := by
  have hx (a : CoefficientField m) : rootWord m i a ∈
      closure {z | ∃ i : Fin 8, i ≠ 7 ∧ ∃ t : CoefficientField m, z = rootWord m i t} :=
    subset_closure ⟨i, hi, a, rfl⟩
  have heq : centralWord m i t =
      (rootWord m i (1 + t))⁻¹ * (rootWord m i 1 * rootWord m i t) := by
    rw [mainParameterProduct m i he t, inv_mul_cancel_left]
  rw [heq]
  exact mul_mem (inv_mem (hx _)) (mul_mem (hx _) (hx _))

/-- Unconditional fixed-point generation, obtained from unique split coordinates. -/
theorem fixed_radical_mem_closure {m : ℕ} (d : LocalBlockInput m)
    (z : SplitGroup m) (hz : z ∈ splitRadical m .linear) (hf : d.twist z = z) :
    z ∈ closure {z | ∃ i : Fin 8, i ≠ 7 ∧
      ∃ t : CoefficientField m, z = rootWord m i t} := by
  let B := layout.blocks
  obtain ⟨t, ht⟩ := (wordInSubgroup_bijective m B.order).2 ⟨z, hz⟩
  have hw : word m B.order t = z := congrArg Subtype.val ht
  have hfixed : blockTwist m (B.repack m t) = B.repack m t := by
    apply B.blockWord_injective m (wordInSubgroup_bijective m B.order)
    rw [← B.twist_blockWord m (mixedRootCommutation m) (b2RootSwap m),
      ← B.word_eq_blockWord, hw]
    exact (DFunLike.congr_fun d.twist_toMonoidHom_eq z).symm.trans hf
  rw [← hw, B.word_eq_blockWord, layout.blockWord_factorization m
    (mixedRootCommutation m) _ hfixed]
  apply mul_mem
  · apply list_prod_mem
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact subset_closure ⟨layout.pairIndex j, pair_ne_seven j, _, rfl⟩
  · apply list_prod_mem
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact mul_mem (subset_closure ⟨layout.quartetIndex j, quartet_ne_seven j, _, rfl⟩)
      (central_mem_closure m _ (quartet_ne_seven j) (layout.quartet_even j) _)

/-- The seven literal main curves generate the radical inside its linear seed. -/
theorem radical_eq_closure {m : ℕ} (d : LocalBlockInput m) :
    seedRadical d .linear = closure {z | ∃ i : Fin 8, i ≠ 7 ∧
      ∃ t : CoefficientField m, z = rootElement d i t} := by
  apply le_antisymm
  · let C := closure {z | ∃ i : Fin 8, i ≠ 7 ∧ ∃ t : CoefficientField m,
        z = rootElement d i t}
    let j : standardSeed d .linear →* SplitGroup m :=
      d.fixedGroup.subtype.comp (standardSeed d .linear).subtype
    have hj : Function.Injective j := Subtype.val_injective.comp Subtype.val_injective
    have hC : closure {z | ∃ i : Fin 8, i ≠ 7 ∧ ∃ t : CoefficientField m,
        z = rootWord m i t} ≤ C.map j := by
      apply (closure_le _).mpr
      rintro z ⟨i, hi, t, rfl⟩
      exact ⟨rootElement d i t, subset_closure ⟨i, hi, t, rfl⟩, rfl⟩
    intro z hz
    obtain ⟨u, hu, he⟩ := hC (fixed_radical_mem_closure d (j z) hz z.val.property)
    exact hj he ▸ hu
  · apply (closure_le _).mpr
    rintro z ⟨i, hi, t, rfl⟩
    exact rootElement_mem_radical d i hi t

private theorem root_add (m : ℕ) (r : F4Chevalley.Root) (a b : CoefficientField m) :
    rootGeneratorInGroup m r (a + b) = rootGeneratorInGroup m r a * rootGeneratorInGroup m r b :=
  Subtype.ext (F4Chevalley.rootCurve_add r a b)

/-- The paired main curves are additive. -/
theorem rootWord_odd_add (m : ℕ) (i : Fin 8) (hi : i.val % 2 ≠ 0)
    (t u : CoefficientField m) :
    rootWord m i (t + u) = rootWord m i t * rootWord m i u := by
  have hc := mixedRootCommutation m (longRoot i) (shortRoot i)
    (MatrixRelations.longRoot_pos i) (MatrixRelations.shortRoot_pos i)
    (MatrixRelations.longRoot_isLong i) (MatrixRelations.shortRoot_isShort i)
    (by rw [MatrixRelations.rootPair_dot, if_neg hi]) u (rootFieldEnd m (longRoot i) t)
  simp only [rootWord, if_neg hi, mul_one, map_add, root_add]
  exact hc.mul_mul_mul_comm _ _

/-- The central curve of the first B₂ block is additive. -/
theorem centralWord_zero_add (m : ℕ) (t u : CoefficientField m) :
    centralWord m 0 (t + u) = centralWord m 0 t * centralWord m 0 u := by
  have hc : Commute (rootGeneratorInGroup m (highRoot 0) u)
      (rootGeneratorInGroup m (mixedRoot 0) (rootFieldEnd m (longRoot 0) t)) :=
    layout.quartet_top_commute m (mixedRootCommutation m) (0 : Fin 4) u _
  simp only [centralWord, map_add, root_add]
  exact hc.mul_mul_mul_comm _ _

end ReeF4.LargeLocalSeeds.LinearCommutators
