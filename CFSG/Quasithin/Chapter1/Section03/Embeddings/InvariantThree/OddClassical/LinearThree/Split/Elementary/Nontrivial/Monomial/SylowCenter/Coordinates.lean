module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary.Nontrivial.Monomial.CubeLine
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.GroupTheory.CentralCoprimeLiftUnique

/-!
# Coordinate signs in a monomial Sylow subgroup

The normal diagonal sign subgroup has exponent two, so it lies in every
Sylow two-subgroup of the monomial group. Coprime torsion uniqueness through
the full scalar quotient shows that a lift of an element centralizing these
signs is diagonal. Conjugating an explicit signed swap into the given Sylow
supplies an element whose coordinate action is a transposition.

The column-support argument follows the calculation in
`Theory/SpecificGroups/SL3/SplitMonomial/LocalCore/LinearFour.lean`, specialized
here to the published coordinate signs needed for Sylow-center position.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`); the decomposition stabilizer in
GLS3, Theorem 6.5.3(b), `refs/KGroup/GLS3/chapter6.tex`.
-/

public section

open Subgroup Matrix
open scoped MatrixGroups Pointwise

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial.Monomial.SylowCenter

open Matrix.SL3.SplitMonomial Matrix.PSL3.OuterSolvable.OddPrimeCoverage
variable {F : Type*} [Field F]

private theorem column_support (g : linear F) (j : Fin 3) :
    ∃ i, g.val i j ≠ 0 ∧ ∀ r, r ≠ i → g.val r j = 0 := by
  have hstab : g.val • coordinateVectors F = coordinateVectors F :=
    MulAction.mem_stabilizer_iff.mp g.property
  have hv : g.val • Pi.single j (1 : F) ∈ coordinateVectors F := by
    rw [← hstab]
    exact Set.smul_mem_smul_set (single_mem_coordinateVectors F j one_ne_zero)
  change ∃ i, (g.val.val *ᵥ Pi.single j (1 : F)) i ≠ 0 ∧
    ∀ r, r ≠ i → (g.val.val *ᵥ Pi.single j (1 : F)) r = 0 at hv
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hv

/-- A monomial matrix has a permutation as its column support. -/
theorem exists_column_permutation (g : linear F) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ i j, i ≠ σ j → g.val i j = 0 := by
  classical
  let p : Fin 3 → Fin 3 := fun j => (column_support g j).choose
  have hp (j r : Fin 3) (h : r ≠ p j) : g.val r j = 0 :=
    (column_support g j).choose_spec.2 r h
  have hs : Function.Surjective p := by
    intro i
    by_contra h
    have hz (j : Fin 3) : g.val i j = 0 := hp j i (fun he => h ⟨j, he.symm⟩)
    have hh := congrArg (fun A : SpecialLinearGroup (Fin 3) F => A i i)
      (mul_inv_cancel g.val)
    change (g.val.val * (g.val⁻¹).val) i i = (1 : Matrix (Fin 3) (Fin 3) F) i i at hh
    simp only [Matrix.one_apply_eq, Matrix.mul_apply, hz, zero_mul, Finset.sum_const_zero] at hh
    exact zero_ne_one hh
  let σ : Equiv.Perm (Fin 3) := Equiv.ofBijective p
    ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  exact ⟨σ, fun i j hij => hp j i hij⟩


private theorem conjugate_signSL (g : linear F) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ k,
      g.val * signSL k * g.val⁻¹ = signSL (σ k) := by
  obtain ⟨σ, hσ⟩ := exists_column_permutation g
  refine ⟨σ, fun k => ?_⟩
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  change g.val.val * Matrix.diagonal _ = Matrix.diagonal _ * g.val.val
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : i = σ j
  · subst i
    by_cases hjk : j = k
    · subst j; simp
    · simp [hjk, σ.injective.ne hjk]
  · change g.val i j * _ = _ * g.val i j
    rw [hσ i j hij, zero_mul, mul_zero]

private theorem conjugate_signElement (g : projective F) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ k,
      g.val * signElement k * g.val⁻¹ = signElement (σ k) := by
  obtain ⟨x, hx, he⟩ := g.property
  obtain ⟨σ, hσ⟩ := conjugate_signSL (⟨x, hx⟩ : linear F)
  refine ⟨σ, fun k => ?_⟩
  have hh := congrArg (Matrix.PSL3.projection F) (hσ k)
  change Matrix.PSL3.projection F x = g.val at he
  change Matrix.PSL3.projection F x * Matrix.PSL3.projection F (signSL k) *
    (Matrix.PSL3.projection F x)⁻¹ = Matrix.PSL3.projection F (signSL (σ k)) at hh
  rw [he] at hh
  exact hh

/-- The action of the projective monomial group on the three coordinate signs. -/
noncomputable def coordinateAction (h2 : (2 : F) ≠ 0) :
    projective F →* Equiv.Perm (Fin 3) where
  toFun g := (conjugate_signElement g).choose
  map_one' := by
    apply Equiv.ext
    intro k
    apply signElement_injective h2
    simpa using ((conjugate_signElement (1 : projective F)).choose_spec k).symm
  map_mul' g h := by
    apply Equiv.ext
    intro k
    apply signElement_injective h2
    have hg := (conjugate_signElement g).choose_spec
    have hh := (conjugate_signElement h).choose_spec
    have hgh := (conjugate_signElement (g*h)).choose_spec
    change signElement _ = signElement ((conjugate_signElement g).choose ((conjugate_signElement h).choose k))
    rw [← hgh k, ← hg _, ← hh k]
    simp [mul_assoc]

/-- The coordinate permutation is realized by actual conjugation in PSL₃. -/
theorem coordinateAction_spec (h2 : (2 : F) ≠ 0) (g : projective F) (k : Fin 3) :
    g.val * signElement k * g.val⁻¹ = signElement (coordinateAction h2 g k) :=
  (conjugate_signElement g).choose_spec k

private theorem signSL_preserves (k : Fin 3) {v : Fin 3 → F}
    (hv : v ∈ coordinateVectors F) : signSL (F := F) k • v ∈ coordinateVectors F := by
  obtain ⟨i, hi, hv⟩ := hv
  change ∃ i, (Matrix.diagonal (fun r => if r = k then (1 : F) else -1) *ᵥ v) i ≠ 0 ∧ _
  refine ⟨i, ?_, ?_⟩
  · simpa only [Matrix.mulVec_diagonal, Pi.mul_apply] using
      mul_ne_zero (show (if i = k then (1 : F) else -1) ≠ 0 by split_ifs <;> simp) hi
  · intro j hj
    change (Matrix.diagonal (fun r => if r = k then (1 : F) else -1) *ᵥ v) j = 0
    simp [Matrix.mulVec_diagonal, hv j hj]

private theorem signSL_mem (k : Fin 3) : signSL (F := F) k ∈ linear F := by
  change signSL k ∈ MulAction.stabilizer _ (coordinateVectors F)
  rw [MulAction.mem_stabilizer_iff]
  apply Set.Subset.antisymm
  · exact Set.smul_set_subset_iff.mpr (fun _ hv => signSL_preserves k hv)
  · rw [Set.subset_smul_set_iff, signSL_inv]
    exact Set.smul_set_subset_iff.mpr (fun _ hv => signSL_preserves k hv)

private theorem signElement_mem (k : Fin 3) : signElement (F := F) k ∈ projective F :=
  ⟨signSL k, signSL_mem k, rfl⟩

private theorem signElement_mul (i j : Fin 3) :
    signElement (F := F) i * signElement j = 1 ∨
      ∃ k, signElement (F := F) i * signElement j = signElement k := by
  by_cases h : i = j
  · subst j
    exact Or.inl (by simpa only [pow_two] using signElement_sq (F := F) i)
  · right
    have hh : ∃ k, signSL (F := F) i * signSL j = signSL k := by
      fin_cases i <;> fin_cases j
      all_goals try exact (h rfl).elim
      case' «0».«1» => refine ⟨2, ?_⟩
      case' «0».«2» => refine ⟨1, ?_⟩
      case' «1».«0» => refine ⟨2, ?_⟩
      case' «1».«2» => refine ⟨0, ?_⟩
      case' «2».«0» => refine ⟨1, ?_⟩
      case' «2».«1» => refine ⟨0, ?_⟩
      all_goals
        apply Subtype.ext
        change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _
        rw [Matrix.diagonal_mul_diagonal]
        congr 1
        ext r
        fin_cases r <;> simp
    obtain ⟨k, hk⟩ := hh
    exact ⟨k, by simpa only [map_mul, Matrix.PSL3.projection, signElement, QuotientGroup.mk'_apply] using congrArg (Matrix.PSL3.projection F) hk⟩

private def signs : Subgroup (projective F) where
  carrier := {x | x = 1 ∨ ∃ k, x.val = signElement k}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | ⟨i, hi⟩) (rfl | ⟨j, hj⟩)
    · exact Or.inl (one_mul 1)
    · exact Or.inr ⟨j, by simpa using hj⟩
    · exact Or.inr ⟨i, by simpa using hi⟩
    · rcases signElement_mul (F := F) i j with h | ⟨k, hk⟩
      · exact Or.inl (Subtype.ext (by simpa only [Subgroup.coe_mul, Subgroup.coe_one, hi, hj] using h))
      · exact Or.inr ⟨k, by simpa only [Subgroup.coe_mul, hi, hj] using hk⟩
  inv_mem' := by
    rintro a (rfl | ⟨i, hi⟩)
    · exact Or.inl inv_one
    · refine Or.inr ⟨i, ?_⟩
      change a.val⁻¹ = _
      rw [hi]
      exact inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using signElement_sq (F := F) i)

private theorem signs_normal : (signs (F := F)).Normal := by
  constructor
  intro x hx g
  rcases hx with rfl | ⟨k, hk⟩
  · exact Or.inl (by simp)
  · obtain ⟨σ, hσ⟩ := conjugate_signElement g
    exact Or.inr ⟨σ k, by simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hk] using hσ k⟩

private theorem signs_two : IsPGroup 2 (signs (F := F)) := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change x.val.val ^ (2 ^ 1) = 1
  rcases x.property with hx | ⟨k, hk⟩
  · simp [hx]
  · simpa only [hk, pow_one] using signElement_sq (F := F) k

/-- Normality and Sylow maximality put every coordinate sign in the given Sylow. -/
theorem signs_le_sylow [Finite F] (T : Sylow 2 PSL(3,F))
    (hT : (T : Subgroup PSL(3,F)) ≤ projective F) (k : Fin 3) :
    signElement (F := F) k ∈ (T : Subgroup PSL(3,F)) := by
  let := signs_normal (F := F)
  exact signs_two.le_sylow_of_normal (T.subtype hT)
    (show (⟨signElement k, signElement_mem k⟩ : projective F) ∈ signs from Or.inr ⟨k, rfl⟩)

/-- Commuting projective images of involutions lift to commuting matrices. -/
theorem commute_sign_of_projective [Finite F] (x : SL(3,F)) (k : Fin 3)
    (h : Commute (Matrix.PSL3.projection F x) (signElement k)) : Commute x (signSL k) := by
  have hker : IsPGroup 3 (Matrix.PSL3.projection F).ker := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    simpa only [Matrix.PSL3.projection_ker, pow_one] using Matrix.SL3.card_center_dvd_three F
  have he : x * signSL k * x⁻¹ = signSL k :=
    (Matrix.PSL3.projection F).eq_of_map_eq_of_pow_eq_one_of_central_pgroup_ker
      (by rw [Matrix.PSL3.projection_ker]) hker (by decide : Nat.Coprime 3 2)
      (by simpa only [map_mul, map_inv, mul_inv_eq_iff_eq_mul, Matrix.PSL3.projection, signElement, QuotientGroup.mk'_apply] using h.eq)
      (by change (MulAut.conj x (signSL k)) ^ 2 = 1
          rw [← map_pow, signSL_sq, map_one]) (signSL_sq k)
  exact mul_inv_eq_iff_eq_mul.mp he

/-- Centralizing all coordinate signs forces a lift to be diagonal. -/
theorem diagonal_of_commute_signs [Finite F] (h2 : (2 : F) ≠ 0) (x : SL(3,F))
    (h : ∀ k, Commute (Matrix.PSL3.projection F x) (signElement k)) :
    x.val = Matrix.diagonal (fun i => x i i) := by
  ext i j
  by_cases hij : i = j
  · subst j; simp
  · have hh := congrArg (fun A : SL(3,F) => A i j) (commute_sign_of_projective x i (h i)).eq
    change (x.val * Matrix.diagonal (fun r => if r = i then (1 : F) else -1)) i j =
      (Matrix.diagonal (fun r => if r = i then (1 : F) else -1) * x.val) i j at hh
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hh
    simp [Ne.symm hij] at hh
    have hz : x i j = 0 :=
      (mul_eq_zero.mp (show (2 : F) * x i j = 0 by linear_combination -hh)).resolve_left h2
    simpa [Matrix.diagonal_apply, hij] using hz

/-- Interchange the two coordinates different from `k`. -/
@[expose] def swapPerm (k : Fin 3) : Equiv.Perm (Fin 3) :=
  Equiv.swap (rootFirst k) (rootSecond k)

/-- The omitted coordinate is fixed by the transposition. -/
theorem swapPerm_fix (k : Fin 3) : swapPerm k k = k := by fin_cases k <;> decide

private theorem involutory_perm_three (σ : Equiv.Perm (Fin 3)) (hs : σ ^ 2 = 1) (hn : σ ≠ 1) :
    ∃ k, σ = swapPerm k := by
  revert σ
  decide

private theorem swapSL_two_preserves {v : Fin 3 → F} (hv : v ∈ coordinateVectors F) :
    swapSL (F := F) 2 • v ∈ coordinateVectors F := by
  obtain ⟨i, hi, hv⟩ := hv
  change ∃ j, ((swapSL (F := F) 2).val *ᵥ v) j ≠ 0 ∧
    ∀ r, r ≠ j → ((swapSL (F := F) 2).val *ᵥ v) r = 0
  refine ⟨swapPerm 2 i, ?_, ?_⟩
  · fin_cases i <;> simpa [swapPerm, rootFirst, rootSecond, Equiv.swap_apply_def, swapSL,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hi
  · intro r hr
    fin_cases i <;> fin_cases r <;>
      simp_all [swapPerm, rootFirst, rootSecond, Equiv.swap_apply_def, swapSL,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem swapSL_two_mem : swapSL (F := F) 2 ∈ linear F := by
  change swapSL 2 ∈ MulAction.stabilizer _ (coordinateVectors F)
  rw [MulAction.mem_stabilizer_iff]
  apply Set.Subset.antisymm
  · exact Set.smul_set_subset_iff.mpr (fun _ hv => swapSL_two_preserves hv)
  · rw [Set.subset_smul_set_iff, swapSL_inv]
    exact Set.smul_set_subset_iff.mpr (fun _ hv => swapSL_two_preserves hv)

private theorem swap_sign_zero :
    swapSL (F := F) 2 * signSL 0 * (swapSL 2)⁻¹ = signSL 1 := by
  rw [swapSL_inv]
  apply Subtype.ext
  change (swapSL (F := F) 2).val * (signSL 0).val * (swapSL 2).val = (signSL 1).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapSL, signSL, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

/-- A conjugate of the signed swap lies in the actual Sylow and acts as a transposition. -/
theorem sylow_has_transposition [Finite F] (h2 : (2 : F) ≠ 0)
    (T : Sylow 2 PSL(3,F)) (hT : (T : Subgroup PSL(3,F)) ≤ projective F) :
    ∃ (t : projective F) (k : Fin 3), t.val ∈ (T : Subgroup PSL(3,F)) ∧
      coordinateAction h2 t = swapPerm k := by
  let v : projective F := ⟨Matrix.PSL3.projection F (swapSL 2),
    ⟨swapSL 2, swapSL_two_mem, rfl⟩⟩
  have hv2 : v ^ 2 = 1 := by
    apply Subtype.ext
    change Matrix.PSL3.projection F (swapSL 2) ^ 2 = 1
    rw [← map_pow, pow_two, swapSL_sq, map_one]
  have hvact : coordinateAction h2 v ≠ 1 := by
    intro hv
    have he := coordinateAction_spec h2 v 0
    rw [hv] at he
    have hs := congrArg (Matrix.PSL3.projection F) (swap_sign_zero (F := F))
    rw [map_mul, map_mul, map_inv] at hs
    have hh : signElement (F := F) 1 = signElement 0 := hs.symm.trans he
    exact (by decide : (1 : Fin 3) ≠ 0) (signElement_injective h2 hh)
  have hvorder : orderOf v = 2 := orderOf_eq_prime hv2 (fun h => hvact (by rw [h, map_one]))
  obtain ⟨y, hy⟩ := (T.subtype hT).exists_isConj_of_orderOf_eq_prime_pow
    (n := 1) (by simpa using hvorder)
  obtain ⟨g, hg⟩ := isConj_iff.mp hy
  change (MulAut.conj g) v = (y : projective F) at hg
  have hy2 : (y : projective F) ^ 2 = 1 := by rw [← hg, ← map_pow, hv2, map_one]
  have hyact : coordinateAction h2 (y : projective F) ≠ 1 := by
    intro he
    rw [← hg, MulAut.conj_apply, map_mul, map_mul, map_inv] at he
    have hh : coordinateAction h2 v = 1 := by
      apply (MulAut.conj (coordinateAction h2 g)).injective
      exact he.trans (map_one _).symm
    exact hvact hh
  obtain ⟨k, hk⟩ := involutory_perm_three (coordinateAction h2 (y : projective F))
    (by rw [← map_pow, hy2, map_one]) hyact
  exact ⟨y, k, y.property, hk⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial.Monomial.SylowCenter
