module

public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Geometry
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups.Sylow

/-!
# Coordinate actors for the five-dimensional adapted pair

The coordinate-flag stabilizer is identified with the existing standard Borel
of GL₅(2), giving its order 1024. The actual representation detects automorphisms
through their conjugation of inner actors. This makes the coordinate identity
τ(x,f) = (Jf,Jx) prove τ² = 1 in the automorphism group itself.

Elementary transvections supply coordinate tests for fixed vectors; the upper
actors and τ fix z = (e₁,e₅*), and τ is an outer actor fixing (e₃,e₃*).
Indices displayed here are one-based, while Lean uses zero-based indices.
The Sylow and semidirect-product assertions are separate proof obligations.

Source: Aschbacher–Smith, H.9.1(4), printed p.390, with the corrected adapted
choice in the source audit of 6 October 2026; consumers 12.1.1 and 12.1.3.
-/

@[expose] public section

open BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveFlagGeometry.SylowOvergroups
namespace BinaryNaturalDual.AdaptedPair.Five

theorem initialSpace_eq_flagSpace (k : Fin 4) :
    initialSpace 5 (k.val + 1) = flagSpace standardBasis k := by
  unfold initialSpace flagSpace
  congr 1
  ext v
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, Nat.le_of_lt_succ hi, by simp [standardBasis, axis]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, Nat.lt_succ_of_le hi, by simp [standardBasis, axis]⟩

theorem initialSpace_five : initialSpace 5 5 = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun (ZMod 2) (Fin 5)).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨i, i.isLt, by simp [axis]⟩

/-- The published full coordinate flag is the existing standard Borel, including
its redundant last cut, which is the whole space. -/
theorem upperGroup_eq_standardBorel : upperGroup 5 = standardBorel := by
  ext g
  simp only [upperGroup, Subgroup.mem_iInf, standardBorel, flagStabilizer,
    Set.mem_univ, iInf_pos]
  constructor
  · intro h i
    simpa only [initialSpace_eq_flagSpace i] using h ⟨i.val, by omega⟩
  · intro h k
    by_cases hk : k.val < 4
    · simpa only [initialSpace_eq_flagSpace ⟨k.val, hk⟩] using h ⟨k.val, hk⟩
    · have he : k.val + 1 = 5 := by omega
      rw [he, initialSpace_five]
      change ∀ v, g v ∈ (⊤ : Submodule (ZMod 2) (BinaryLinear.OuterCyclic.Space 5)) ↔ v ∈ ⊤
      simp

theorem upperGroup_card : Nat.card (upperGroup 5) = 1024 := by
  rw [upperGroup_eq_standardBorel, standardBorel_card]

theorem inner_injective {n : ℕ} (d : CoordinateAction n) : Function.Injective
    (MulAut.conj : LinearGroup n →* MulAut (LinearGroup n)) := by
  intro g h he
  apply LinearEquiv.ext
  intro x
  have hx := congrArg (fun a => (linearAction d a (x, 0)).1) he
  simpa only [linearAction_inner, BinaryLinear.NaturalDualFlag.action_fst] using hx

/-- Faithfulness follows from the natural action and conjugation of inner actors. -/
theorem linearAction_injective {n : ℕ} (d : CoordinateAction n) :
    Function.Injective (linearAction d) := by
  have hin : Function.Injective (fun g : LinearGroup n => linearAction d (MulAut.conj g)) := by
    intro g h he
    apply LinearEquiv.ext
    intro x
    have hx := congrArg (fun a : CoordinateSpace n ≃ₗ[ZMod 2] CoordinateSpace n => (a (x, 0)).1) he
    simpa only [linearAction_inner, BinaryLinear.NaturalDualFlag.action_fst] using hx
  have hc (a : MulAut (LinearGroup n)) (g : LinearGroup n) :
      MulAut.conj (a g) = a * MulAut.conj g * a⁻¹ := by
    ext x
    simp [MulAut.mul_apply, MulAut.conj_apply]
  intro a b he
  apply MulEquiv.ext
  intro g
  apply hin
  change linearAction d (MulAut.conj (a g)) = linearAction d (MulAut.conj (b g))
  rw [hc, hc]
  simp only [map_mul, map_inv, he]

theorem tau_fst {n : ℕ} (d : CoordinateAction n) (v : CoordinateSpace n) (i : Fin n) :
    (linearAction d (tau n) v).1 i = v.2 (axis i.rev) := by
  rw [tau, map_mul, LinearEquiv.mul_apply, linearAction_inner]
  rw [BinaryLinear.NaturalDualFlag.action_fst, linearAction_apply, d.on_graph]
  rfl

theorem reversal_axis {n : ℕ} (i : Fin n) : reversal n (axis i) = axis i.rev := by
  ext j
  simp [axis, Pi.single_apply, Fin.rev_eq_iff]

theorem tau_snd_axis {n : ℕ} (d : CoordinateAction n) (v : CoordinateSpace n) (i : Fin n) :
    (linearAction d (tau n) v).2 (axis i) = v.1 i.rev := by
  rw [tau, map_mul, LinearEquiv.mul_apply, linearAction_inner]
  rw [BinaryLinear.NaturalDualFlag.action_snd, linearAction_apply, d.on_graph]
  change dotProduct v.1 (reversal n (axis i)) = _
  rw [reversal_axis]
  simp [axis]

/-- Reversal-twisted graph action, with the dual identified by the dot product. -/
theorem tau_apply {n : ℕ} (d : CoordinateAction n) (v : CoordinateSpace n) :
    linearAction d (tau n) v =
      (reversal n ((dotProductEquiv (ZMod 2) (Fin n)).symm v.2),
        dotProductEquiv (ZMod 2) (Fin n) (reversal n v.1)) := by
  apply Prod.ext
  · ext i
    rw [tau_fst]
    rfl
  · apply (Pi.basisFun (ZMod 2) (Fin n)).ext
    intro i
    simp only [Pi.basisFun_apply]
    change (linearAction d (tau n) v).2 (axis i) = dotProduct (reversal n v.1) (axis i)
    rw [tau_snd_axis]
    simp [axis]

theorem tau_sq {n : ℕ} (d : CoordinateAction n) : tau n ^ 2 = 1 := by
  apply linearAction_injective d
  rw [map_pow, map_one, pow_two]
  apply LinearEquiv.ext
  intro v
  apply Prod.ext
  · ext i
    simp only [LinearEquiv.mul_apply, tau_fst, tau_snd_axis, Fin.rev_rev]
    rfl
  · apply (Pi.basisFun (ZMod 2) (Fin n)).ext
    intro i
    simp only [Pi.basisFun_apply]
    change (linearAction d (tau n) (linearAction d (tau n) v)).2 (axis i) = v.2 (axis i)
    rw [tau_snd_axis, tau_fst, Fin.rev_rev]

theorem tau_fixes_vectorFive (d : CoordinateAction 5) :
    linearAction d (tau 5) vectorFive = vectorFive := by
  apply Prod.ext
  · ext i
    rw [tau_fst]
    fin_cases i <;> simp [vectorFive, axis, Fin.rev]
  · apply (Pi.basisFun (ZMod 2) (Fin 5)).ext
    intro i
    simp only [Pi.basisFun_apply]
    change (linearAction d (tau 5) vectorFive).2 (axis i) = vectorFive.2 (axis i)
    rw [tau_snd_axis]
    fin_cases i <;> simp [vectorFive, axis, Fin.rev]

/-- The summand exchange cannot be induced by an inner automorphism. -/
theorem tau_not_inner (d : CoordinateAction 5) : tau 5 ∉ innerGroup 5 := by
  rintro ⟨g, hg⟩
  have h := congrArg (fun a => (linearAction d a (0, coordinateForm 0)).1 4) hg
  rw [linearAction_inner, tau_fst] at h
  simp [axis, Fin.rev, BinaryLinear.NaturalDualFlag.action_fst] at h

theorem tau_fixes_fixedVector (d : CoordinateAction 5) :
    linearAction d (tau 5) (fixedVector 5) = fixedVector 5 := by
  apply Prod.ext
  · ext i
    rw [tau_fst]
    fin_cases i <;> simp [fixedVector, axis, Fin.rev]
  · apply (Pi.basisFun (ZMod 2) (Fin 5)).ext
    intro i
    simp only [Pi.basisFun_apply]
    change (linearAction d (tau 5) (fixedVector 5)).2 (axis i) = (fixedVector 5).2 (axis i)
    rw [tau_snd_axis]
    fin_cases i <;> simp [fixedVector, axis, Fin.rev]

/-- The elementary transvection with matrix `I + Eᵢⱼ`. -/
def root (i j : Fin 5) (hij : i ≠ j) : LinearGroup 5 :=
  BinaryLinear.transvection (axis i) (coordinateForm j) (by simp [axis, hij])

theorem root_apply (i j : Fin 5) (hij : i ≠ j) (v : BinaryLinear.OuterCyclic.Space 5) :
    root i j hij v = v + v j • axis i := rfl

theorem root_symm_apply (i j : Fin 5) (hij : i ≠ j) (v : BinaryLinear.OuterCyclic.Space 5) :
    (root i j hij).symm v = v + v j • axis i := rfl

theorem root_mem_upper {i j : Fin 5} (hij : i < j) : root i j hij.ne ∈ upperGroup 5 := by
  rw [upperGroup_eq_standardBorel, mem_standardBorel_iff]
  intro a b hba
  rw [matrix_apply]
  simp only [standardBasis, Pi.basisFun_apply]
  rw [root_apply]
  have hne : b ≠ a := ne_of_lt hba
  have hm : b ≠ j ∨ a ≠ i := by
    by_cases hb : b = j
    · right
      intro ha
      subst a
      subst b
      exact (not_lt_of_ge hij.le) hba
    · exact Or.inl hb
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases hm with hb | ha
  · simp [axis, hne.symm, hb.symm]
  · simp [axis, hne.symm, ha.symm]

/-- A transvection fixer has zero natural j-coordinate and zero dual i-coordinate. -/
theorem root_fixed_coordinates (d : CoordinateAction 5) (i j : Fin 5) (hij : i ≠ j)
    (v : CoordinateSpace 5) (h : linearAction d (MulAut.conj (root i j hij)) v = v) :
    v.1 j = 0 ∧ v.2 (axis i) = 0 := by
  rw [linearAction_inner] at h
  constructor
  · have hh := congrArg (fun w : CoordinateSpace 5 => w.1 i) h
    simp only [BinaryLinear.NaturalDualFlag.action_fst, root_apply,
      Pi.add_apply, Pi.smul_apply, axis, Pi.single_eq_same, smul_eq_mul, mul_one] at hh
    exact add_eq_left.mp hh
  · have hh := congrArg (fun w : CoordinateSpace 5 => w.2 (axis j)) h
    simp only [BinaryLinear.NaturalDualFlag.action_snd, root_symm_apply,
      axis, Pi.single_eq_same, one_smul, map_add] at hh
    exact add_eq_left.mp hh

theorem root_fixes_vectorFive (d : CoordinateAction 5) (i j : Fin 5) (hij : i ≠ j)
    (hi : i ≠ 2) (hj : j ≠ 2) :
    linearAction d (MulAut.conj (root i j hij)) vectorFive = vectorFive := by
  rw [linearAction_inner]
  apply Prod.ext
  · simp [BinaryLinear.NaturalDualFlag.action_fst, root_apply, vectorFive,
      axis, hj]
  · apply LinearMap.ext
    intro x
    rw [BinaryLinear.NaturalDualFlag.action_snd, root_symm_apply]
    change (x + x j • axis i) 2 = x 2
    simp [Pi.add_apply, Pi.smul_apply, axis, hi]

theorem upper_fixes_axis_zero {g : LinearGroup 5} (hg : g ∈ upperGroup 5) :
    g (axis 0) = axis 0 := by
  rw [upperGroup_eq_standardBorel] at hg
  ext i
  have hm : g (axis 0) i = matrix g i 0 := by
    rw [matrix_apply]
    simp [standardBasis, axis]
  rw [hm]
  have hu := (mem_standardBorel_iff g).mp hg
  fin_cases i
  · simpa [axis] using standardBorel_diagonal hg 0
  all_goals simpa [axis] using hu (by decide : (0 : Fin 5) < _)

theorem upper_last_coordinate {g : LinearGroup 5} (hg : g ∈ upperGroup 5)
    (x : BinaryLinear.OuterCyclic.Space 5) : g x 4 = x 4 := by
  rw [upperGroup_eq_standardBorel] at hg
  rw [← matrix_mulVec]
  have hr (j : Fin 5) : matrix g 4 j = if j = 4 then 1 else 0 := by
    have hu := (mem_standardBorel_iff g).mp hg
    fin_cases j
    all_goals first
    | simpa using standardBorel_diagonal hg 4
    | simpa using hu (by decide : (_ : Fin 5) < 4)
  simp [Matrix.mulVec, dotProduct, hr]

theorem upper_fixes_fixedVector (d : CoordinateAction 5) {g : LinearGroup 5}
    (hg : g ∈ upperGroup 5) :
    linearAction d (MulAut.conj g) (fixedVector 5) = fixedVector 5 := by
  rw [linearAction_inner]
  apply Prod.ext
  · rw [BinaryLinear.NaturalDualFlag.action_fst]
    exact upper_fixes_axis_zero hg
  · apply LinearMap.ext
    intro x
    rw [BinaryLinear.NaturalDualFlag.action_snd]
    exact upper_last_coordinate ((upperGroup 5).inv_mem hg) x

theorem fixedVector_mem_fixedVectors (d : CoordinateAction 5) :
    fixedVector 5 ∈ fixedVectors (linearAction d) (standardGroup 5) := by
  change standardGroup 5 ≤ pointStabilizer (linearAction d) (fixedVector 5)
  apply sup_le
  · rintro _ ⟨g, hg, rfl⟩
    exact upper_fixes_fixedVector d hg
  · apply Subgroup.zpowers_le.mpr
    exact tau_fixes_fixedVector d

theorem tau_mem_standard : tau 5 ∈ standardGroup 5 := by
  apply (show Subgroup.zpowers (tau 5) ≤ standardGroup 5 from le_sup_right)
  exact Subgroup.mem_zpowers _

theorem inner_root_mem_standard {i j : Fin 5} (hij : i < j) :
    MulAut.conj (root i j hij.ne) ∈ standardGroup 5 := by
  apply (show (upperGroup 5).map MulAut.conj ≤ standardGroup 5 from le_sup_left)
  exact Subgroup.mem_map_of_mem _ (root_mem_upper hij)


end BinaryNaturalDual.AdaptedPair.Five
