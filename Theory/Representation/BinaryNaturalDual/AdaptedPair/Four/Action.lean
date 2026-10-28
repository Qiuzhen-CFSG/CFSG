module

public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Geometry

/-!
# Coordinate actors for the four-dimensional adapted pair

The natural-plus-dual specification is faithful on the actual automorphism
group. Thus the coordinate formulas for the reversal-twisted graph actor
prove its involution identity in that group. Elementary upper transvections
preserve the actual coordinate flag. The standard upper group fixes e₁ and
e₄*, and the specified outer involution fixes the nonsingular adapted pair.

Source: Aschbacher–Smith, H.9.1(4), printed p.390, with the corrected
adapted-pair choice described in the source audit of 6 October 2026.
-/

@[expose] public section

open BinaryNaturalDual BinaryLinear.OuterCyclic
namespace BinaryNaturalDual.AdaptedPair.Four

theorem dual_ext {n : ℕ} {f h : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)}
    (he : ∀ i, f (axis i) = h (axis i)) : f = h :=
  (Pi.basisFun (ZMod 2) (Fin n)).ext (by simpa only [Pi.basisFun_apply, axis] using he)

theorem linearAction_injective {n : ℕ} (d : CoordinateAction n) :
    Function.Injective (linearAction d) := by
  intro a b hab
  have hconj (c : MulAut (LinearGroup n)) (g : LinearGroup n) :
      MulAut.conj (c g) = c * MulAut.conj g * c⁻¹ := by
    ext x
    simp [MulAut.mul_apply, MulAut.conj_apply]
  ext g x i
  have he : linearAction d (MulAut.conj (a g)) = linearAction d (MulAut.conj (b g)) := by
    rw [hconj, hconj, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hab]
  have hv := congrArg (fun t : CoordinateSpace n ≃ₗ[ZMod 2] CoordinateSpace n =>
    (t (x, 0)).1 i) he
  simpa only [linearAction_inner, BinaryLinear.NaturalDualFlag.action_fst] using hv

/-- The specified natural action also detects each inner actor uniquely. -/
theorem conj_injective {n : ℕ} (d : CoordinateAction n) :
    Function.Injective (MulAut.conj : LinearGroup n →* MulAut (LinearGroup n)) := by
  intro g h he
  ext x i
  have hh := congrArg (fun a : MulAut (LinearGroup n) =>
    (linearAction d a (x, 0)).1 i) he
  simpa only [linearAction_inner, BinaryLinear.NaturalDualFlag.action_fst] using hh

theorem linearAction_tau_fst {n : ℕ} (d : CoordinateAction n) (v : CoordinateSpace n)
    (i : Fin n) : (linearAction d (tau n) v).1 i = v.2 (axis i.rev) := by
  change (linearAction d (MulAut.conj (reversal n) * graphLinear n) v).1 i = _
  rw [map_mul, LinearEquiv.mul_apply, linearAction_inner,
    BinaryLinear.NaturalDualFlag.action_fst]
  change (d.representation (graphLinear n) v).1 i.rev = _
  rw [d.on_graph, coordinateSwap_apply]
  rfl

theorem linearAction_tau_snd_axis {n : ℕ} (d : CoordinateAction n) (v : CoordinateSpace n)
    (i : Fin n) : (linearAction d (tau n) v).2 (axis i) = v.1 i.rev := by
  have hr : (reversal n).symm (axis i) = axis i.rev := by
    ext j
    have he : j.rev = i ↔ j = i.rev := by
      constructor <;> intro h <;> simpa using congrArg Fin.rev h
    simp [reversal, axis, Pi.single_apply, he]
  change (linearAction d (MulAut.conj (reversal n) * graphLinear n) v).2 (axis i) = _
  rw [map_mul, LinearEquiv.mul_apply, linearAction_inner,
    BinaryLinear.NaturalDualFlag.action_snd, hr]
  change (d.representation (graphLinear n) v).2 (axis i.rev) = _
  rw [d.on_graph, coordinateSwap_apply]
  change dotProduct v.1 (Pi.single i.rev 1) = _
  simp

/-- Reversal after the graph actor exchanges the natural and dual coordinates. -/
theorem linearAction_tau {n : ℕ} (d : CoordinateAction n) (v : CoordinateSpace n) :
    linearAction d (tau n) v =
      (reversal n ((dotProductEquiv (ZMod 2) (Fin n)).symm v.2),
        dotProductEquiv (ZMod 2) (Fin n) (reversal n v.1)) := by
  apply Prod.ext
  · ext i
    exact linearAction_tau_fst d v i
  · apply dual_ext
    intro i
    rw [linearAction_tau_snd_axis]
    change v.1 i.rev = dotProduct (reversal n v.1) (Pi.single i 1)
    simp

theorem tau_sq {n : ℕ} (d : CoordinateAction n) : tau n ^ 2 = 1 := by
  apply linearAction_injective d
  rw [map_pow, map_one, pow_two]
  apply LinearEquiv.ext
  intro v
  apply Prod.ext
  · ext i
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq,
      linearAction_tau_fst, linearAction_tau_snd_axis, Fin.rev_rev]
  · apply dual_ext
    intro i
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq,
      linearAction_tau_snd_axis, linearAction_tau_fst, Fin.rev_rev]

theorem tau_not_inner {n : ℕ} [NeZero n] (d : CoordinateAction n) :
    tau n ∉ innerGroup n := by
  rintro ⟨g, hg⟩
  have he := linearAction_tau_snd_axis d (axis (0 : Fin n), 0) (0 : Fin n).rev
  rw [← hg, linearAction_inner, BinaryLinear.NaturalDualFlag.action_snd] at he
  simp [axis] at he

theorem mem_initialSpace_iff {n k : ℕ} (x : BinaryLinear.OuterCyclic.Space n) :
    x ∈ initialSpace n k ↔ ∀ i : Fin n, k ≤ i.val → x i = 0 := by
  have hs : {x | ∃ i : Fin n, i.val < k ∧ x = axis i} =
      (Pi.basisFun (ZMod 2) (Fin n)) '' {i | i.val < k} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_image, Pi.basisFun_apply, axis]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  rw [initialSpace, hs, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff,
    Pi.basisFun_repr, Set.mem_ofPred_eq]
  constructor
  · intro h i hi
    by_contra hx
    exact (Nat.not_lt_of_ge hi) (h i hx)
  · intro h i hi
    by_contra hk
    exact hi (h i (Nat.le_of_not_gt hk))

/-- The elementary upper transvection I + Eᵢⱼ. -/
def elementary {n : ℕ} (i j : Fin n) (hij : i < j) : LinearGroup n :=
  BinaryLinear.transvection (axis i) (coordinateForm j) (by
    simp [axis, ne_of_gt hij])

theorem elementary_apply {n : ℕ} (i j : Fin n) (hij : i < j)
    (x : BinaryLinear.OuterCyclic.Space n) :
    elementary i j hij x = x + x j • axis i := rfl

theorem elementary_symm_apply {n : ℕ} (i j : Fin n) (hij : i < j)
    (x : BinaryLinear.OuterCyclic.Space n) :
    (elementary i j hij).symm x = x + x j • axis i := rfl

theorem elementary_mem_upperGroup {n : ℕ} (i j : Fin n) (hij : i < j) :
    elementary i j hij ∈ upperGroup n := by
  have hmap (k : ℕ) (x : BinaryLinear.OuterCyclic.Space n)
      (hx : x ∈ initialSpace n k) : elementary i j hij x ∈ initialSpace n k := by
    rw [mem_initialSpace_iff] at hx ⊢
    intro t ht
    rw [elementary_apply]
    by_cases hi : t = i
    · subst t
      have hj : k ≤ j.val := le_trans ht (Fin.le_iff_val_le_val.mp hij.le)
      simp [hx i ht, hx j hj]
    · simp [axis, Ne.symm hi, hx t ht]
  rw [upperGroup, Subgroup.mem_iInf]
  intro k x
  constructor
  · intro hx
    have hh := hmap (k.val + 1) (elementary i j hij x) hx
    have he : elementary i j hij (elementary i j hij x) = x :=
      (elementary i j hij).symm_apply_apply x
    rwa [he] at hh
  · exact hmap _ x

theorem inner_mem_standard {n : ℕ} {g : LinearGroup n} (hg : g ∈ upperGroup n) :
    MulAut.conj g ∈ standardGroup n :=
  (le_sup_left : (upperGroup n).map MulAut.conj ≤ standardGroup n)
    (Subgroup.mem_map_of_mem MulAut.conj hg)

theorem tau_mem_standard (n : ℕ) : tau n ∈ standardGroup n :=
  (le_sup_right : Subgroup.zpowers (tau n) ≤ standardGroup n)
    (Subgroup.mem_zpowers (tau n))

theorem elementary_fixes_iff {n : ℕ} (d : CoordinateAction n)
    (i j : Fin n) (hij : i < j) (v : CoordinateSpace n) :
    linearAction d (MulAut.conj (elementary i j hij)) v = v ↔
      v.1 j = 0 ∧ v.2 (axis i) = 0 := by
  rw [linearAction_inner]
  constructor
  · intro he
    have hx := congrArg (fun w : CoordinateSpace n => w.1 i) he
    have hf := congrArg (fun w : CoordinateSpace n => w.2 (axis j)) he
    rw [BinaryLinear.NaturalDualFlag.action_fst] at hx
    rw [BinaryLinear.NaturalDualFlag.action_snd] at hf
    change v.1 i + v.1 j * axis i i = v.1 i at hx
    change v.2 (axis j + axis j j • axis i) = v.2 (axis j) at hf
    simp only [axis, Pi.single_eq_same, mul_one, one_smul, map_add, add_eq_left] at hx hf
    exact ⟨hx, hf⟩
  · rintro ⟨hx, hf⟩
    apply Prod.ext
    · rw [BinaryLinear.NaturalDualFlag.action_fst]
      change v.1 + v.1 j • axis i = v.1
      rw [hx, zero_smul, add_zero]
    · apply LinearMap.ext
      intro x
      rw [BinaryLinear.NaturalDualFlag.action_snd]
      change v.2 (x + x j • axis i) = v.2 x
      simp [hf]

theorem upper_fixes_axis_zero {g : LinearGroup 4} (hg : g ∈ upperGroup 4) :
    g (axis 0) = axis 0 := by
  have hs (x : BinaryLinear.OuterCyclic.Space 4) :
      x ∈ initialSpace 4 1 ↔ x ∈ Submodule.span (ZMod 2) {axis (0 : Fin 4)} := by
    have hset : {x | ∃ i : Fin 4, i.val < 1 ∧ x = axis i} = {axis (0 : Fin 4)} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, hi, rfl⟩
        have he : i = 0 := by apply Fin.ext; omega
        rw [he]
      · intro he
        exact ⟨0, by decide, he⟩
    rw [initialSpace, hset]
  have haxis : axis (0 : Fin 4) ∈ initialSpace 4 1 :=
    (hs _).mpr (Submodule.mem_span_singleton_self _)
  have hm : g (axis 0) ∈ initialSpace 4 1 :=
    ((Subgroup.mem_iInf.mp hg (0 : Fin 4)) _).mpr haxis
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ((hs _).mp hm)
  have hc0 : c ≠ 0 := by
    intro h
    have hz : g (axis 0) = 0 := by simpa [h] using hc.symm
    have ha : axis (0 : Fin 4) = 0 := g.injective (hz.trans (map_zero g).symm)
    have hh := congrFun ha 0
    simp [axis] at hh
  have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc0
  simpa [hc1] using hc.symm

theorem upper_preserves_last {g : LinearGroup 4} (hg : g ∈ upperGroup 4)
    (x : BinaryLinear.OuterCyclic.Space 4) : (g x) 3 = x 3 := by
  have hs (y : BinaryLinear.OuterCyclic.Space 4) :
      y ∈ initialSpace 4 3 ↔ y 3 = 0 := by
    rw [mem_initialSpace_iff]
    constructor
    · intro h; exact h 3 (by decide)
    · intro h i hi
      have he : i = 3 := by apply Fin.ext; omega
      simpa only [he] using h
  have he : (g x) 3 = 0 ↔ x 3 = 0 := by
    have hh := Subgroup.mem_iInf.mp hg (2 : Fin 4) x
    change g x ∈ initialSpace 4 3 ↔ x ∈ initialSpace 4 3 at hh
    simpa only [hs] using hh
  exact (by decide : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b) _ _ he

theorem upper_fixes_fixedVector (d : CoordinateAction 4) {g : LinearGroup 4}
    (hg : g ∈ upperGroup 4) :
    linearAction d (MulAut.conj g) (fixedVector 4) = fixedVector 4 := by
  rw [linearAction_inner]
  apply Prod.ext
  · rw [BinaryLinear.NaturalDualFlag.action_fst]
    exact upper_fixes_axis_zero hg
  · apply LinearMap.ext
    intro x
    rw [BinaryLinear.NaturalDualFlag.action_snd]
    exact upper_preserves_last ((upperGroup 4).inv_mem hg) x

theorem tau_fixes_fixedVector (d : CoordinateAction 4) :
    linearAction d (tau 4) (fixedVector 4) = fixedVector 4 := by
  apply Prod.ext
  · ext i
    rw [linearAction_tau_fst]
    fin_cases i <;> simp [fixedVector, axis]
  · apply dual_ext
    intro i
    rw [linearAction_tau_snd_axis]
    fin_cases i <;> simp [fixedVector, axis]

theorem fixedVector_mem_fixedVectors_standard (d : CoordinateAction 4) :
    fixedVector 4 ∈ fixedVectors (linearAction d) (standardGroup 4) := by
  have hle : standardGroup 4 ≤ pointStabilizer (linearAction d) (fixedVector 4) := by
    apply sup_le
    · rintro _ ⟨g, hg, rfl⟩
      exact upper_fixes_fixedVector d hg
    · exact Subgroup.zpowers_le.mpr (tau_fixes_fixedVector d)
  exact fun g hg => hle hg

theorem outerFour_eq : outerFour = MulAut.conj (elementary (1 : Fin 4) 2 (by decide)) * tau 4 := rfl

theorem outerFour_mem_standard : outerFour ∈ standardGroup 4 := by
  rw [outerFour_eq]
  exact (standardGroup 4).mul_mem (inner_mem_standard (elementary_mem_upperGroup _ _ _))
    (tau_mem_standard 4)

theorem outerFour_fst (d : CoordinateAction 4) (v : CoordinateSpace 4) (i : Fin 4) :
    (linearAction d outerFour v).1 i =
      v.2 (axis i.rev) + v.2 (axis 1) * axis (1 : Fin 4) i := by
  rw [outerFour_eq, map_mul, LinearEquiv.mul_apply, linearAction_inner]
  rw [BinaryLinear.NaturalDualFlag.action_fst]
  change (linearAction d (tau 4) v).1 i +
    (linearAction d (tau 4) v).1 2 * axis (1 : Fin 4) i = _
  rw [linearAction_tau_fst, linearAction_tau_fst]
  rfl

theorem outerFour_snd_axis (d : CoordinateAction 4) (v : CoordinateSpace 4) (i : Fin 4) :
    (linearAction d outerFour v).2 (axis i) =
      v.1 i.rev + axis i (2 : Fin 4) * v.1 2 := by
  rw [outerFour_eq, map_mul, LinearEquiv.mul_apply, linearAction_inner]
  rw [BinaryLinear.NaturalDualFlag.action_snd]
  change (linearAction d (tau 4) v).2 (axis i + axis i (2 : Fin 4) • axis 1) = _
  simp only [map_add, map_smul, smul_eq_mul, linearAction_tau_snd_axis]
  rfl

theorem outerFour_fixes_vectorFour (d : CoordinateAction 4) :
    linearAction d outerFour vectorFour = vectorFour := by
  apply Prod.ext
  · ext i
    rw [outerFour_fst]
    fin_cases i <;> simp [vectorFour, axis, CharTwo.add_self_eq_zero]
  · apply dual_ext
    intro i
    rw [outerFour_snd_axis]
    fin_cases i <;> simp [vectorFour, axis, CharTwo.add_self_eq_zero]

theorem outerFour_sq (d : CoordinateAction 4) : outerFour ^ 2 = 1 := by
  apply linearAction_injective d
  rw [map_pow, map_one, pow_two]
  apply LinearEquiv.ext
  intro v
  apply Prod.ext
  · ext i
    change (linearAction d outerFour (linearAction d outerFour v)).1 i = v.1 i
    rw [outerFour_fst, outerFour_snd_axis, outerFour_snd_axis]
    fin_cases i <;> simp [axis, CharTwo.add_self_eq_zero, add_assoc]
  · apply dual_ext
    intro i
    change (linearAction d outerFour (linearAction d outerFour v)).2 (axis i) = v.2 (axis i)
    rw [outerFour_snd_axis, outerFour_fst, outerFour_fst]
    fin_cases i <;> simp [axis, CharTwo.add_self_eq_zero, add_assoc]

theorem outerFour_not_inner (d : CoordinateAction 4) : outerFour ∉ innerGroup 4 := by
  intro h
  have he : tau 4 ∈ innerGroup 4 := by
    have hm : MulAut.conj (elementary (1 : Fin 4) 2 (by decide)) ∈ innerGroup 4 := ⟨_, rfl⟩
    have hh := (innerGroup 4).mul_mem ((innerGroup 4).inv_mem hm) h
    simpa only [outerFour_eq, inv_mul_cancel_left] using hh
  exact tau_not_inner d he

end BinaryNaturalDual.AdaptedPair.Four
