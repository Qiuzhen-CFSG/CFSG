module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.Graph.Model
import Mathlib.Tactic.LinearCombination

/-!
# A dihedral Sylow subgroup of the orthogonal–Frobenius group

For the isotropic vector `v = (1,1,0)`, the matrices `u(c) = I + c v vᵀ`
form an additive root subgroup of the actual inverse-transpose fixed group
in SL₃(4). Entrywise Frobenius carries `u(c)` to `u(c²)`. In the concrete
semidirect product, take the rotation `(u(c), Frobenius)` and reflection
`(1, Frobenius)`. A coefficient outside the fixed field makes the square of
the rotation nonidentity. The dihedral relations therefore give a faithful
map from `DihedralGroup 4`; its order-eight image has odd index fifteen.

This supplies the semilinear Sylow input for the graph-centralizer assembly,
without asserting the separate full-centralizer calculation. Source:
Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.4(6), printed
p.1171, and the quaternion application on printed p.1192 (`refs/quasithin.pdf`).
-/

noncomputable section
open Matrix
open Subgroup
open Matrix.PSL3Four
namespace Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.Graph.SemilinearSylow

private def rootMatrix (c : F) : Matrix (Fin 3) (Fin 3) F :=
  !![1 + c, c, 0; c, 1 + c, 0; 0, 0, 1]

private theorem rootMatrix_det (c : F) : (rootMatrix c).det = 1 := by
  simp [rootMatrix, Matrix.det_fin_three]
  linear_combination c * CharTwo.two_eq_zero (R := F)

private def rootSL (c : F) : SL := ⟨rootMatrix c, rootMatrix_det c⟩

private theorem rootSL_mem (c : F) : rootSL c ∈ Fixed := by
  rw [GraphFixed.mem_graphSL_fixed_iff]
  change (rootMatrix c).transpose * rootMatrix c = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals linear_combination (c + c ^ 2) * CharTwo.two_eq_zero (R := F)

private def root (c : F) : Fixed := ⟨rootSL c, rootSL_mem c⟩

private theorem root_add (c d : F) : root (c + d) = root c * root d := by
  apply Subtype.ext
  apply Subtype.ext
  change rootMatrix (c + d) = rootMatrix c * rootMatrix d
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals linear_combination -(c * d) * CharTwo.two_eq_zero (R := F)

private theorem root_zero : root 0 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [root, rootSL, rootMatrix]

private theorem root_injective : Function.Injective root := by
  intro c d h
  exact congrArg (fun x : Fixed => x.val.val 0 1) h

private theorem root_sq (c : F) : root c ^ 2 = 1 := by
  rw [pow_two, ← root_add, CharTwo.add_self_eq_zero, root_zero]

private theorem frobenius_root (c : F) : fixedFrobenius (root c) = root (fieldFrobenius c) := by
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  change (rootMatrix c i j) ^ 2 = rootMatrix (fieldFrobenius c) i j
  fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, add_sq, CharTwo.two_eq_zero]

-- Adapted from the private normal-form construction in DihedralPresentation.
private def rotationPowers {G : Type*} [Group G] {m : ℕ} [NeZero m]
    (c : G) (hc : c ^ m = 1) : Multiplicative (ZMod m) →* G where
  toFun i := c ^ i.toAdd.val
  map_one' := by simp
  map_mul' i j := by
    change c ^ (i.toAdd + j.toAdd).val = c ^ i.toAdd.val * c ^ j.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod (i.toAdd.val + j.toAdd.val) hc).symm

private def presentationHom {G : Type*} [Group G] {m : ℕ} [NeZero m]
    (c d : G) (hc : c ^ m = 1) (hd : d ^ 2 = 1)
    (hconj : d * c * d⁻¹ = c⁻¹) : DihedralGroup m →* G := by
  let f := rotationPowers c hc
  have hswap (i : Multiplicative (ZMod m)) : f i * d = d * (f i)⁻¹ := by
    have hh : d * f i * d⁻¹ = (f i)⁻¹ := by
      change d * c ^ i.toAdd.val * d⁻¹ = (c ^ i.toAdd.val)⁻¹
      rw [← conj_pow, hconj, inv_pow]
    have dd : d * d = 1 := by simpa [pow_two] using hd
    calc
      f i * d = (d * d) * f i * d := by rw [dd, one_mul]
      _ = d * (d * f i * d⁻¹) := by
        have hi : d⁻¹ = d := inv_eq_of_mul_eq_one_right dd
        rw [hi]
        simp only [mul_assoc]
      _ = d * (f i)⁻¹ := by rw [hh]
  refine {
    toFun := fun x => match x with
      | .r i => f (.ofAdd i)
      | .sr i => d * f (.ofAdd i)
    map_one' := by change f 1 = 1; exact f.map_one
    map_mul' := ?_ }
  intro x y
  cases x with
  | r i =>
    cases y with
    | r j => exact f.map_mul (.ofAdd i) (.ofAdd j)
    | sr j =>
      change d * f (.ofAdd (j - i)) = f (.ofAdd i) * (d * f (.ofAdd j))
      rw [← mul_assoc, hswap, mul_assoc]
      rw [sub_eq_add_neg]
      change d * f ((.ofAdd j) * (.ofAdd i)⁻¹) = d * ((f (.ofAdd i))⁻¹ * f (.ofAdd j))
      rw [map_mul, map_inv]
      congr 1
      simpa only [map_inv] using (Commute.map (Commute.all (.ofAdd j) ((.ofAdd i)⁻¹)) f).eq
  | sr i =>
    cases y with
    | r j =>
      change d * f ((.ofAdd i) * (.ofAdd j)) = d * f (.ofAdd i) * f (.ofAdd j)
      rw [map_mul, mul_assoc]
    | sr j =>
      change f (.ofAdd (j - i)) = (d * f (.ofAdd i)) * (d * f (.ofAdd j))
      rw [mul_assoc d, ← mul_assoc (f (.ofAdd i)), hswap, ← mul_assoc d, ← mul_assoc d d]
      have dd : d * d = 1 := by simpa [pow_two] using hd
      rw [dd, one_mul]
      rw [sub_eq_add_neg]
      change f ((.ofAdd j) * (.ofAdd i)⁻¹) = (f (.ofAdd i))⁻¹ * f (.ofAdd j)
      rw [map_mul, map_inv]
      simpa only [map_inv] using (Commute.map (Commute.all (.ofAdd j) ((.ofAdd i)⁻¹)) f).eq


private abbrev fieldGenerator : C2 := Multiplicative.ofAdd (1 : ZMod 2)

private def turn (c : F) : Semilinear := ⟨root c, fieldGenerator⟩
private def reflection : Semilinear := SemidirectProduct.inr fieldGenerator

private theorem turn_sq (c : F) :
    turn c ^ 2 = SemidirectProduct.inl (root (c + fieldFrobenius c)) := by
  rw [pow_two]
  apply SemidirectProduct.ext
  · change root c * fixedFieldAction fieldGenerator (root c) = root (c + fieldFrobenius c)
    rw [fixedFieldAction, involutionHom_generator, frobenius_root, root_add]
  · change (fieldGenerator * fieldGenerator : C2) = 1
    decide

private theorem turn_four (c : F) : turn c ^ 4 = 1 := by
  rw [show 4 = 2 * 2 by decide, pow_mul, turn_sq, ← map_pow, root_sq, map_one]

private theorem reflection_sq : reflection ^ 2 = 1 := by
  change SemidirectProduct.inr fieldGenerator ^ 2 = (1 : Semilinear)
  rw [← map_pow]
  exact map_one _

private theorem reflection_conj_turn (c : F) :
    reflection * turn c * reflection⁻¹ = (turn c)⁻¹ := by
  have hi : (SemidirectProduct.inl (root c) : Semilinear)⁻¹ =
      SemidirectProduct.inl (root c) := by
    rw [← map_inv]
    congr 1
    exact inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using root_sq c)
  have hs : reflection⁻¹ = reflection :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using reflection_sq)
  have he : turn c = SemidirectProduct.inl (root c) * reflection :=
    SemidirectProduct.mk_eq_inl_mul_inr _ _
  rw [he, _root_.mul_inv_rev, hi]
  simp only [mul_assoc, mul_inv_cancel, mul_one]
  rw [hs]

private def dihedralHom (c : F) : DihedralGroup 4 →* Semilinear :=
  presentationHom (turn c) reflection (turn_four c) reflection_sq (reflection_conj_turn c)

private theorem dihedralHom_central (c : F) :
    dihedralHom c (.r 2) = SemidirectProduct.inl (root (c + fieldFrobenius c)) := by
  change turn c ^ 2 = _
  exact turn_sq c

private theorem dihedralHom_injective (c : F) (hc : fieldFrobenius c ≠ c) :
    Function.Injective (dihedralHom c) := by
  have hn : dihedralHom c (.r 2) ≠ 1 := by
    rw [dihedralHom_central]
    intro h
    have hroot : root (c + fieldFrobenius c) = root 0 := by
      rw [root_zero]
      exact SemidirectProduct.inl_injective (h.trans (map_one _).symm)
    have he := root_injective hroot
    apply hc
    simpa only [← add_assoc, CharTwo.add_self_eq_zero, zero_add, add_zero] using
      congrArg (c + ·) he
  have hcases : ∀ d : DihedralGroup 4, d = 1 ∨ d = .r 2 ∨
      d * d = .r 2 ∨ (.r 1 * d * (.r 1)⁻¹) * d⁻¹ = .r 2 := by decide +kernel
  apply (MonoidHom.ker_eq_bot_iff (dihedralHom c)).mp
  apply eq_bot_iff.mpr
  intro d hd
  have hfd : dihedralHom c d = 1 := hd
  rcases hcases d with h1 | h2 | hsq | hcomm
  · exact h1
  · exact (hn (h2 ▸ hfd)).elim
  · apply False.elim
    apply hn
    rw [← hsq, map_mul, hfd, one_mul]
  · apply False.elim
    apply hn
    rw [← hcomm, map_mul, map_mul, map_mul, map_inv, map_inv, hfd]
    simp

end Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.Graph.SemilinearSylow

namespace Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.Graph

/-- The actual orthogonal group extended by entrywise Frobenius has a dihedral
Sylow two-subgroup of order eight. -/
public theorem exists_semilinear_sylow :
    ∃ S : Sylow 2 Semilinear, Nonempty (S ≃* DihedralGroup 4) := by
  obtain ⟨c, hc⟩ := exists_fieldFrobenius_ne
  let f := SemilinearSylow.dihedralHom c
  let e : DihedralGroup 4 ≃* f.range :=
    MonoidHom.ofInjective (SemilinearSylow.dihedralHom_injective c hc)
  have hcard : Nat.card f.range = 2 ^ 3 := by
    rw [← Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    norm_num
  have hp : IsPGroup 2 f.range := IsPGroup.of_card hcard
  have hi : ¬ 2 ∣ f.range.index := by
    have h := f.range.card_mul_index
    rw [hcard, semilinear_card] at h
    have hi : f.range.index = 15 := by omega
    rw [hi]
    decide
  exact ⟨hp.toSylow hi, ⟨e.symm⟩⟩

end Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.Graph
