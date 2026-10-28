module
public import Theory.SpecificGroups.GL2.ThreeConjugacy
public import Theory.Character.ClassFunction

/-!
# Class functions on the actual group GL₂(3)

The eight conjugacy classes give an extensionality principle and a weighted
scalar-product formula. A trace/determinant classifier partitions the 48
invertible matrices into classes of sizes 1,1,6,8,8,12,6,6; the finite
calculations are kernel checked. Source: Wong (1964), Table 1, p.97.
-/

open Matrix
open scoped BigOperators
namespace Matrix.GeneralLinearGroup
noncomputable section
local notation "G" => GL (Fin 2) (ZMod 3)
local notation "M" => Matrix (Fin 2) (Fin 2) (ZMod 3)

private def matrixIndex (A : M) : Fin 8 :=
  if A = 1 then 0 else if A = -1 then 1 else
  if A 0 0 + A 1 1 = 0 then (if A.det = 1 then 2 else 5) else
  if A.det = 1 then (if A 0 0 + A 1 1 = 2 then 3 else 4) else
  if A 0 0 + A 1 1 = 1 then 6 else 7

public def threeClassIndex (g : G) : Fin 8 := matrixIndex g.val

public def threeMatrixEquiv : G ≃ {A : M // A.det ≠ 0} where
  toFun g := ⟨g.val, g.det_ne_zero⟩
  invFun A := mkOfDetNeZero A.val A.property
  left_inv _ := Units.ext rfl
  right_inv _ := Subtype.ext rfl

private theorem coverage : ∀ A : M, A.det ≠ 0 →
    ∃ B : M, B.det ≠ 0 ∧ B * A = (threeClassRepr (matrixIndex A)).val * B := by
  decide +kernel

public theorem three_isConj_classIndex (g : G) : IsConj g (threeClassRepr (threeClassIndex g)) := by
  obtain ⟨B, hB, h⟩ := coverage g.val g.det_ne_zero
  let b := mkOfDetNeZero B hB
  have heq : b * g = threeClassRepr (threeClassIndex g) * b := Units.ext h
  exact isConj_iff.mpr ⟨b, by rw [heq]; group⟩

public theorem three_classFunction_apply (f : ClassFunction G) (hf : IsClassFunction f) (g : G) :
    f g = f (threeClassRepr (threeClassIndex g)) := by
  obtain ⟨b, hb⟩ := isConj_iff.mp (three_isConj_classIndex g)
  rw [← hb]
  exact (hf g b).symm

public theorem three_classFunction_ext {f h : ClassFunction G}
    (hf : IsClassFunction f) (hh : IsClassFunction h)
    (heq : ∀ i, f (threeClassRepr i) = h (threeClassRepr i)) : f = h := by
  funext g
  rw [three_classFunction_apply f hf, three_classFunction_apply h hh, heq]

private theorem counts : ∀ i : Fin 8,
    (Finset.univ.filter (fun A : M => A.det ≠ 0 ∧ matrixIndex A = i)).card =
      ![1,1,6,8,8,12,6,6] i := by
  decide +kernel

public theorem three_sum_classFunction (f : ClassFunction G) (hf : IsClassFunction f) :
    (∑ g : G, f g) = ∑ i : Fin 8, (![1,1,6,8,8,12,6,6] i : ℂ) * f (threeClassRepr i) := by
  classical
  calc
    _ = ∑ A : {A : M // A.det ≠ 0}, f (threeClassRepr (matrixIndex A.val)) :=
      Fintype.sum_equiv threeMatrixEquiv _ _ (fun g => three_classFunction_apply f hf g)
    _ = ∑ A ∈ Finset.univ.filter (fun A : M => A.det ≠ 0),
        f (threeClassRepr (matrixIndex A)) := by
      symm; exact Finset.sum_subtype _ (by simp) _
    _ = ∑ i : Fin 8, ∑ A ∈ (Finset.univ.filter (fun A : M => A.det ≠ 0)).filter
        (fun A => matrixIndex A = i), f (threeClassRepr (matrixIndex A)) := by
      symm; exact Finset.sum_fiberwise _ matrixIndex _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_congr rfl (fun A hA => by
        rw [(Finset.mem_filter.mp hA).2])]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.filter_filter, counts]
      fin_cases i <;> norm_num

public theorem three_scalarProduct (f h : ClassFunction G)
    (hf : IsClassFunction f) (hh : IsClassFunction h) :
    scalarProduct G f h = (∑ i : Fin 8,
      (![1,1,6,8,8,12,6,6] i : ℂ) * (f (threeClassRepr i) * star (h (threeClassRepr i)))) / 48 := by
  have hc : Nat.card G = 48 := by
    rw [Matrix.card_GL_field]; norm_num [Fin.prod_univ_two]
  unfold scalarProduct
  rw [hc, three_sum_classFunction _ (by intro g b; dsimp; rw [hf g b, hh g b])]
  ring

/-- The central involution is fixed by conjugation. -/
public theorem threeCentral_conj (b : G) : b * threeCentral * b⁻¹ = threeCentral := by
  have h : ∀ A : M, A * threeCentral.val = threeCentral.val * A := by decide +kernel
  have hb : b * threeCentral = threeCentral * b := Units.ext (h b.val)
  rw [hb]; group

/-- Being a cyclic root of the central involution is constant on conjugacy classes. -/
public theorem threeCentral_mem_zpowers_isConj {g h : G} (hc : IsConj g h) :
    threeCentral ∈ Subgroup.zpowers g ↔ threeCentral ∈ Subgroup.zpowers h := by
  have forward {g h : G} (hc : IsConj g h)
      (hm : threeCentral ∈ Subgroup.zpowers g) : threeCentral ∈ Subgroup.zpowers h := by
    obtain ⟨b, rfl⟩ := isConj_iff.mp hc
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hm
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [conj_zpow, hn, threeCentral_conj]⟩
  exact ⟨forward hc, forward hc.symm⟩

end
end Matrix.GeneralLinearGroup
