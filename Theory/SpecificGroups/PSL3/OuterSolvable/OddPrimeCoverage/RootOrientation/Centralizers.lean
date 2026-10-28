module

public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.RootOrientation.Signs

/-!
# Recovering coordinate roots from diagonal involutions

Conjugation by a diagonal sign matrix changes the signs of two of the
three unitriangular coordinates. In odd characteristic its fixed subgroup
is exactly the remaining root. Inverse transpose gives the opposite root.
Among the positive roots, only the highest root centralizes the whole
unitriangular group; this distinguishes the middle label of the diagram.

All equalities hold in the actual PSL₃ quotient, using the faithful
unitriangular embedding, without a trace calculation or division by three.
Source: GLS3, Theorem 2.5.12(a) and §2.7,
`refs/KGroup/GLS3/chapter2.tex`, lines 1111–1115.
-/

public section

open scoped MatrixGroups
open Matrix Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.OuterSolvable.OddPrimeCoverage
variable {F : Type*} [Field F]

private def signedU (k : Fin 3) (u : U F) : U F :=
  ⟨if k = 2 then u.x else -u.x, if k = 0 then u.y else -u.y,
    if k = 1 then u.c else -u.c⟩

private theorem sign_conj_projective (k : Fin 3) (u : U F) :
    signElement k * projective F u * signElement k = projective F (signedU k u) := by
  have he : signSL k * specialLinear F u * signSL k = specialLinear F (signedU k u) := by
    apply Subtype.ext
    change Matrix.diagonal (fun i => if i = k then (1 : F) else -1) * matrix F u *
      Matrix.diagonal (fun i => if i = k then (1 : F) else -1) = matrix F (signedU k u)
    ext i j
    fin_cases k <;> fin_cases i <;> fin_cases j <;>
      simp [matrix, signedU, Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact congrArg (projection F) he

private theorem projective_commutes_sign_iff (k : Fin 3) (u : U F) :
    projective F u * signElement k = signElement k * projective F u ↔ u = signedU k u := by
  have hs : signElement (F := F) k * signElement k = 1 := by
    simpa only [pow_two] using signElement_sq (F := F) k
  calc
    _ ↔ (projective F u * signElement k) * signElement k =
        (signElement k * projective F u) * signElement k := (mul_left_inj _).symm
    _ ↔ projective F u = projective F (signedU k u) := by
      rw [mul_assoc (projective F u), hs, mul_one, sign_conj_projective]
    _ ↔ u = signedU k u := (projective_injective F).eq_iff

private def rootU (k : Fin 3) (a : F) : U F :=
  ⟨if k = 2 then a else 0, if k = 0 then a else 0, if k = 1 then a else 0⟩

private theorem projective_rootU (k : Fin 3) (a : F) :
    projective F (rootU k a) = rootElement (rootFirst_ne_second k) a := by
  apply congrArg (QuotientGroup.mk : SL(3,F) → PSL(3,F))
  apply Subtype.ext
  change matrix F (rootU k a) = 1 + Matrix.single (rootFirst k) (rootSecond k) a
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [rootU, matrix, rootFirst, rootSecond]

private theorem self_eq_neg_iff (h2 : (2 : F) ≠ 0) (a : F) : a = -a ↔ a = 0 := by
  constructor
  · intro ha
    have h : (2 : F) * a = 0 := by linear_combination ha
    exact (mul_eq_zero.mp h).resolve_left h2
  · rintro rfl; simp

private theorem signedU_fixed (h2 : (2 : F) ≠ 0) (k : Fin 3) (u : U F) :
    u = signedU k u ↔ ∃ a, u = rootU k a := by
  rw [U.ext_iff]
  fin_cases k <;> simp [signedU, self_eq_neg_iff h2]
  · constructor
    · rintro ⟨hx, hc⟩
      exact ⟨u.y, U.ext hx rfl hc⟩
    · rintro ⟨a, rfl⟩; simp [rootU]
  · constructor
    · rintro ⟨hx, hy⟩
      exact ⟨u.c, U.ext hx hy rfl⟩
    · rintro ⟨a, rfl⟩; simp [rootU]
  · constructor
    · rintro ⟨hy, hc⟩
      exact ⟨u.x, U.ext rfl hy hc⟩
    · rintro ⟨a, rfl⟩; simp [rootU]

/-- A sign involution fixes precisely the root whose indices omit its marked
coordinate, inside the upper unitriangular subgroup. -/
theorem upper_inf_centralizer_sign (h2 : (2 : F) ≠ 0) (k : Fin 3) :
    upperUnipotent F ⊓ Subgroup.centralizer {signElement k} = positiveRoot k := by
  ext x
  constructor
  · rintro ⟨hx,hc⟩
    rw [upperUnipotent, ← projective_range] at hx
    obtain ⟨u,rfl⟩ := hx
    have hu := (projective_commutes_sign_iff k u).mp
      (Subgroup.mem_centralizer_singleton_iff.mp hc)
    obtain ⟨a,rfl⟩ := (signedU_fixed h2 k u).mp hu
    rw [projective_rootU]
    exact rootElement_mem _ _
  · rintro ⟨a,rfl⟩
    change rootElement (rootFirst_ne_second k) a.toAdd ∈ _
    rw [← projective_rootU]
    constructor
    · rw [upperUnipotent, ← projective_range]
      exact ⟨rootU k a.toAdd,rfl⟩
    · apply Subgroup.mem_centralizer_singleton_iff.mpr
      apply (projective_commutes_sign_iff _ _).mpr
      exact (signedU_fixed h2 k _).mpr ⟨a.toAdd,rfl⟩

private theorem graph_positiveRoot (k : Fin 3) :
    (positiveRoot (F := F) k).map (graph F).toMonoidHom = negativeRoot k := by
  ext x
  constructor
  · rintro ⟨y, ⟨a,rfl⟩,rfl⟩
    exact ⟨Multiplicative.ofAdd (-a.toAdd), (graph_rootElement _ _).symm⟩
  · rintro ⟨a,rfl⟩
    refine ⟨rootElement (rootFirst_ne_second k) (-a.toAdd), rootElement_mem _ _, ?_⟩
    change graph F (rootElement _ _) = rootElement _ _
    rw [graph_rootElement, neg_neg]

/-- The same sign involution cuts out the opposite root in the lower subgroup. -/
theorem lower_inf_centralizer_sign (h2 : (2 : F) ≠ 0) (k : Fin 3) :
    lowerUnipotent F ⊓ Subgroup.centralizer {signElement k} = negativeRoot k := by
  have h := congrArg (fun H : Subgroup PSL(3,F) => H.map (graph F).toMonoidHom)
    (upper_inf_centralizer_sign h2 k)
  rw [map_inf_centralizer_singleton, graph_signElement, graph_positiveRoot] at h
  exact h

/-- Among the three positive coordinate roots, only the highest root
centralizes the entire upper unitriangular group. -/
theorem positiveRoot_central_iff (k : Fin 3) :
    positiveRoot (F := F) k ≤ Subgroup.centralizer (upperUnipotent F : Set PSL(3,F)) ↔
      k = 1 := by
  have hc (a : F) : rootElement (rootFirst_ne_second k) a ∈
      Subgroup.centralizer (upperUnipotent F : Set PSL(3,F)) ↔ rootU k a ∈ Subgroup.center (U F) := by
    rw [← projective_rootU, Subgroup.mem_center_iff]
    constructor
    · intro h u
      apply projective_injective F
      simp only [map_mul]
      exact h (projective F u) (by rw [upperUnipotent, ← projective_range]; exact ⟨u,rfl⟩)
    · intro h x hx
      rw [upperUnipotent, ← projective_range] at hx
      obtain ⟨u,rfl⟩ := hx
      simpa only [map_mul] using congrArg (projective F) (h u)
  constructor
  · intro h
    have hz := (hc 1).mp (h (rootElement_mem _ _))
    rw [← Z_eq_center, mem_Z] at hz
    fin_cases k <;> simp_all [rootU]
  · rintro rfl x ⟨a,rfl⟩
    apply (hc a.toAdd).mpr
    rw [← Z_eq_center, mem_Z]
    simp [rootU]

end Matrix.PSL3.OuterSolvable.OddPrimeCoverage
