module

public import Theory.SpecificGroups.PSL3Even.NonbinaryCentralizer.Models
public import Theory.SpecificGroups.PSL3Even.NonbinaryCentralizer.StandardGeneration
public import Theory.SpecificGroups.PSL3Even.NonbinaryCentralizer.FixedGeneration.Transport
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient
public import Theory.SpecificGroups.PSL3.ExtensionBorel.Linear

/-!
# Field conjugacy preserving the marked PSL₃ unipotent subgroup

An automorphism conjugate to a nontrivial coefficient involution and preserving
upper unipotent matrices admits a conjugator with the same marking. Factor the
original conjugator into linear, field and graph factors. The latter two commute
with the given coefficient action, leaving a strict matrix cocycle
`g = m * σ(m)⁻¹`. Preservation of the literal projective unipotent subgroup
forces `g` to be upper triangular.

Choose a diagonal matrix `D` so that `P = D + g * σ(D)` has nonzero diagonal.
Nontriviality of the coefficient action makes each choice possible, including
in characteristic two. Then `P` is upper triangular and invertible, and the
strict cocycle identity gives `g * σ(P) = P`. Conjugation by `P⁻¹` therefore
preserves the original unipotent subgroup and carries the actor to the original
coefficient action. The transport theorem supplies fixed-group generation.

This discharges the field branch of the generation premise used for
Aschbacher–Smith E.1.14(1), printed p.214, with the definitions E.1.1–6,
printed pp.209–210. The matrix and automorphism conventions are GLS3,
Theorem 2.5.12 and §2.7, `refs/KGroup/GLS3/chapter2.tex`. Degree two is included;
no condition on the size of the fixed subfield is needed.
-/

public section

open scoped MatrixGroups
open Matrix Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.CartanActions Matrix.PSL3.ExtensionBorel
namespace Matrix.PSL3Even.NonbinaryCentralizer
variable {F : Type*} [Field F]

section TriangularDescent
variable [CharP F 2]

private theorem exists_trace_ne_zero (σ : F ≃+* F) (hσ : σ ≠ 1) (d : F) :
    ∃ t : F, t + d * σ t ≠ 0 := by
  by_contra! h
  have hd : d = 1 := by
    have h1 := h 1
    simp only [map_one, mul_one] at h1
    exact (eq_neg_of_add_eq_zero_right h1).trans (CharTwo.neg_eq 1)
  apply hσ
  ext t
  have ht := h t
  rw [hd, one_mul] at ht
  exact (eq_neg_of_add_eq_zero_right ht).trans (CharTwo.neg_eq t)

private theorem triangular_descent (σ : F ≃+* F) (hσ : σ ≠ 1) (hs : σ ^ 2 = 1)
    (g : GL (Fin 3) F) (hg : g ∈ glBorel F)
    (hc : g * GeneralLinearGroup.map σ.toRingHom g = 1) :
    ∃ P : GL (Fin 3) F, P ∈ glBorel F ∧
      g * GeneralLinearGroup.map σ.toRingHom P = P := by
  classical
  choose t ht using fun j : Fin 3 => exists_trace_ne_zero σ hσ (g.val j j)
  let D : Matrix (Fin 3) (Fin 3) F := diagonal t
  let P : Matrix (Fin 3) (Fin 3) F := D + g.val * D.map σ
  have hp (i j : Fin 3) : P i j = (if i = j then t i else 0) + g.val i j * σ (t j) := by
    simp [P, D, Matrix.mul_diagonal, Matrix.diagonal_apply]
  obtain ⟨g10, g20, g21⟩ := hg
  have p10 : P 1 0 = 0 := by simp [hp, g10]
  have p20 : P 2 0 = 0 := by simp [hp, g20]
  have p21 : P 2 1 = 0 := by simp [hp, g21]
  have hdet : det P ≠ 0 := by
    rw [det_fin_three]
    simp only [p10, p20, p21, mul_zero, zero_mul, sub_zero, add_zero]
    exact mul_ne_zero (mul_ne_zero (by simpa [hp] using ht 0)
      (by simpa [hp] using ht 1)) (by simpa [hp] using ht 2)
  refine ⟨GeneralLinearGroup.mkOfDetNeZero P hdet, ⟨p10, p20, p21⟩, ?_⟩
  apply Units.ext
  change g.val * P.map σ = P
  have hss (x : F) : σ (σ x) = x := DFunLike.congr_fun hs x
  have hDD : (D.map σ).map σ = D := by ext i j; exact hss _
  have hgg : g.val * g.val.map σ = 1 := congrArg Units.val hc
  dsimp only [P]
  rw [Matrix.map_add σ (map_add σ), Matrix.map_mul,
    mul_add, ← mul_assoc, hgg, one_mul, hDD, add_comm]

end TriangularDescent

private theorem exists_strict_linear_field [Finite F] {f : ℕ}
    (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (σ : F ≃+* F) (hs : σ ^ 2 = 1)
    (a : MulAut PSL(3,F)) (ha : IsConj a (fieldAction F σ)) :
    ∃ g : GL (Fin 3) F, a = linearConj F g * fieldAction F σ ∧
      g * GeneralLinearGroup.map σ.toRingHom g = 1 := by
  let := BenderSuzuki.MatrixGroups.HermitianForm.finiteFieldAut_isCyclic (E := F)
  have hcomm (τ : F ≃+* F) : Commute (fieldAction F τ) (fieldAction F σ) := by
    change fieldAction F τ * fieldAction F σ = fieldAction F σ * fieldAction F τ
    rw [← map_mul, ← map_mul, IsMulCommutative.is_comm.comm τ σ]
  obtain ⟨b, hb⟩ := isConj_iff.mp ha.symm
  have hstd : b ∈ standard F := by
    rw [standard_eq_top_of_two_power_card F (by omega : 0 < f) hF]
    trivial
  obtain ⟨m, τ, hbform⟩ := NormalizerForm.standard_factorization F
    field_linearConj graph_linearConj_exists field_commute_graph b hstd
  obtain ⟨d, hd, hdc⟩ : ∃ d : MulAut PSL(3,F),
      b = linearConj F m * d ∧ Commute d (fieldAction F σ) := by
    rcases hbform with h | h
    · exact ⟨fieldAction F τ, h, hcomm τ⟩
    · exact ⟨fieldAction F τ * graph F, by simpa only [mul_assoc] using h,
        (hcomm τ).mul_left (field_commute_graph σ).symm⟩
  have hform : a = linearConj F m * fieldAction F σ * (linearConj F m)⁻¹ := by
    rw [← hb, hd]
    calc
      _ = linearConj F m * (d * fieldAction F σ * d⁻¹) * (linearConj F m)⁻¹ := by group
      _ = _ := by rw [hdc.eq, mul_inv_cancel_right]
  refine ⟨m * (GeneralLinearGroup.map σ.toRingHom m)⁻¹, ?_, ?_⟩
  · rw [hform, mul_assoc, ← map_inv, field_linearConj,
      ← mul_assoc, ← map_mul, map_inv]
  · have hss : GeneralLinearGroup.map σ.toRingHom
        (GeneralLinearGroup.map σ.toRingHom m) = m := by
      apply Units.ext
      ext i j
      exact DFunLike.congr_fun hs (m.val i j)
    rw [map_mul, map_inv, hss]
    group

private theorem conjugate_of_descent_matrix (g P : GL (Fin 3) F) (σ : F ≃+* F)
    (hP : g * GeneralLinearGroup.map σ.toRingHom P = P) :
    MulAut.congr (linearConj F P⁻¹) (linearConj F g * fieldAction F σ) = fieldAction F σ := by
  have hcongr : MulAut.congr (linearConj F P⁻¹) (linearConj F g * fieldAction F σ) =
      linearConj F P⁻¹ * (linearConj F g * fieldAction F σ) * linearConj F P := by
    ext x
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.mul_apply]
    rfl
  rw [hcongr, mul_assoc, mul_assoc, field_linearConj, ← mul_assoc,
    ← mul_assoc, ← map_mul, ← map_mul]
  have he : P⁻¹ * g * GeneralLinearGroup.map σ.toRingHom P = 1 := by
    rw [mul_assoc, hP, inv_mul_cancel]
  rw [he, map_one, one_mul]

/-- Conjugacy to the given coefficient involution can be realized while
preserving the literal upper unipotent subgroup. The coefficient involution
in the conclusion is the same `σ` as in the hypothesis. -/
theorem exists_marked_congr_field [Finite F] {f : ℕ}
    (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (σ : F ≃+* F) (hσ : σ ≠ 1) (hs : σ ^ 2 = 1)
    (a : MulAut PSL(3,F)) (ha : IsConj a (fieldAction F σ))
    (hU : (unipotent F).map a.toMonoidHom = unipotent F) :
    ∃ c : MulAut PSL(3,F), MulAut.congr c a = fieldAction F σ ∧
      (unipotent F).map c.toMonoidHom = unipotent F := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨g, rfl, hc⟩ := exists_strict_linear_field hf hF σ hs a ha
  have hg : g ∈ glBorel F := by
    apply NormalizerForm.linearConj_upperTriangular F g
    change (unipotent F).map ((linearConj F g).toMonoidHom.comp
      (fieldAction F σ).toMonoidHom) = unipotent F at hU
    rwa [← Subgroup.map_map, fieldAction_unipotent] at hU
  obtain ⟨P, hPB, hP⟩ := triangular_descent σ hσ hs g hg hc
  exact ⟨linearConj F P⁻¹, conjugate_of_descent_matrix g P σ hP,
    linearConj_preserves F P⁻¹ ((glBorel F).inv_mem hPB)⟩

/-- The field branch of nonbinary fixed-group generation, with the original
marked unipotent subgroup. This includes fields of order four. -/
theorem field_fixed_sup_unipotent_of_isConj [Finite F] {f : ℕ}
    (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (σ : F ≃+* F) (hσ : σ ≠ 1) (hs : σ ^ 2 = 1)
    (a : MulAut PSL(3,F)) (ha : IsConj a (fieldAction F σ))
    (hU : (unipotent F).map a.toMonoidHom = unipotent F) :
    a.fixedSubgroup ⊔ unipotent F = ⊤ := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨c, hc, hcU⟩ := exists_marked_congr_field hf hF σ hσ hs a ha hU
  exact field_fixed_sup_unipotent_of_marked_congr a c σ hc hcU

end Matrix.PSL3Even.NonbinaryCentralizer
