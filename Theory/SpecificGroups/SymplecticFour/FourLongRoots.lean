module
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.RootRecognition.FourAxes
public import Theory.SpecificGroups.SymplecticFour.RootTori

/-!
# Four conjugate long-root subgroups generate symplectic four-space

Use the first hyperbolic root pair, the root along the sum of the two first
basis vectors, and the opposite second-coordinate root. The first pair gives
a diagonal torus. A nontrivial torus weight separates the mixed root into the
second long root and the upper short root; opposition supplies the lower
short root. The existing elementary generation theorem then applies.
All four starting subgroups are literal conjugates of the same long root.

Source: Meierfrankenfeld--Stellmacher (1993), (1.1)(ii)(1), as used in the
symplectic branch of (3.3), printed p.867. The argument requires field order
larger than two, precisely as in that source application.
-/

@[expose] public noncomputable section
open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.FourLongRoots
variable {F : Type*} [Field F] [CharP F 2]

private def mixed (t : F) : Sp F := rootElement 7 1 * rootElement 0 t * rootElement 7 1
private def swapFirst : Sp F := rootElement 0 1 * rootElement 1 1 * rootElement 0 1
private def swapSecond : Sp F := rootElement 2 1 * rootElement 3 1 * rootElement 2 1
private def swapPairs : Sp F := rootElement 6 1 * rootElement 7 1 * rootElement 6 1

private theorem root_inv (r : Fin 8) (t : F) : (rootElement r t)⁻¹ = rootElement r t := by
  apply inv_eq_of_mul_eq_one_right
  rw [RootSubgroup.element_add, CharTwo.add_self_eq_zero, RootSubgroup.element_zero]

private theorem mixed_matrix (t : F) : (mixed t).val =
    fromBlocks 1 !![t,t;t,t] 0 1 := by
  change rootMatrix 7 1 * rootMatrix 0 t * rootMatrix 7 1 = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.fromBlocks, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private theorem diagonal_word (u : Fˣ) :
    (rootElement 0 (u : F) * rootElement 1 (↑u⁻¹ : F) * rootElement 0 (u : F)) *
      swapFirst = diagonalTorus u 1 := by
  apply Subtype.ext
  change (rootMatrix 0 (u : F) * rootMatrix 1 (↑u⁻¹ : F) * rootMatrix 0 (u : F)) *
      (rootMatrix 0 1 * rootMatrix 1 1 * rootMatrix 0 1) = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.fromBlocks, diagonalTorus, Matrix.diagonal,
      CharTwo.add_self_eq_zero]

omit [CharP F 2] in
private theorem upper_matrix (a b c : F) :
    rootMatrix 0 a * rootMatrix 2 b * rootMatrix 4 c =
      fromBlocks 1 !![a,c;c,b] 0 1 := by
  simp [rootMatrix, Matrix.fromBlocks_multiply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single]

private theorem diagonal_mixed (u : Fˣ) (t : F) :
    diagonalTorus u 1 * mixed t =
      (rootElement 0 ((u : F)^2*t) * rootElement 2 t * rootElement 4 ((u : F)*t)) *
        diagonalTorus u 1 := by
  apply Subtype.ext
  change (diagonalTorus u 1).val * (mixed t).val =
    (rootMatrix 0 ((u : F)^2*t) * rootMatrix 2 t * rootMatrix 4 ((u : F)*t)) * _
  rw [mixed_matrix, upper_matrix]
  ext i j
  simp only [diagonalTorus, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.fromBlocks, pow_two, mul_assoc, mul_comm]

private theorem extract_short (u t : F) :
    (rootElement 0 (u^2*t) * rootElement 2 t * rootElement 4 (u*t)) *
      mixed t * rootElement 0 ((u^2+1)*t) = rootElement 4 ((u+1)*t) := by
  apply Subtype.ext
  change (rootMatrix 0 (u^2*t) * rootMatrix 2 t * rootMatrix 4 (u*t)) *
      (mixed t).val * rootMatrix 0 ((u^2+1)*t) = rootMatrix 4 ((u+1)*t)
  rw [upper_matrix, mixed_matrix]
  simp only [rootMatrix, Matrix.cons_val_zero,
    Matrix.fromBlocks_multiply, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.single, add_mul, CharTwo.add_self_eq_zero, add_comm]

private theorem extract_second (t : F) :
    rootElement 0 t * mixed t * rootElement 4 t = rootElement 2 t := by
  apply Subtype.ext
  change rootMatrix 0 t * (mixed t).val * rootMatrix 4 t = rootMatrix 2 t
  rw [mixed_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.fromBlocks, CharTwo.add_self_eq_zero]

private theorem opposition_word : swapFirst * swapSecond = TwoConjugate.opposition (F := F) := by
  apply Subtype.ext
  change (rootMatrix 0 1 * rootMatrix 1 1 * rootMatrix 0 1) *
    (rootMatrix 2 1 * rootMatrix 3 1 * rootMatrix 2 1) = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.fromBlocks, TwoConjugate.opposition,
      CharTwo.add_self_eq_zero]

private theorem first_conjugate (t : F) :
    swapFirst * rootElement 0 t * swapFirst⁻¹ = rootElement 1 t := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (rootMatrix 0 1 * rootMatrix 1 1 * rootMatrix 0 1) * rootMatrix 0 t =
    rootMatrix 1 t * (rootMatrix 0 1 * rootMatrix 1 1 * rootMatrix 0 1)
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.fromBlocks, CharTwo.add_self_eq_zero]

private theorem swapPairs_matrix : (swapPairs (F := F)).val =
    fromBlocks !![0,1;1,0] 0 0 !![0,1;1,0] := by
  change rootMatrix 6 1 * rootMatrix 7 1 * rootMatrix 6 1 = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.fromBlocks, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private theorem last_conjugate (t : F) :
    (TwoConjugate.opposition * swapPairs) * rootElement 0 t *
      (TwoConjugate.opposition * swapPairs)⁻¹ = rootElement 3 t := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (TwoConjugate.opposition (F := F)).val * (swapPairs (F := F)).val *
    rootMatrix 0 t = rootMatrix 3 t *
      ((TwoConjugate.opposition (F := F)).val * (swapPairs (F := F)).val)
  rw [swapPairs_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.fromBlocks, TwoConjugate.opposition]

/-- A first hyperbolic root pair, one mixed transvection root, and the opposite
second long root generate the whole symplectic group over a field larger than two. -/
private theorem eq_top_of_four_long_roots [Finite F] (hF : 2 < Nat.card F)
    (H : Subgroup (Sp F))
    (h₀ : ∀ t : F, rootElement 0 t ∈ H)
    (h₁ : ∀ t : F, rootElement 1 t ∈ H)
    (hm : ∀ t : F, mixed t ∈ H)
    (h₃ : ∀ t : F, rootElement 3 t ∈ H) : H = ⊤ := by
  classical
  let := Fintype.ofFinite F
  have hc : 2 < Fintype.card F := by simpa only [Nat.card_eq_fintype_card] using hF
  obtain ⟨x,y,z,hxy,hxz,hyz⟩ := Fintype.two_lt_card_iff.mp hc
  have hex : ∃ x : F, x ≠ 0 ∧ x ≠ 1 := by
    by_contra! h
    have hx := h x
    have hy := h y
    have hz := h z
    by_cases hx0 : x = 0 <;> by_cases hy0 : y = 0 <;> by_cases hz0 : z = 0 <;> simp_all
  obtain ⟨u,hu0,hu1⟩ := hex
  let s : Fˣ := Units.mk0 u hu0
  have hs : (s : F) + 1 ≠ 0 := by
    intro he
    apply hu1
    have hh := congrArg (fun v : F => v+1) he
    simpa [s, add_assoc, CharTwo.add_self_eq_zero] using hh
  have hw : swapFirst (F := F) ∈ H := H.mul_mem (H.mul_mem (h₀ 1) (h₁ 1)) (h₀ 1)
  have hd : diagonalTorus s 1 ∈ H := by
    rw [←diagonal_word]
    exact H.mul_mem (H.mul_mem (H.mul_mem (h₀ _) (h₁ _)) (h₀ _)) hw
  have hmix (t : F) : rootElement 0 ((s:F)^2*t) * rootElement 2 t *
      rootElement 4 ((s:F)*t) ∈ H := by
    have he := congrArg (fun g : Sp F => g * (diagonalTorus s 1)⁻¹) (diagonal_mixed s t)
    simp only [mul_inv_cancel_right] at he
    exact he ▸ H.mul_mem (H.mul_mem hd (hm t)) (H.inv_mem hd)
  have h₄ (t : F) : rootElement 4 t ∈ H := by
    have hh := H.mul_mem (H.mul_mem (hmix (t/((s:F)+1))) (hm (t/((s:F)+1))))
      (h₀ (((s:F)^2+1)*(t/((s:F)+1))))
    rw [extract_short, mul_div_cancel₀ _ hs] at hh
    exact hh
  have h₂ (t : F) : rootElement 2 t ∈ H := by
    rw [←extract_second]
    exact H.mul_mem (H.mul_mem (h₀ t) (hm t)) (h₄ t)
  have hop : TwoConjugate.opposition (F := F) ∈ H := by
    rw [←opposition_word]
    exact H.mul_mem hw (H.mul_mem (H.mul_mem (h₂ 1) (h₃ 1)) (h₂ 1))
  apply TwoConjugate.eq_top_of_four_axes H h₀ h₁ h₄
  intro t
  rw [←(TwoConjugate.opposition_central_axes t).2]
  exact H.mul_mem (H.mul_mem hop (h₄ t)) (H.inv_mem hop)

/-- Four actual conjugates of the first long-root subgroup generate Sp₄. -/
theorem exists_four_conjugates_generate [Finite F] (hF : 2 < Nat.card F) :
    ∃ g : Fin 4 → Sp F,
      (⨆ i, (RootSubgroup.group 0).map (MulAut.conj (g i)).toMonoidHom) = ⊤ := by
  classical
  let g : Fin 4 → Sp F := ![1,swapFirst,rootElement 7 1,TwoConjugate.opposition*swapPairs]
  refine ⟨g,?_⟩
  let H := ⨆ i, (RootSubgroup.group 0).map (MulAut.conj (g i)).toMonoidHom
  have hm (i : Fin 4) (t : F) : g i * rootElement 0 t * (g i)⁻¹ ∈ H := by
    apply (le_iSup (fun i => (RootSubgroup.group 0).map (MulAut.conj (g i)).toMonoidHom) i)
    exact mem_map_of_mem _ (subset_closure ⟨t,rfl⟩)
  apply eq_top_of_four_long_roots hF
  · intro t
    simpa only [g, Matrix.cons_val_zero, one_mul, inv_one, mul_one] using hm 0 t
  · intro t
    have h := hm 1 t
    change swapFirst * rootElement 0 t * swapFirst⁻¹ ∈ H at h
    rwa [first_conjugate] at h
  · intro t
    have h := hm 2 t
    change rootElement 7 1 * rootElement 0 t * (rootElement 7 1)⁻¹ ∈ H at h
    rw [root_inv] at h
    exact h
  · intro t
    have h := hm 3 t
    change (TwoConjugate.opposition * swapPairs) * rootElement 0 t *
      (TwoConjugate.opposition * swapPairs)⁻¹ ∈ H at h
    rwa [last_conjugate] at h

end Theory.SpecificGroups.SymplecticFour.FourLongRoots
