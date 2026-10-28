module

public import Theory.SpecificGroups.SymplecticFour.OppositeLongRootPair.Recognition
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.RootRecognition.FourAxes
public import Theory.SpecificGroups.SymplecticFour.Sylow.Normalizer

/-!
# Three point-local conjugates of an opposite long-root pair

The conjugators 1, x₄(1), x₆(1) fix the first vector. After swapping the
first hyperbolic pair, their opposite roots are the mixed transvections
along e₀+e₁ and e₀+f₁. A first-plane torus separates these into both
second-plane long roots and a short root. Elementary generation finishes.

The torus-separation calculations are adapted from `FourLongRoots.lean`.
Source: Aschbacher–Smith, 11.5.7, printed p.783.
-/

@[expose] public noncomputable section
open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.OppositeLongRootPair
variable {F : Type*} [Field F] [CharP F 2]

private def mixed (t : F) : Sp F := rootElement 7 1 * rootElement 0 t * rootElement 7 1
private def swapFirst : Sp F := rootElement 0 1 * rootElement 1 1 * rootElement 0 1
private def swapSecond : Sp F := rootElement 2 1 * rootElement 3 1 * rootElement 2 1

private theorem root_inv (r : Fin 8) (t : F) : (rootElement r t)⁻¹ = rootElement r t := by
  apply inv_eq_of_mul_eq_one_right
  rw [RootSubgroup.element_add, CharTwo.add_self_eq_zero, RootSubgroup.element_zero]

private theorem swapFirst_matrix : (swapFirst (F := F)).val =
    fromBlocks !![0,0;0,1] !![1,0;0,0] !![1,0;0,0] !![0,0;0,1] := by
  change (rootMatrix 0 1 * rootMatrix 1 1 * rootMatrix 0 1) = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      single, fromBlocks, CharTwo.add_self_eq_zero]

private theorem swapSecond_matrix : (swapSecond (F := F)).val =
    fromBlocks !![1,0;0,0] !![0,0;0,1] !![0,0;0,1] !![1,0;0,0] := by
  change (rootMatrix 2 1 * rootMatrix 3 1 * rootMatrix 2 1) = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      single, fromBlocks, CharTwo.add_self_eq_zero]

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

private theorem roots_of_mixed [Finite F] (hF : 2 < Nat.card F)
    (H : Subgroup (Sp F))
    (h₀ : ∀ t : F, rootElement 0 t ∈ H)
    (h₁ : ∀ t : F, rootElement 1 t ∈ H)
    (hm : ∀ t : F, mixed t ∈ H) :
    (∀ t : F, rootElement 2 t ∈ H) ∧ (∀ t : F, rootElement 4 t ∈ H) := by
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
  exact ⟨h₂, h₄⟩

private theorem swapFirst_inv : (swapFirst (F := F))⁻¹ = swapFirst := by
  simp only [swapFirst, _root_.mul_inv_rev, root_inv, mul_assoc]

private theorem swapSecond_inv : (swapSecond (F := F))⁻¹ = swapSecond := by
  simp only [swapSecond, _root_.mul_inv_rev, root_inv, mul_assoc]

private theorem pair4_mixed (t : F) :
    swapFirst * (rootElement 4 1 * rootElement 1 t * (rootElement 4 1)⁻¹) *
      swapFirst⁻¹ = mixed t := by
  rw [root_inv, mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (swapFirst (F := F)).val *
    (rootMatrix 4 1 * rootMatrix 1 t * rootMatrix 4 1) =
    (mixed t).val * (swapFirst (F := F)).val
  rw [mixed_matrix, swapFirst_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      single, fromBlocks, CharTwo.add_self_eq_zero]

private theorem secondSwap_roots (t : F) :
    swapSecond * rootElement 0 t * swapSecond⁻¹ = rootElement 0 t ∧
    swapSecond * rootElement 1 t * swapSecond⁻¹ = rootElement 1 t ∧
    swapSecond * rootElement 2 t * swapSecond⁻¹ = rootElement 3 t := by
  have h (r r' : Fin 8)
      (he : (swapSecond (F := F)).val * rootMatrix r t =
        rootMatrix r' t * (swapSecond (F := F)).val) :
      swapSecond * rootElement r t * swapSecond⁻¹ = rootElement r' t := by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subtype.ext he
  refine ⟨h 0 0 ?_, h 1 1 ?_, h 2 3 ?_⟩ <;>
    rw [swapSecond_matrix] <;> ext i j <;>
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [rootMatrix, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
        single, fromBlocks]

private theorem pair6_mixed (t : F) :
    swapSecond * mixed t * swapSecond⁻¹ =
      swapFirst * (rootElement 6 1 * rootElement 1 t * (rootElement 6 1)⁻¹) *
        swapFirst⁻¹ := by
  have hmiddle : rootMatrix 6 (1 : F) * rootMatrix 1 t * rootMatrix 6 1 =
      fromBlocks 1 0 !![t,t;t,t] 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [rootMatrix, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
        single, fromBlocks, CharTwo.neg_eq, CharTwo.add_self_eq_zero]
  rw [root_inv, swapFirst_inv, swapSecond_inv]
  apply Subtype.ext
  change (swapSecond (F := F)).val * (mixed t).val * (swapSecond (F := F)).val =
    ((swapFirst (F := F)).val * (rootMatrix 6 1 * rootMatrix 1 t * rootMatrix 6 1)) *
      (swapFirst (F := F)).val
  rw [hmiddle, mixed_matrix, swapFirst_matrix, swapSecond_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      fromBlocks, CharTwo.add_self_eq_zero]

private theorem opposition_word : swapFirst * swapSecond = TwoConjugate.opposition (F := F) := by
  apply Subtype.ext
  change (swapFirst (F := F)).val * (swapSecond (F := F)).val = _
  rw [swapFirst_matrix, swapSecond_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      fromBlocks, TwoConjugate.opposition]

/-- The three specified conjugators belong to the actual point-local subgroup. -/
def conjugators : Fin 3 → Sp F := ![1, rootElement 4 1, rootElement 6 1]

omit [CharP F 2] in
theorem conjugators_mem (i : Fin 3) : conjugators (F := F) i ∈ pointLocal := by
  fin_cases i
  · exact one_mem _
  · exact (positive_root_mem_unipotent 4 1 (by simp)).1
  · exact (positive_root_mem_unipotent 6 1 (by simp)).1

/-- Three point-local conjugates of the literal opposite long-root pair
 generate the full matrix symplectic group. -/
theorem three_pairs_generate [Finite F] (hF : 2 < Nat.card F) :
    (⨆ i, (pair (F := F)).map (MulAut.conj (conjugators i)).toMonoidHom) = ⊤ := by
  let H := ⨆ i, (pair (F := F)).map (MulAut.conj (conjugators i)).toMonoidHom
  have hpair : pair ≤ H := by
    intro x hx
    apply (le_iSup (fun i => (pair (F := F)).map
      (MulAut.conj (conjugators i)).toMonoidHom) 0)
    exact ⟨x, hx, by simp [conjugators]⟩
  have h₀ (t : F) : rootElement 0 t ∈ H := hpair (mem_sup_left (subset_closure ⟨t, rfl⟩))
  have h₁ (t : F) : rootElement 1 t ∈ H := hpair (mem_sup_right (subset_closure ⟨t, rfl⟩))
  have hcon (i : Fin 3) (t : F) :
      conjugators i * rootElement 1 t * (conjugators i)⁻¹ ∈ H := by
    apply (le_iSup (fun i => (pair (F := F)).map
      (MulAut.conj (conjugators i)).toMonoidHom) i)
    exact mem_map_of_mem _ (mem_sup_right (subset_closure ⟨t, rfl⟩))
  have hw : swapFirst (F := F) ∈ H := H.mul_mem (H.mul_mem (h₀ 1) (h₁ 1)) (h₀ 1)
  have hm (t : F) : mixed t ∈ H := by
    rw [← pair4_mixed]
    exact H.mul_mem (H.mul_mem hw (hcon 1 t)) (H.inv_mem hw)
  obtain ⟨h₂, h₄⟩ := roots_of_mixed hF H h₀ h₁ hm
  let J := H.comap (MulAut.conj (swapSecond (F := F))).toMonoidHom
  have hj₀ (t : F) : rootElement 0 t ∈ J := by
    change swapSecond * rootElement 0 t * swapSecond⁻¹ ∈ H
    rw [(secondSwap_roots t).1]
    exact h₀ t
  have hj₁ (t : F) : rootElement 1 t ∈ J := by
    change swapSecond * rootElement 1 t * swapSecond⁻¹ ∈ H
    rw [(secondSwap_roots t).2.1]
    exact h₁ t
  have hjm (t : F) : mixed t ∈ J := by
    change swapSecond * mixed t * swapSecond⁻¹ ∈ H
    rw [pair6_mixed]
    exact H.mul_mem (H.mul_mem hw (hcon 2 t)) (H.inv_mem hw)
  have h₃ (t : F) : rootElement 3 t ∈ H := by
    have hh := (roots_of_mixed hF J hj₀ hj₁ hjm).1 t
    change swapSecond * rootElement 2 t * swapSecond⁻¹ ∈ H at hh
    rwa [(secondSwap_roots t).2.2] at hh
  have hop : TwoConjugate.opposition (F := F) ∈ H := by
    rw [← opposition_word]
    exact H.mul_mem hw (H.mul_mem (H.mul_mem (h₂ 1) (h₃ 1)) (h₂ 1))
  apply TwoConjugate.eq_top_of_four_axes H h₀ h₁ h₄
  intro t
  rw [← (TwoConjugate.opposition_central_axes t).2]
  exact H.mul_mem (H.mul_mem hop (h₄ t)) (H.inv_mem hop)

/-- Simultaneously changing the marking preserves point-local generation. -/
theorem exists_three_conjugated_pairs [Finite F] (hF : 2 < Nat.card F) (g : Sp F) :
    ∃ k : Fin 3 → Sp F,
      (∀ i, k i ∈ (pointLocal (F := F)).map (MulAut.conj g).toMonoidHom) ∧
      (⨆ i, ((pair (F := F)).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj (k i)).toMonoidHom) = ⊤ := by
  let k : Fin 3 → Sp F := fun i => (MulAut.conj g) (conjugators i)
  refine ⟨k, fun i => mem_map_of_mem _ (conjugators_mem i), ?_⟩
  have he (i : Fin 3) :
      ((pair (F := F)).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj (k i)).toMonoidHom =
      ((pair (F := F)).map (MulAut.conj (conjugators i)).toMonoidHom).map
        (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change (g * conjugators i * g⁻¹) * (g * x * g⁻¹) *
      (g * conjugators i * g⁻¹)⁻¹ = g * (conjugators i * x * (conjugators i)⁻¹) * g⁻¹
    group
  simp_rw [he]
  rw [← Subgroup.map_iSup, three_pairs_generate hF,
    map_top_of_surjective _ (MulAut.conj g).surjective]

end Theory.SpecificGroups.SymplecticFour.OppositeLongRootPair
