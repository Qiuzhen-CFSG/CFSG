module
public import Theory.Representation.HermitianTensorThree.UnipotentRadicals
open Subgroup Representation Representation.BinaryOffender
open Representation.HermitianTensorThree
open Matrix.PSL3Even.UnipotentGeometry
open scoped MatrixGroups
/-!
# The four-dimensional section above a Hermitian corner

The plane radical in SL₃(4) has fixed space the upper Hermitian corner.
Its second fixed space is the hyperplane with bottom diagonal entry zero,
which has order 2⁸. A corner-preserving congruence trivial on this hyperplane
modulo the corner is already trivial on the corner. The proof reads the two
upper entries of the last column, retaining the original matrix action.

These are the coordinate calculations used for the natural section in
Aschbacher–Smith H.4.6(2) and 8.2.8(4), printed pp.382 and718,
refs/quasithin.pdf (1 March 2004 manuscript).
-/
public noncomputable section
namespace Representation.HermitianTensorThree.PlaneSection
/-- The fixed Hermitian two-by-two corner. -/
abbrev Corner := fixedSpace (UnipotentRadicals.ambientAction 1) (UnipotentRadicals.plane 1)

/-- The second fixed space of the plane radical is its canonical hyperplane. -/
theorem displacement_mem_corner_iff (X : Space 1) :
    (∀ t ∈ UnipotentRadicals.plane 1, t X - X ∈ Corner) ↔ X.val 2 2 = 0 := by
  constructor
  · intro h
    have hh := (UnipotentRadicals.mem_plane_fixed_iff 1 _).mp
      (h (UnipotentRadicals.unipotentHom 1 ⟨0,0,1⟩)
        (mem_map_of_mem _ ((mem_V₂ (E 1) _).mpr rfl)))
    have hh := hh.2.2
    change ((matrix (E 1) ⟨0,0,1⟩ * X.val * adjoint 1 (matrix (E 1) ⟨0,0,1⟩)) 0 2 - X.val 0 2) = 0 at hh
    simpa [matrix,adjoint,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three] using hh
  · intro h t ht
    obtain ⟨z,hz,rfl⟩ := ht
    have hx := (mem_V₂ (E 1) z).mp hz
    apply (UnipotentRadicals.mem_plane_fixed_iff 1 _).mpr
    change (matrix (E 1) z * X.val * adjoint 1 (matrix (E 1) z)) 2 2 - X.val 2 2 = 0 ∧
      (matrix (E 1) z * X.val * adjoint 1 (matrix (E 1) z)) 1 2 - X.val 1 2 = 0 ∧
      (matrix (E 1) z * X.val * adjoint 1 (matrix (E 1) z)) 0 2 - X.val 0 2 = 0
    simp [matrix,hx,adjoint,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three,h]

/-- The canonical hyperplane has binary dimension eight. -/
theorem card_hyperplane : Nat.card {X : Space 1 // X.val 2 2 = 0} = 2^8 := by
  let e : {X : Space 1 // X.val 2 2 = 0} ≃ ((F 1 × F 1) × (Fin 3 → E 1)) := {
    toFun := fun X => (((coordinates 1 X.val).1 0,(coordinates 1 X.val).1 1),
      (coordinates 1 X.val).2)
    invFun := fun x => ⟨(coordinates 1).symm (![x.1.1,x.1.2,0],x.2),rfl⟩
    left_inv := fun X => by
      apply Subtype.ext
      apply (coordinates 1).injective
      rw [LinearEquiv.apply_symm_apply]
      apply Prod.ext
      · ext i
        fin_cases i
        · rfl
        · rfl
        · exact X.property.symm
      · rfl
    right_inv := fun x => by simp only [LinearEquiv.apply_symm_apply]; rfl }
  rw [Nat.card_congr e, Nat.card_prod,Nat.card_prod,Nat.card_fun,Nat.card_fin,card_F,card_E]
  norm_num

private def diag (i : Fin 3) : Space 1 :=
  ⟨Matrix.single i i 1, by ext a b; simp [adjoint,Matrix.single_apply]⟩
private theorem diag_action (A : Mat 1) (i a b : Fin 3) :
    (A * (diag i).val * adjoint 1 A) a b = A a i * sigma 1 (A b i) := by
  simp [diag,Matrix.mul_apply,Matrix.single_apply,adjoint,ite_and]

private theorem corner_preserver_lower (a : Cover 1)
    (h : ∀ X ∈ Corner, binaryActionHom 1 a X ∈ Corner) :
    a 2 0 = 0 ∧ a 2 1 = 0 := by
  have hi (i : Fin 2) : a 2 i.castSucc = 0 := by
    have hx : diag i.castSucc ∈ Corner := by
      apply (UnipotentRadicals.mem_plane_fixed_iff 1 _).mpr
      fin_cases i <;> simp [diag]
    have hh := ((UnipotentRadicals.mem_plane_fixed_iff 1 _).mp (h _ hx)).1
    change (a.val * (diag i.castSucc).val * adjoint 1 a.val) 2 2 = 0 at hh
    rw [diag_action] at hh
    rcases mul_eq_zero.mp hh with hz | hz
    · exact hz
    · exact (sigma 1).injective (hz.trans (map_zero _).symm)
  exact ⟨hi 0,hi 1⟩

private theorem norm_one (d : E 1) (hd : d ≠ 0) : d * sigma 1 d = 1 := by
  let : Fintype (E 1) := Fintype.ofFinite _
  have hh := FiniteField.pow_card_sub_one_eq_one d hd
  have hc : Fintype.card (E 1) = 4 := by rw [←Nat.card_eq_fintype_card,card_E]; norm_num
  rw [hc] at hh
  change d * d^(2^1) = 1
  simpa [pow_succ,mul_assoc] using hh

private def cross (u v : E 1) : Space 1 :=
  (coordinates 1).symm (0,![0,u,v])

/-- Triviality on the canonical section forces triviality on its corner. -/
theorem section_trivial_implies_corner_trivial (a : Cover 1)
    (h : ∀ X ∈ Corner, binaryActionHom 1 a X ∈ Corner)
    (ht : ∀ X : Space 1, X.val 2 2 = 0 → binaryActionHom 1 a X - X ∈ Corner) :
    ∀ X ∈ Corner, binaryActionHom 1 a X = X := by
  obtain ⟨h20,h21⟩ := corner_preserver_lower a h
  have hc (u v : E 1) := (UnipotentRadicals.mem_plane_fixed_iff 1 _).mp
    (ht (cross u v) rfl)
  have h00 : a 0 0 * sigma 1 (a 2 2) = 1 := by
    have hh := (hc 1 0).2.2
    change (a.val * (cross 1 0).val * adjoint 1 a.val) 0 2 - (cross 1 0).val 0 2 = 0 at hh
    simpa [cross,coordinates,adjoint,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three,h20,h21,sub_eq_zero] using hh
  have h11 : a 1 1 * sigma 1 (a 2 2) = 1 := by
    have hh := (hc 0 1).2.1
    change (a.val * (cross 0 1).val * adjoint 1 a.val) 1 2 - (cross 0 1).val 1 2 = 0 at hh
    simpa [cross,coordinates,adjoint,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three,h20,h21,sub_eq_zero] using hh
  have hs : sigma 1 (a 2 2) ≠ 0 := right_ne_zero_of_mul_eq_one h00
  have hd : a 2 2 ≠ 0 := fun hz => hs (by rw [hz,map_zero])
  have hn := norm_one _ hd
  have he00 : a 0 0 = a 2 2 := mul_right_cancel₀ hs (h00.trans hn.symm)
  have he11 : a 1 1 = a 2 2 := mul_right_cancel₀ hs (h11.trans hn.symm)
  have h01 : a 0 1 = 0 := by
    have hh := (hc 0 1).2.2
    change (a.val * (cross 0 1).val * adjoint 1 a.val) 0 2 - (cross 0 1).val 0 2 = 0 at hh
    have hz : a 0 1 * sigma 1 (a 2 2) = 0 := by
      simpa [cross,coordinates,adjoint,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three,h20,h21,sub_eq_zero] using hh
    exact (mul_eq_zero.mp hz).resolve_right hs
  have h10 : a 1 0 = 0 := by
    have hh := (hc 1 0).2.1
    change (a.val * (cross 1 0).val * adjoint 1 a.val) 1 2 - (cross 1 0).val 1 2 = 0 at hh
    have hz : a 1 0 * sigma 1 (a 2 2) = 0 := by
      simpa [cross,coordinates,adjoint,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three,h20,h21,sub_eq_zero] using hh
    exact (mul_eq_zero.mp hz).resolve_right hs
  intro X hX
  obtain ⟨h22,h12,h02⟩ := (UnipotentRadicals.mem_plane_fixed_iff 1 X).mp hX
  have hx20 : X.val 2 0 = 0 := by rw [←entry_conjugate 1 X 2 0,h02,map_zero]
  have hx21 : X.val 2 1 = 0 := by rw [←entry_conjugate 1 X 2 1,h12,map_zero]
  apply Subtype.ext
  change a.val * X.val * adjoint 1 a.val = X.val
  have hn' (x : E 1) : a 2 2 * x * sigma 1 (a 2 2) = x := by
    rw [mul_right_comm,hn,one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjoint,Matrix.mul_apply,Fin.sum_univ_three,h20,h21,h01,h10,he00,he11,
      h22,h12,h02,hx20,hx21,hn']
end Representation.HermitianTensorThree.PlaneSection
