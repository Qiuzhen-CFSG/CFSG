module
public import Theory.Representation.HermitianTensorThree.PlaneSection
public import Theory.SpecificGroups.SL2.Affine.Action
/-!
# The natural section of the Hermitian nine-space

The last-column map identifies the hyperplane X₂₂=0 modulo its fixed
Hermitian corner with F₄². Every corner-preserving SL₃(4) congruence
induces a determinant-one matrix on these coordinates: its upper block
is multiplied by the conjugate of the last diagonal entry. The determinant
calculation uses d³=1 in F₄. This supplies the natural, rather than the
orthogonal, action needed on the source section B₀/U.

Source: Aschbacher–Smith H.4.6(2), applied in 8.2.8(4–5), printed
pp.382,718–719, refs/quasithin.pdf (1 March 2004 manuscript).
-/
open Subgroup Representation Representation.BinaryOffender
open Representation.HermitianTensorThree
open scoped MatrixGroups
public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Representation.HermitianTensorThree.PlaneSection
/-- The two upper entries in the last column. -/
def column : Space 1 →ₗ[ZMod 2] (Fin 2 → E 1) where
  toFun X i := X.val i.castSucc 2
  map_add' _ _ := rfl
  map_smul' a X := by
    fin_cases a <;> simp
    rfl

theorem column_eq_zero_iff (X : Space 1) (hX : X.val 2 2 = 0) :
    column X = 0 ↔ X ∈ Corner := by
  rw [UnipotentRadicals.mem_plane_fixed_iff]
  constructor
  · intro h
    exact ⟨hX,congrFun h 1,congrFun h 0⟩
  · rintro ⟨_,h1,h0⟩
    ext i
    fin_cases i <;> assumption

theorem column_surjective :
    ∀ v : Fin 2 → E 1, ∃ X : Space 1, X.val 2 2 = 0 ∧ column X = v := by
  intro v
  refine ⟨(coordinates 1).symm (0,![0,v 0,v 1]),rfl,?_⟩
  ext i
  fin_cases i <;> rfl

private theorem lower_zero (a : Cover 1)
    (h : ∀ X ∈ Corner, binaryActionHom 1 a X ∈ Corner) :
    a 2 0 = 0 ∧ a 2 1 = 0 := by
  have hi (i : Fin 2) : a 2 i.castSucc = 0 := by
    let X : Space 1 := ⟨Matrix.single i.castSucc i.castSucc 1,by
      ext j k
      simp [adjoint,Matrix.single_apply]⟩
    have hx : X ∈ Corner := by
      apply (UnipotentRadicals.mem_plane_fixed_iff 1 _).mpr
      fin_cases i <;> simp [X]
    have hh := ((UnipotentRadicals.mem_plane_fixed_iff 1 _).mp (h X hx)).1
    change (a.val * X.val * adjoint 1 a.val) 2 2 = 0 at hh
    have hh : a 2 i.castSucc * sigma 1 (a 2 i.castSucc) = 0 := by
      simpa [X,adjoint,Matrix.mul_apply,Matrix.single_apply,ite_and] using hh
    rcases mul_eq_zero.mp hh with hz | hz
    · exact hz
    · exact (sigma 1).injective (hz.trans (map_zero _).symm)
  exact ⟨hi 0,hi 1⟩

/-- Each corner-preserving SL₃(4) congruence induces a determinant-one
natural transformation on the last-column section. -/
theorem column_action (a : Cover 1)
    (h : ∀ X ∈ Corner, binaryActionHom 1 a X ∈ Corner) :
    ∃ t : SL(2,E 1), ∀ X : Space 1, X.val 2 2 = 0 →
      column (binaryActionHom 1 a X) = t.val.mulVec (column X) := by
  obtain ⟨h20,h21⟩ := lower_zero a h
  let d := a 2 2
  let b : Matrix (Fin 2) (Fin 2) (E 1) := fun i j => a i.castSucc j.castSucc
  have hb : b.det * d = 1 := by
    have hh : a.val.det = 1 := a.property
    simp only [Matrix.det_fin_three,h20,h21,mul_zero,add_zero,sub_zero] at hh
    simpa [b,d,Matrix.det_fin_two,sub_mul] using hh
  have hd : d ≠ 0 := right_ne_zero_of_mul_eq_one hb
  have hd3 : d^3 = 1 := by
    let : Fintype (E 1) := Fintype.ofFinite _
    have hc : Fintype.card (E 1) = 4 := by rw [←Nat.card_eq_fintype_card,card_E]; norm_num
    simpa [hc] using FiniteField.pow_card_sub_one_eq_one d hd
  have hs : sigma 1 d = d^2 := rfl
  let t : SL(2,E 1) := ⟨sigma 1 d • b,by
    rw [Matrix.det_smul, Fintype.card_fin,hs]
    calc
      (d^2)^2 * b.det = (b.det*d)*d^3 := by ring
      _ = 1 := by rw [hb,hd3,one_mul]⟩
  refine ⟨t,?_⟩
  intro X hX
  ext i
  change (a.val * X.val * adjoint 1 a.val) i.castSucc 2 =
    ((sigma 1 d • b).mulVec (column X)) i
  simp [adjoint,Matrix.mul_apply,Fin.sum_univ_three,h20,h21,hX,
    Matrix.mulVec, dotProduct,Fin.sum_univ_two,b,column,d]
  ring
end Representation.HermitianTensorThree.PlaneSection
