module
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.Flag.Frattini
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Counting
public import Theory.Frattini.BinarySquares
public import Theory.ElementaryAbelian.Injective

/-!
# The center and involutions of the unitary-five plane radical

In the actual plane parameters `(x,z)`, the square has Hermitian block
`x x*`. Thus square-one elements have `x = 0`. Commutation with lifts of
the two coordinate vectors shows that this is also exactly the center.
The existing explicit commutators generate this kernel; the square formula
then identifies the Frattini subgroup. Two fixed diagonal entries and one
arbitrary off-diagonal entry count the center as `4^4` over the field of
order sixteen. Every elementary two-subgroup lies in this same center.

This is the native plane-core input to Aschbacher--Smith F.4.29(6) and
F.4.35, printed pp.289--292 of `refs/quasithin.pdf`. Transport to the
projective model and the original prepared row is in the ChapterF/6
companions. It does not identify the Thompson subgroup of the larger Sylow.
-/

public section
open BenderSuzuki.MatrixGroups Matrix Subgroup
namespace Theory.SpecificGroups.UnitaryFive.PlaneCore.Parameters
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

theorem square_eq_one_iff (u : Parameters J) : u ^ 2 = 1 ↔ u.x = 0 := by
  constructor
  · intro h
    funext i
    have hz := congrArg (fun v : Parameters J => v.z i i) h
    simp only [pow_two, mul_z, CharTwo.add_self_eq_zero, zero_add,
      one_z, Matrix.zero_apply] at hz
    rcases mul_eq_zero.mp hz with hi | hi
    · exact hi
    · exact J.conj.injective (by simpa using hi)
  · intro h
    rw [pow_two]
    apply Parameters.ext
    · simp [h]
    · ext i j
      simp [h, CharTwo.add_self_eq_zero]

theorem mem_center_of_x_eq_zero (u : Parameters J) (hu : u.x = 0) :
    u ∈ center (Parameters J) := by
  apply mem_center_iff.mpr
  intro v
  apply Parameters.ext
  · simp [hu]
  · ext i j
    simp [hu, add_comm]

theorem mem_center_iff_x_eq_zero (c : F) (hc : c + J.conj c = 1)
    (u : Parameters J) : u ∈ center (Parameters J) ↔ u.x = 0 := by
  refine ⟨?_, mem_center_of_x_eq_zero J u⟩
  intro hu
  have hcomm (v : Fin 2 → F) (i j : Fin 2) :
      v i * J.conj (u.x j) = u.x i * J.conj (v j) := by
    obtain ⟨w, hw⟩ := vectorHom_surjective J c hc (Multiplicative.ofAdd v)
    have hw' : w.x = v := congrArg Multiplicative.toAdd hw
    have hh := congrArg (fun a : Parameters J => a.z i j) (mem_center_iff.mp hu w)
    simp only [mul_z, hw'] at hh
    linear_combination hh
  funext i
  fin_cases i
  · have hh := hcomm ![0,1] 0 1
    simpa using hh.symm
  · have hh := hcomm ![1,0] 1 0
    simpa using hh.symm

theorem square_eq_one_iff_mem_center (c : F) (hc : c + J.conj c = 1)
    (u : Parameters J) : u ^ 2 = 1 ↔ u ∈ center (Parameters J) :=
  (square_eq_one_iff J u).trans (mem_center_iff_x_eq_zero J c hc u).symm

theorem center_eq_vector_ker (c : F) (hc : c + J.conj c = 1) :
    center (Parameters J) = (vectorHom J).ker := by
  ext u
  rw [mem_center_iff_x_eq_zero J c hc]
  rfl

theorem commutator_eq_center (c : F) (hc : c + J.conj c = 1) :
    commutator (Parameters J) = center (Parameters J) := by
  rw [center_eq_vector_ker J c hc]
  exact le_antisymm (Abelianization.commutator_subset_ker (vectorHom J))
    (vectorHom_ker_le_commutator J c hc)

theorem center_isElementaryAbelian (c : F) (hc : c + J.conj c = 1) :
    IsElementaryAbelian 2 (center (Parameters J)) := by
  refine { exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro u
  apply Subtype.ext
  exact (square_eq_one_iff_mem_center J c hc u.val).mpr u.property

theorem frattini_eq_center [Finite F] (c : F) (hc : c + J.conj c = 1) :
    frattini (Parameters J) = center (Parameters J) := by
  let : Finite (Parameters J) := Finite.of_injective
    (fun u : Parameters J => (u.x,u.z)) (by
      intro u v he
      exact Parameters.ext (congrArg Prod.fst he) (congrArg Prod.snd he))
  rw [(Parameters.isPGroup (J := J)).frattini_eq_closure_squares]
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨u,rfl⟩
    apply mem_center_of_x_eq_zero
    ext i
    simp [pow_two, CharTwo.add_self_eq_zero]
  · rw [←commutator_eq_center J c hc]
    exact commutator_le_closure_squares

private theorem central_entry (c : F) (hc : c + J.conj c = 1)
    (u : center (Parameters J)) (i j : Fin 2) : J.conj (u.val.z j i) = u.val.z i j := by
  have hh := u.val.relation i j
  rw [(mem_center_iff_x_eq_zero J c hc u.val).mp u.property, Pi.zero_apply, zero_mul] at hh
  exact add_left_cancel (hh.trans (CharTwo.add_self_eq_zero (u.val.z i j)).symm)

def centerCoordinateEquiv (c : F) (hc : c + J.conj c = 1) :
    center (Parameters J) ≃
      ({a : F // J.conj a = a} × {a : F // J.conj a = a}) × F where
  toFun u := ((⟨u.val.z 0 0, central_entry J c hc u 0 0⟩,
    ⟨u.val.z 1 1, central_entry J c hc u 1 1⟩),u.val.z 0 1)
  invFun a := ⟨⟨0,!![a.1.1.val,a.2;J.conj a.2,a.1.2.val],by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [a.1.1.property,a.1.2.property,CharTwo.add_self_eq_zero]⟩,
    mem_center_of_x_eq_zero J _ rfl⟩
  left_inv u := by
    apply Subtype.ext
    apply Parameters.ext
    · exact ((mem_center_iff_x_eq_zero J c hc u.val).mp u.property).symm
    · ext i j
      fin_cases i <;> fin_cases j
      · rfl
      · rfl
      · exact central_entry J c hc u 1 0
      · rfl
  right_inv a := by cases a; rfl

theorem card_center [Finite F] (hcard : Nat.card F = 16)
    (hconj : ∀ a, J.conj a = a ^ 4) (c : F) (hc : c + J.conj c = 1) :
    Nat.card (center (Parameters J)) = 4 ^ 4 := by
  rw [Nat.card_congr (centerCoordinateEquiv J c hc),Nat.card_prod,Nat.card_prod,
    fixed_card_four J hcard hconj,hcard]
  norm_num

theorem elementary_le_center (c : F) (hc : c + J.conj c = 1)
    (E : Subgroup (Parameters J)) (hE : IsElementaryAbelian 2 E) :
    E ≤ center (Parameters J) := by
  let := hE
  intro u hu
  exact (square_eq_one_iff_mem_center J c hc u).mp
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) u hu)

/-- An actual core equivalence transports the special-group structure and the
exact square-one locus. The supplied field is still the field of order sixteen. -/
theorem structure_of_equiv {Q : Type*} [Group Q] [Finite Q]
    [Finite F] (hcard : Nat.card F = 16) (hconj : ∀ a, J.conj a = a ^ 4)
    (c : F) (hc : c + J.conj c = 1) (e : Q ≃* Parameters J) :
    Nat.card (center Q) = 4 ^ 4 ∧ IsElementaryAbelian 2 (center Q) ∧
      center Q = commutator Q ∧ center Q = frattini Q ∧
      ∀ u : Q, u ^ 2 = 1 ↔ u ∈ center Q := by
  have hmem (u : Q) : e u ∈ center (Parameters J) ↔ u ∈ center Q := by
    rw [←center_map_equiv e]
    exact mem_map_iff_mem e.injective
  let := center_isElementaryAbelian J c hc
  refine ⟨(Nat.card_congr (centerCongr e).toEquiv).trans
    (card_center J hcard hconj c hc),
    IsElementaryAbelian.of_injective (centerCongr e).toMonoidHom
      (centerCongr e).injective, ?_, ?_, ?_⟩
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [center_map_equiv e, map_commutator_eq,
      MonoidHom.range_eq_top.mpr e.surjective, ←_root_.commutator_def]
    exact (commutator_eq_center J c hc).symm
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [center_map_equiv e, frattini_map_equiv e]
    exact (frattini_eq_center J c hc).symm
  · intro u
    rw [←hmem, ←square_eq_one_iff_mem_center J c hc]
    constructor
    · intro hu
      rw [←map_pow, hu, map_one]
    · intro hu
      apply e.injective
      simpa only [map_pow, map_one] using hu

end Theory.SpecificGroups.UnitaryFive.PlaneCore.Parameters
