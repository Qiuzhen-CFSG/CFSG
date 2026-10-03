module
public import BenderGlauberman.Lemma19
public import Theory.Representation.GLTwoBorelIndex
public import Theory.SpecificGroups.GL2.ThreeConjugacy

/-!
# Wong's degree-four character of GL₂(3)

The sign of the first diagonal entry is a linear character of the actual
upper-triangular subgroup. Inducing it to GL₂(3) gives the character with
values `[4,-4,0,1,-1,0,0,0]` on `threeClassRepr`.

A conjugator contributes precisely when its first column spans an invariant
line. Its contribution is +1 when that column is fixed, and -1 otherwise.
Kernel-checked sums over matrices over ZMod 3 compute the induced values and
its norm one. Since induction gives a genuine character, norm one proves
irreducibility.

Source: W. J. Wong, On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2, J. Austral. Math. Soc. 4 (1964), Table 1, p. 97,
DOI:10.1017/S1446788700022771.
-/

open Matrix Matrix.GeneralLinearGroup
open scoped BigOperators
namespace ABG
noncomputable section

private abbrev G := GL (Fin 2) (ZMod 3)
private abbrev M := Matrix (Fin 2) (Fin 2) (ZMod 3)
private abbrev Borel := GLTwo.borelSubgroup (ZMod 3)

private theorem firstEntry_ne_zero (b : Borel) : b.val 0 0 ≠ 0 := by
  have hdet := b.val.det_ne_zero
  have hb := (GLTwo.mem_borelSubgroup _ b.val).mp b.property
  have hdiag : b.val 0 0 ≠ 0 ∧ b.val 1 1 ≠ 0 := by
    simpa [Matrix.det_fin_two, hb, mul_ne_zero_iff] using hdet
  exact hdiag.1

private def firstEntry : Borel →* (ZMod 3)ˣ where
  toFun b := Units.mk0 (b.val 0 0) (firstEntry_ne_zero b)
  map_one' := by apply Units.ext; rfl
  map_mul' b c := by
    apply Units.ext
    change (b.val.val * c.val.val) 0 0 = b.val 0 0 * c.val 0 0
    simp [Matrix.mul_apply, Fin.sum_univ_two,
      (GLTwo.mem_borelSubgroup _ c.val).mp c.property]

private theorem unit_three_cases (u : (ZMod 3)ˣ) : u = 1 ∨ u = -1 := by
  revert u
  decide +kernel

private def unitThreeSign : (ZMod 3)ˣ →* ℂˣ where
  toFun u := if u = 1 then 1 else -1
  map_one' := by simp
  map_mul' u v := by
    have hne : (-1 : (ZMod 3)ˣ) ≠ 1 := by decide
    rcases unit_three_cases u with rfl | rfl <;>
      rcases unit_three_cases v with rfl | rfl <;> simp [hne]

private def borelSign : Borel →* ℂˣ := unitThreeSign.comp firstEntry

private theorem borelSign_apply (b : Borel) :
    (borelSign b : ℂ) = if b.val 0 0 = 1 then 1 else -1 := by
  have heq : firstEntry b = 1 ↔ b.val 0 0 = 1 := Units.ext_iff
  by_cases h : b.val 0 0 = 1 <;> simp [borelSign, unitThreeSign, heq, h]

/-- Induction of the sign of the Borel's first diagonal entry. -/
public def glTwoThreeDegreeFourCharacter : ClassFunction (GL (Fin 2) (ZMod 3)) :=
  inducedClassFunction Borel (fun b => (borelSign b : ℂ))

/-- The degree-four row is afforded by an actual induced representation. -/
public theorem glTwoThreeDegreeFourCharacter_isCharacter :
    IsCharacter glTwoThreeDegreeFourCharacter := by
  let : Fintype Borel := Fintype.ofFinite _
  exact BenderGlauberman.isCharacter_induced _
    (BenderGlauberman.isCharacter_of_isIrreducibleCharacter
      (BenderGlauberman.isLinearCharacter_of_hom borelSign).1)

private def matrixEquiv : G ≃ {A : M // A.det ≠ 0} where
  toFun g := ⟨g.val, g.det_ne_zero⟩
  invFun A := mkOfDetNeZero A.val A.property
  left_inv _ := Units.ext rfl
  right_inv _ := Subtype.ext rfl

private abbrev fixedCondition (A B : M) : Prop :=
  B 0 0 * (A * B) 1 0 = B 1 0 * (A * B) 0 0

private theorem conjugate_mem_borel_iff (g x : G) :
    x⁻¹ * g * x ∈ Borel ↔ fixedCondition g.val x.val := by
  let y := x⁻¹ * g * x
  have hmul : g.val * x.val = x.val * y.val := by
    exact congrArg Units.val (by simp [y, mul_assoc] : g * x = x * y)
  rw [GLTwo.mem_borelSubgroup]
  change y 1 0 = 0 ↔ _
  unfold fixedCondition
  rw [hmul]
  have heq : x.val 0 0 * (x.val * y.val) 1 0 - x.val 1 0 * (x.val * y.val) 0 0 =
      x.val.det * y 1 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
    ring
  conv_rhs => rw [← sub_eq_zero, heq, mul_eq_zero]
  simp [x.det_ne_zero]

private abbrev columnFixed (A B : M) : Prop :=
  (A * B) 0 0 = B 0 0 ∧ (A * B) 1 0 = B 1 0

private theorem conjugate_firstEntry_eq_one (g x : G) (h : x⁻¹ * g * x ∈ Borel) :
    (x⁻¹ * g * x) 0 0 = 1 ↔ columnFixed g.val x.val := by
  let y := x⁻¹ * g * x
  have hy : y 1 0 = 0 := h
  have hmul : g.val * x.val = x.val * y.val :=
    congrArg Units.val (by simp [y, mul_assoc] : g * x = x * y)
  have hcol : x.val 0 0 ≠ 0 ∨ x.val 1 0 ≠ 0 := by
    by_contra hzero
    push Not at hzero
    have hd := x.det_ne_zero
    simp [Matrix.det_fin_two, hzero.1, hzero.2] at hd
  change y 0 0 = 1 ↔ _
  unfold columnFixed
  rw [hmul]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hy, mul_zero, add_zero]
  constructor
  · intro h; simp [h]
  · intro h
    rcases hcol with hc | hc
    · exact (mul_left_cancel₀ hc (h.1.trans (mul_one _).symm))
    · exact (mul_left_cancel₀ hc (h.2.trans (mul_one _).symm))

private def contribution (A B : M) : ℤ :=
  if fixedCondition A B then (if columnFixed A B then 1 else -1) else 0

private def rawValue (A : M) : ℤ :=
  ∑ B ∈ Finset.univ.filter (fun B : M => B.det ≠ 0), contribution A B

private theorem borel_card : Nat.card Borel = 12 := by
  have h := Borel.index_mul_card
  rw [GLTwo.borelSubgroup_index, Matrix.card_GL_field] at h
  norm_num [Fin.prod_univ_two] at h ⊢
  omega

private theorem row_apply (g : G) :
    glTwoThreeDegreeFourCharacter g = (rawValue g.val : ℂ) / 12 := by
  classical
  have hterm (x : G) :
      (if h : x⁻¹ * g * x ∈ Borel then (borelSign ⟨x⁻¹ * g * x, h⟩ : ℂ) else 0) =
        (contribution g.val x.val : ℂ) := by
    by_cases hx : x⁻¹ * g * x ∈ Borel
    · have hfix := (conjugate_mem_borel_iff g x).mp hx
      simp only [dif_pos hx, borelSign_apply, contribution, if_pos hfix]
      simp only [conjugate_firstEntry_eq_one g x hx]
      split_ifs <;> norm_num
    · have hfix := (conjugate_mem_borel_iff g x).not.mp hx
      simp [hx, contribution, hfix]
  have hsum : (∑ x : G, (contribution g.val x.val : ℂ)) = (rawValue g.val : ℂ) := by
    calc
      _ = ∑ A : {A : M // A.det ≠ 0}, (contribution g.val A.val : ℂ) :=
        Fintype.sum_equiv matrixEquiv _ _ (fun _ => rfl)
      _ = ∑ A ∈ Finset.univ.filter (fun A : M => A.det ≠ 0),
          (contribution g.val A : ℂ) := by
        symm
        exact Finset.sum_subtype _ (by simp) _
      _ = _ := by simp [rawValue]
  unfold glTwoThreeDegreeFourCharacter inducedClassFunction
  simp only [borel_card, hterm, hsum]
  ring

private theorem class_rawValue : ∀ i : Fin 8,
    rawValue (threeClassRepr i).val = ![48,-48,0,12,-12,0,0,0] i := by
  decide +kernel

/-- The degree-four row in Wong's source column order. -/
public theorem glTwoThreeDegreeFourCharacter_values (i : Fin 8) :
    glTwoThreeDegreeFourCharacter (threeClassRepr i) =
      ![4,-4,0,1,-1,0,0,0] i := by
  rw [row_apply, class_rawValue]
  fin_cases i <;> norm_num

private theorem matrix_norm_sum :
    ∑ A ∈ Finset.univ.filter (fun A : M => A.det ≠ 0), (rawValue A)^2 = 6912 := by
  decide +kernel

private theorem row_norm :
    scalarProduct G glTwoThreeDegreeFourCharacter glTwoThreeDegreeFourCharacter = 1 := by
  classical
  have hcard : Nat.card G = 48 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_two]
  have hsum : (∑ g : G, (rawValue g.val : ℂ)^2) = 6912 := by
    calc
      (∑ g : G, (rawValue g.val : ℂ)^2) =
          ∑ A : {A : M // A.det ≠ 0}, (rawValue A.val : ℂ)^2 :=
        Fintype.sum_equiv matrixEquiv _ _ (fun _ => rfl)
      _ = ∑ A ∈ Finset.univ.filter (fun A : M => A.det ≠ 0), (rawValue A : ℂ)^2 := by
        symm
        exact Finset.sum_subtype _ (by simp) _
      _ = 6912 := by exact_mod_cast matrix_norm_sum
  unfold scalarProduct
  simp only [hcard, row_apply, star_div₀, star_intCast, star_ofNat]
  simp_rw [div_mul_div_comm, ← pow_two]
  rw [← Finset.sum_div, hsum]
  norm_num

/-- The actual induced degree-four character is irreducible. -/
public theorem glTwoThreeDegreeFourCharacter_irreducible :
    IsIrreducibleCharacter glTwoThreeDegreeFourCharacter := by
  apply BenderGlauberman.isIrreducibleCharacter_of_norm_one_inv
    glTwoThreeDegreeFourCharacter_isCharacter
  rw [← BenderGlauberman.star_scalarProduct_eq_inv_of_char
    glTwoThreeDegreeFourCharacter_isCharacter, row_norm, star_one]

end
end ABG
