module
public import BenderGlauberman.Lemma19
public import Theory.Representation.GLTwoBorelIndex
public import Theory.SpecificGroups.GL2.ThreeConjugacy

/-!
# The degree-three Borel permutation character of GL2(3)

For the actual upper-triangular subgroup `GLTwo.borelSubgroup (ZMod 3)`,
the character induced from its trivial representation, minus the trivial
character, is irreducible. Its values on the eight specified matrix classes
are `[3,3,-1,0,0,1,-1,-1]`. This is row four of Wong's table and supplies
one of the actual representations needed by the full character-table assembly.

A conjugator contributes to induction precisely when the matrix preserves
the line spanned by the conjugator's first column. Multiplication by its
nonzero determinant identifies this condition with membership of the
conjugate in the existing Borel. An explicit equivalence transfers the
conjugator count to the 81 matrices over `ZMod 3`; Lean's kernel checks the
eight counts and the integer sum giving scalar-product norm one. Induction
of the trivial representation gives a genuine character, so its difference
with the trivial character is a generalized character. The signed norm-one
criterion and its positive degree three then prove irreducibility.

Source: W. J. Wong, On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2, J. Austral. Math. Soc. 4 (1964), Table 1, article p. 97,
DOI:10.1017/S1446788700022771. The column representatives and their order are
those of `Matrix.GeneralLinearGroup.threeClassRepr`.
-/

open Matrix Matrix.GeneralLinearGroup
open scoped BigOperators
namespace ABG
noncomputable section

private abbrev G := GL (Fin 2) (ZMod 3)
private abbrev M := Matrix (Fin 2) (Fin 2) (ZMod 3)

/-- The actual Borel permutation character with its trivial constituent removed. -/
@[expose] public def glTwoThreeBorelPermutationCharacter : ClassFunction (GL (Fin 2) (ZMod 3)) :=
  inducedClassFunction (GLTwo.borelSubgroup (ZMod 3)) 1 - 1

private def matrixEquiv : G ≃ {A : M // A.det ≠ 0} where
  toFun g := ⟨g.val, g.det_ne_zero⟩
  invFun A := mkOfDetNeZero A.val A.property
  left_inv _ := Units.ext rfl
  right_inv _ := Subtype.ext rfl

private abbrev fixedCondition (A B : M) : Prop :=
  B 0 0 * (A * B) 1 0 = B 1 0 * (A * B) 0 0

private theorem conjugate_mem_borel_iff (g x : G) :
    x⁻¹ * g * x ∈ GLTwo.borelSubgroup (ZMod 3) ↔ fixedCondition g.val x.val := by
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

private def fixedCount (A : M) : ℕ :=
  (Finset.univ.filter (fun B : M => B.det ≠ 0 ∧ fixedCondition A B)).card

private def conjugatorEquiv (g : G) :
    {x : G // x⁻¹ * g * x ∈ GLTwo.borelSubgroup (ZMod 3)} ≃
      {B : M // B.det ≠ 0 ∧ fixedCondition g.val B} where
  toFun x := ⟨x.val.val, x.val.det_ne_zero,
    (conjugate_mem_borel_iff g x.val).mp x.property⟩
  invFun B := ⟨mkOfDetNeZero B.val B.property.1,
    (conjugate_mem_borel_iff g _).mpr B.property.2⟩
  left_inv _ := Subtype.ext (Units.ext rfl)
  right_inv _ := Subtype.ext rfl

private theorem borel_card : Nat.card (GLTwo.borelSubgroup (ZMod 3)) = 12 := by
  have h := (GLTwo.borelSubgroup (ZMod 3)).index_mul_card
  rw [GLTwo.borelSubgroup_index, Matrix.card_GL_field] at h
  norm_num [Fin.prod_univ_two] at h ⊢
  omega

private theorem induced_one_apply (g : G) :
    inducedClassFunction (GLTwo.borelSubgroup (ZMod 3)) 1 g = (fixedCount g.val : ℂ) / 12 := by
  classical
  unfold inducedClassFunction
  simp only [Pi.one_apply, borel_card, dite_eq_ite]
  have hsum : (∑ x : G, if x⁻¹ * g * x ∈ GLTwo.borelSubgroup (ZMod 3) then (1 : ℂ) else 0) =
      (fixedCount g.val : ℂ) := by
    have hc := Nat.card_congr (conjugatorEquiv g)
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
    change (Finset.univ.filter (fun x : G => x⁻¹ * g * x ∈ GLTwo.borelSubgroup (ZMod 3))).card =
      fixedCount g.val at hc
    rw [Finset.card_filter] at hc
    exact_mod_cast hc
  rw [hsum]
  ring

private theorem class_fixed_count : ∀ i : Fin 8,
    fixedCount (threeClassRepr i).val = ![48,48,0,12,12,24,0,0] i := by
  decide +kernel

/-- The eight values in Wong Table 1, row four and source column order. -/
public theorem glTwoThreeBorelPermutationCharacter_values (i : Fin 8) :
    glTwoThreeBorelPermutationCharacter (threeClassRepr i) =
      ![3,3,-1,0,0,1,-1,-1] i := by
  change inducedClassFunction (GLTwo.borelSubgroup (ZMod 3)) 1 (threeClassRepr i) - 1 = _
  rw [induced_one_apply, class_fixed_count]
  fin_cases i <;> norm_num

private def rawValue (A : M) : ℤ := fixedCount A - 12

private theorem matrix_norm_sum :
    ∑ A ∈ Finset.univ.filter (fun A : M => A.det ≠ 0), (rawValue A)^2 = 6912 := by
  decide +kernel

private theorem row_apply (g : G) :
    glTwoThreeBorelPermutationCharacter g = (rawValue g.val : ℂ) / 12 := by
  change inducedClassFunction (GLTwo.borelSubgroup (ZMod 3)) 1 g - 1 = _
  rw [induced_one_apply]
  simp only [rawValue, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat]
  ring

private theorem row_norm :
    scalarProduct G glTwoThreeBorelPermutationCharacter glTwoThreeBorelPermutationCharacter = 1 := by
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

/-- Removing the trivial constituent of the Borel permutation representation gives
a genuine irreducible character of degree three. -/
public theorem glTwoThreeBorelPermutationCharacter_irreducible :
    IsIrreducibleCharacter glTwoThreeBorelPermutationCharacter := by
  let : Fintype (GLTwo.borelSubgroup (ZMod 3)) := Fintype.ofFinite _
  have hone : IsCharacter (1 : ClassFunction G) :=
    BenderGlauberman.isCharacter_of_isIrreducibleCharacter
      BenderGlauberman.isLinearCharacter_one.1
  have hind : IsCharacter (inducedClassFunction (GLTwo.borelSubgroup (ZMod 3)) 1) :=
    BenderGlauberman.isCharacter_induced _
      (BenderGlauberman.isCharacter_of_isIrreducibleCharacter
        BenderGlauberman.isLinearCharacter_one.1)
  have hgen : IsGeneralizedCharacter glTwoThreeBorelPermutationCharacter :=
    ⟨_, _, hind, hone, rfl⟩
  obtain ⟨χ, hχ, heq | heq⟩ := BenderGlauberman.norm_one_signed_irreducible hgen row_norm
  · rwa [heq]
  · have hthree : glTwoThreeBorelPermutationCharacter 1 = 3 :=
      glTwoThreeBorelPermutationCharacter_values 0
    obtain ⟨n, ρ, _, rfl⟩ := hχ
    have h := congrFun heq 1
    rw [hthree] at h
    simp only [Pi.neg_apply, Representation.char_one, Module.finrank_pi, Fintype.card_fin] at h
    have hre := congrArg Complex.re h
    norm_num at hre
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

end
end ABG
