module
public import BenderGlauberman.Lemma19
public import Theory.SpecificGroups.GL2.ThreeConjugacy

/-!
# Wong's nonfaithful degree-two character of GL2(3)

The matrices `a^k` and `a^k*f`, for `k < 8`, where `a = threeRotation`
and `f = !![1,1;0,2]`, form a subgroup of order sixteen of the actual
matrix group. Its permutation character has degree three. Subtracting the
trivial character gives the irreducible character with values
`[2,2,2,-1,-1,0,0,0]` on `threeClassRepr`.

Finite matrix calculations checked by Lean's kernel establish subgroup
closure, its cardinality, and the induction counts. An explicit equivalence
with invertible matrices transfers those counts to the group. The resulting
generalized character has scalar-product norm one and positive degree, so
the signed irreducibility criterion gives a genuine irreducible character.

Source: W. J. Wong, On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2, J. Austral. Math. Soc. 4 (1964), Table 1, p. 97,
DOI:10.1017/S1446788700022771, the row φ₂.
-/

open Matrix Matrix.GeneralLinearGroup
open scoped BigOperators
namespace ABG
noncomputable section

private abbrev G := GL (Fin 2) (ZMod 3)
private abbrev M := Matrix (Fin 2) (Fin 2) (ZMod 3)

private def frobeniusMatrix : G :=
  mkOfDetNeZero !![(1 : ZMod 3),1;0,2] (by decide)

private def normalizerElement (i : Fin 16) : G :=
  if i.val < 8 then threeRotation ^ i.val
  else threeRotation ^ (i.val - 8) * frobeniusMatrix

private theorem normalizer_mul : ∀ i j : Fin 16,
    ∃ k : Fin 16, normalizerElement i * normalizerElement j = normalizerElement k := by
  decide +kernel

private theorem normalizer_inv : ∀ i : Fin 16,
    ∃ j : Fin 16, (normalizerElement i)⁻¹ = normalizerElement j := by
  decide +kernel

private def torusNormalizer : Subgroup G where
  carrier := {g | ∃ i : Fin 16, g = normalizerElement i}
  one_mem' := ⟨0, by decide +kernel⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact normalizer_mul i j
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact normalizer_inv i

/-- The index-three permutation character with its trivial constituent removed. -/
public def glTwoThreeDegreeTwoCharacter : ClassFunction (GL (Fin 2) (ZMod 3)) :=
  inducedClassFunction torusNormalizer 1 - 1

private def matrixEquiv : G ≃ {A : M // A.det ≠ 0} where
  toFun g := ⟨g.val, g.det_ne_zero⟩
  invFun A := mkOfDetNeZero A.val A.property
  left_inv _ := Units.ext rfl
  right_inv _ := Subtype.ext rfl

private abbrev fixedCondition (A B : M) : Prop :=
  ∃ i : Fin 16, A * B = B * (normalizerElement i).val

private theorem conjugate_mem_normalizer_iff (g x : G) :
    x⁻¹ * g * x ∈ torusNormalizer ↔ fixedCondition g.val x.val := by
  change (∃ i : Fin 16, x⁻¹ * g * x = normalizerElement i) ↔ _
  constructor
  · rintro ⟨i, hi⟩
    have h : g * x = x * normalizerElement i := by
      rw [← hi]
      simp [mul_assoc]
    exact ⟨i, congrArg Units.val h⟩
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have h : g * x = x * normalizerElement i := Units.ext hi
    calc
      x⁻¹ * g * x = x⁻¹ * (g * x) := mul_assoc _ _ _
      _ = normalizerElement i := by rw [h]; simp

private def fixedCount (A : M) : ℕ :=
  (Finset.univ.filter (fun B : M => B.det ≠ 0 ∧ fixedCondition A B)).card

private def conjugatorEquiv (g : G) :
    {x : G // x⁻¹ * g * x ∈ torusNormalizer} ≃
      {B : M // B.det ≠ 0 ∧ fixedCondition g.val B} where
  toFun x := ⟨x.val.val, x.val.det_ne_zero,
    (conjugate_mem_normalizer_iff g x.val).mp x.property⟩
  invFun B := ⟨mkOfDetNeZero B.val B.property.1,
    (conjugate_mem_normalizer_iff g _).mpr B.property.2⟩
  left_inv _ := Subtype.ext (Units.ext rfl)
  right_inv _ := Subtype.ext rfl

private def normalizerMatrixEquiv : torusNormalizer ≃
    {A : M // A.det ≠ 0 ∧ ∃ i : Fin 16, A = (normalizerElement i).val} where
  toFun g := ⟨g.val.val, g.val.det_ne_zero, by
    obtain ⟨i, hi⟩ := g.property
    exact ⟨i, congrArg Units.val hi⟩⟩
  invFun A := ⟨mkOfDetNeZero A.val A.property.1, by
    obtain ⟨i, hi⟩ := A.property.2
    exact ⟨i, Units.ext hi⟩⟩
  left_inv _ := Subtype.ext (Units.ext rfl)
  right_inv _ := Subtype.ext rfl

private theorem normalizer_card : Nat.card torusNormalizer = 16 := by
  rw [Nat.card_congr normalizerMatrixEquiv, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

private theorem induced_one_apply (g : G) :
    inducedClassFunction torusNormalizer 1 g = (fixedCount g.val : ℂ) / 16 := by
  classical
  unfold inducedClassFunction
  simp only [Pi.one_apply, normalizer_card, dite_eq_ite]
  have hsum : (∑ x : G, if x⁻¹ * g * x ∈ torusNormalizer then (1 : ℂ) else 0) =
      (fixedCount g.val : ℂ) := by
    have hc := Nat.card_congr (conjugatorEquiv g)
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
    change (Finset.univ.filter (fun x : G => x⁻¹ * g * x ∈ torusNormalizer)).card =
      fixedCount g.val at hc
    rw [Finset.card_filter] at hc
    exact_mod_cast hc
  rw [hsum]
  ring

private theorem class_fixed_count : ∀ i : Fin 8,
    fixedCount (threeClassRepr i).val = ![48,48,48,0,0,16,16,16] i := by
  decide +kernel

/-- The eight values in Wong Table 1, row φ₂ and source column order. -/
public theorem glTwoThreeDegreeTwoCharacter_values (i : Fin 8) :
    glTwoThreeDegreeTwoCharacter (threeClassRepr i) =
      ![2,2,2,-1,-1,0,0,0] i := by
  change inducedClassFunction torusNormalizer 1 (threeClassRepr i) - 1 = _
  rw [induced_one_apply, class_fixed_count]
  fin_cases i <;> norm_num

private def rawValue (A : M) : ℤ := fixedCount A - 16

private theorem matrix_norm_sum :
    ∑ A ∈ Finset.univ.filter (fun A : M => A.det ≠ 0), (rawValue A)^2 = 12288 := by
  decide +kernel

private theorem row_apply (g : G) :
    glTwoThreeDegreeTwoCharacter g = (rawValue g.val : ℂ) / 16 := by
  change inducedClassFunction torusNormalizer 1 g - 1 = _
  rw [induced_one_apply]
  simp only [rawValue, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat]
  ring

private theorem row_norm :
    scalarProduct G glTwoThreeDegreeTwoCharacter glTwoThreeDegreeTwoCharacter = 1 := by
  classical
  have hcard : Nat.card G = 48 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_two]
  have hsum : (∑ g : G, (rawValue g.val : ℂ)^2) = 12288 := by
    calc
      (∑ g : G, (rawValue g.val : ℂ)^2) =
          ∑ A : {A : M // A.det ≠ 0}, (rawValue A.val : ℂ)^2 :=
        Fintype.sum_equiv matrixEquiv _ _ (fun _ => rfl)
      _ = ∑ A ∈ Finset.univ.filter (fun A : M => A.det ≠ 0), (rawValue A : ℂ)^2 := by
        symm
        exact Finset.sum_subtype _ (by simp) _
      _ = 12288 := by exact_mod_cast matrix_norm_sum
  unfold scalarProduct
  simp only [hcard, row_apply, star_div₀, star_intCast, star_ofNat]
  simp_rw [div_mul_div_comm, ← pow_two]
  rw [← Finset.sum_div, hsum]
  norm_num

/-- Wong’s nonfaithful degree-two row is a genuine irreducible character. -/
public theorem glTwoThreeDegreeTwoCharacter_irreducible :
    IsIrreducibleCharacter glTwoThreeDegreeTwoCharacter := by
  let : Fintype torusNormalizer := Fintype.ofFinite _
  have hone : IsCharacter (1 : ClassFunction G) :=
    BenderGlauberman.isCharacter_of_isIrreducibleCharacter
      BenderGlauberman.isLinearCharacter_one.1
  have hind : IsCharacter (inducedClassFunction torusNormalizer 1) :=
    BenderGlauberman.isCharacter_induced _
      (BenderGlauberman.isCharacter_of_isIrreducibleCharacter
        BenderGlauberman.isLinearCharacter_one.1)
  have hgen : IsGeneralizedCharacter glTwoThreeDegreeTwoCharacter :=
    ⟨_, _, hind, hone, rfl⟩
  obtain ⟨χ, hχ, heq | heq⟩ := BenderGlauberman.norm_one_signed_irreducible hgen row_norm
  · rwa [heq]
  · have htwo : glTwoThreeDegreeTwoCharacter 1 = 2 :=
      glTwoThreeDegreeTwoCharacter_values 0
    obtain ⟨n, ρ, _, rfl⟩ := hχ
    have h := congrFun heq 1
    rw [htwo] at h
    simp only [Pi.neg_apply, Representation.char_one, Module.finrank_pi, Fintype.card_fin] at h
    have hre := congrArg Complex.re h
    norm_num at hre
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

end
end ABG
