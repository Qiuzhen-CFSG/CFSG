module

public import Theory.SpecificGroups.ReeF4.Model
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Frobenius and two-power automorphisms of the concrete Ree carrier

Entrywise Frobenius commutes with the exceptional field twist, since both
are powers of the exceptional endomorphism. Restricting Frobenius to the
actual fixed subgroup gives a field automorphism of period `2 * m + 1`.
At `m = 0` this automorphism is the identity on the full group ²F₄(2).

If an automorphism is a product of an inner automorphism and a power of this
field automorphism, its outer class has odd order. A two-power-order such
automorphism is therefore inner, by coprimality in Aut(Model m)/Inn(Model m).
This proves the reduction, not the missing assertion that all two-power-order
automorphisms have that form. In particular the binary period calculation
does not identify Model 0 with Aut(Tits.ParrottGroup) or prove completeness.

Source: Aschbacher–Smith, F.1.12, printed pp.263–264 of
`refs/quasithin.pdf`; the field action uses the concrete exceptional-twist
construction of GLS3, Theorem 1.15.4 (`refs/KGroup/GLS3/Chapter1.tex`).
-/

public section
noncomputable section
namespace ReeF4.Parabolics.OuterLocal

/-- Frobenius preserves the fixed-point equation defining the Ree group. -/
theorem reeTwist_splitFrobenius (m : ℕ) (x : SplitGroup m) :
    reeTwist m (splitFrobenius m x) = splitFrobenius m (reeTwist m x) := by
  have h : Commute (reeTwist m) (splitFrobeniusEnd m) := by
    rw [reeTwist_eq_pow, ← exceptionalEndomorphism_sq]
    exact (Commute.refl _).pow_pow _ _
  exact DFunLike.congr_fun h.eq x

/-- Entrywise squaring restricted to the actual Ree fixed subgroup. -/
def modelFrobenius (m : ℕ) : Model m →* Model m where
  toFun x := ⟨splitFrobenius m x.val, by
    rw [mem_fixedSubgroup, reeTwist_splitFrobenius]
    exact congrArg (splitFrobenius m) ((mem_fixedSubgroup m x.val).mp x.property)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

/-- The restricted map still acts by the specified split Frobenius. -/
@[simp] theorem modelFrobenius_coe (m : ℕ) (x : Model m) :
    toSplitGroup m (modelFrobenius m x) = splitFrobenius m (toSplitGroup m x) := by
  simp only [toSplitGroup_apply]
  rfl

/-- Faithfulness follows from injectivity of squaring in the coefficient field. -/
theorem modelFrobenius_injective (m : ℕ) : Function.Injective (modelFrobenius m) := by
  intro x y h
  apply Subtype.ext
  exact splitFrobenius_injective m (congrArg Subtype.val h)

/-- The concrete coefficient-field automorphism of the Ree group. -/
def fieldAutomorphism (m : ℕ) : MulAut (Model m) :=
  MulEquiv.ofBijective (modelFrobenius m)
    (Finite.injective_iff_bijective.mp (modelFrobenius_injective m))

/-- Compatibility with the faithful inclusion in the split matrix group. -/
@[simp] theorem fieldAutomorphism_coe (m : ℕ) (x : Model m) :
    toSplitGroup m (fieldAutomorphism m x) = splitFrobenius m (toSplitGroup m x) := by
  simp only [toSplitGroup_apply]
  rfl

/-- Every iterated field automorphism agrees with iterated matrix Frobenius. -/
theorem fieldAutomorphism_pow_coe (m n : ℕ) (x : Model m) :
    toSplitGroup m ((fieldAutomorphism m ^ n) x) =
      (splitFrobeniusEnd m ^ n) (toSplitGroup m x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, fieldAutomorphism_coe, ih]
    rw [pow_succ']
    rfl

/-- The field automorphism squares every entry in the faithful representation. -/
theorem fieldAutomorphism_entry (m : ℕ) (x : Model m)
    (i j : Theory.AlgebraicGroup.F4Chevalley.BasisIndex) :
    (matrixRepresentation m (fieldAutomorphism m x) : MatrixCarrier m) i j =
      (matrixRepresentation m x : MatrixCarrier m) i j ^ 2 := by
  simp only [matrixRepresentation_apply]
  exact splitFrobenius_entry m x.val i j

/-- The odd coefficient-field degree is a period of the restricted automorphism. -/
theorem fieldAutomorphism_period (m : ℕ) :
    fieldAutomorphism m ^ (2 * m + 1) = 1 := by
  apply MulEquiv.ext
  intro x
  apply toSplitGroup_injective m
  rw [fieldAutomorphism_pow_coe, splitFrobenius_pow_fieldDegree]
  rfl

/-- The field part vanishes at the full binary Ree endpoint. -/
@[simp] theorem fieldAutomorphism_zero : fieldAutomorphism 0 = 1 := by
  simpa only [Nat.mul_zero, zero_add, pow_one] using fieldAutomorphism_period 0

/-- A supplied inner-times-field expression for a two-power automorphism has
trivial outer class. Existence of that expression is a separate model theorem. -/
theorem inner_of_twoPower_of_inner_field (m : ℕ) (α : MulAut (Model m))
    (g : Model m) (k n : ℕ)
    (hform : α = MulAut.conj g * fieldAutomorphism m ^ k)
    (hpow : α ^ (2 ^ n) = 1) : ∃ x : Model m, MulAut.conj x = α := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (Model m))
  have hconj : q (MulAut.conj g) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
  have hqform : q α = q (fieldAutomorphism m) ^ k := by
    rw [hform, map_mul, map_pow, hconj, one_mul]
  have hodd : q α ^ (2 * m + 1) = 1 := by
    rw [hqform, pow_right_comm, ← map_pow, fieldAutomorphism_period, map_one, one_pow]
  have htwo : q α ^ (2 ^ n) = 1 := by rw [← map_pow, hpow, map_one]
  have hcop : Nat.Coprime (2 ^ n) (2 * m + 1) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr ⟨m, rfl⟩)
  have horder : orderOf (q α) = 1 := by
    apply Nat.dvd_one.mp
    simpa only [hcop.gcd_eq_one] using
      Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr htwo)
        (orderOf_dvd_iff_pow_eq_one.mpr hodd)
  have hq : q α = 1 := orderOf_eq_one_iff.mp horder
  exact (QuotientGroup.eq_one_iff _).mp hq

end ReeF4.Parabolics.OuterLocal
