module

public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.ThreePrimary.MatrixTorus.Weyl

/-!
# Fixed points of the coordinate cycle on the projective unitary torus

For any subgroup `C` of norm-one units, a projective diagonal element
commutes with the coordinate cycle exactly when both coordinates have cube
one. Dividing by the scalar last coordinate gives the unique representative
`diag(u,u⁻¹,1)` with `u³ = 1`. Thus the fixed subgroup of the literal
projective torus is isomorphic to the cubic torsion of `C`, and over a finite
field its order is `gcd(|C|,3)`.

The full torus retains its original order, including higher three-valuations
such as the norm-one group of order nine for `q = 8`. The norm-one
specialization discharges the fixed-cardinality premise of
`configurationOfCounts` and `nonempty_of_identity_counts` in `MatrixTorus`.

Source: the unitary local calculation used for Aschbacher–Smith I.1.3(2),
printed p.407 (PDF p.418); GLS III, Theorem 6.1.4 and Tables 6.1.2–3.
This is a matrix fixed-point calculation, independent of covering and
multiplier hypotheses.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.ThreePrimary.MatrixTorus
variable {F : Type*} [Field F]
variable (J : HermitianForm 3 F) (hJ : J.form = 1)
variable (C : Subgroup Fˣ) (hC : ∀ u : C, J.conj (u.val : F) * (u.val : F) = 1)

private theorem cubic_coordinates {G : Type*} [CommGroup G] (a b : G) :
    ((a * b)⁻¹ * a⁻¹ = a * b⁻¹ ∧ ((a * b)⁻¹ * a⁻¹) ^ 3 = 1) ↔
      a ^ 3 = 1 ∧ b ^ 3 = 1 := by
  constructor
  · rintro ⟨he, hc⟩
    have ha : a ^ 3 = 1 := by
      have hh := congrArg (fun x => x * a ^ 2 * b) he
      have hh' : 1 = a ^ 3 := by
        convert hh using 1 <;> simp [pow_succ, mul_assoc, mul_comm, mul_left_comm]
      exact hh'.symm
    refine ⟨ha, ?_⟩
    rw [he, mul_pow, inv_pow, ha, one_mul, inv_eq_one] at hc
    exact hc
  · rintro ⟨ha, hb⟩
    have he : (a * b)⁻¹ * a⁻¹ = a * b⁻¹ := by
      apply mul_right_cancel (b := a ^ 2 * b)
      calc
        (a * b)⁻¹ * a⁻¹ * (a ^ 2 * b) = 1 := by group
        _ = a ^ 3 := ha.symm
        _ = a * b⁻¹ * (a ^ 2 * b) := by
          simp [pow_succ, mul_assoc, mul_comm, mul_left_comm]
    exact ⟨he, by rw [he, mul_pow, inv_pow, ha, hb, inv_one, mul_one]⟩

/-- Projective commutation is precisely cubic torsion in both coordinates. -/
theorem diagonalProjective_mem_centralizer_cycle_iff (a : C × C) :
    diagonalProjective J hJ C hC a ∈ centralizer ({cycle J hJ} : Set _) ↔
      a.1 ^ 3 = 1 ∧ a.2 ^ 3 = 1 := by
  rw [mem_centralizer_singleton_iff]
  have he : diagonalProjective J hJ C hC a * cycle J hJ =
      cycle J hJ * diagonalProjective J hJ C hC a ↔
      diagonalProjective J hJ C hC (((a.1 * a.2)⁻¹, a.1) * a⁻¹) = 1 := by
    rw [map_mul, map_inv, mul_inv_eq_one, ← cycle_diagonal,
      mul_inv_eq_iff_eq_mul, eq_comm]
  rw [he, diagonalProjective_eq_one_iff]
  exact cubic_coordinates a.1 a.2

/-- Cubic diagonal coordinates admit a representative with last coordinate one. -/
theorem diagonalProjective_eq_first_of_cube (a : C × C) (hb : a.2 ^ 3 = 1) :
    diagonalProjective J hJ C hC a = first J hJ C hC (a.1 * a.2⁻¹) := by
  apply mul_inv_eq_one.mp
  rw [first, ← map_inv, ← map_mul, diagonalProjective_eq_one_iff]
  have he : a * (a.1 * a.2⁻¹, (1 : C))⁻¹ = (a.2, a.2) := by
    ext <;> simp
  rw [he]
  exact ⟨rfl, hb⟩

/-- Distinct first coordinates remain distinct in the projective quotient. -/
theorem first_injective : Function.Injective (first J hJ C hC) := by
  intro a b h
  have he : diagonalProjective J hJ C hC ((a, 1) * (b, 1)⁻¹) = 1 := by
    rw [map_mul, map_inv, mul_inv_eq_one]
    exact h
  have hk := ((diagonalProjective_eq_one_iff J hJ C hC _).mp he).1
  simpa only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv,
    mul_inv_cancel, mul_inv_eq_one] using hk

/-- Cubic first coordinates land in the literal fixed subgroup of the full torus. -/
def cubicFirst : (powMonoidHom 3 : C →* C).ker →*
    (torus J hJ C hC ⊓ centralizer ({cycle J hJ} : Set _) :
      Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) where
  toFun u := ⟨first J hJ C hC u.val, ⟨⟨(u.val, 1), rfl⟩,
    (diagonalProjective_mem_centralizer_cycle_iff J hJ C hC (u.val, 1)).mpr
      ⟨u.property, one_pow 3⟩⟩⟩
  map_one' := by
    apply Subtype.ext
    exact (diagonalProjective J hJ C hC).map_one
  map_mul' u v := by
    apply Subtype.ext
    change diagonalProjective J hJ C hC ((u * v).val, 1) =
      diagonalProjective J hJ C hC (u.val, 1) * diagonalProjective J hJ C hC (v.val, 1)
    rw [← map_mul]
    congr 1
    ext <;> simp

/-- The scalar quotient leaves exactly one cubic first-coordinate representative. -/
theorem cubicFirst_bijective : Function.Bijective (cubicFirst J hJ C hC) := by
  constructor
  · intro u v h
    apply Subtype.ext
    apply first_injective J hJ C hC
    exact congrArg Subtype.val h
  · rintro ⟨x, hx, hc⟩
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨ha, hb⟩ := (diagonalProjective_mem_centralizer_cycle_iff J hJ C hC a).mp hc
    refine ⟨⟨a.1 * a.2⁻¹, ?_⟩, ?_⟩
    · change (a.1 * a.2⁻¹) ^ 3 = 1
      rw [mul_pow, inv_pow, ha, hb, inv_one, mul_one]
    · apply Subtype.ext
      exact (diagonalProjective_eq_first_of_cube J hJ C hC a hb).symm

/-- An explicit isomorphism counts fixed points in the actual projective image. -/
def cubicFixedEquiv : (powMonoidHom 3 : C →* C).ker ≃*
    (torus J hJ C hC ⊓ centralizer ({cycle J hJ} : Set _) :
      Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
  MulEquiv.ofBijective (cubicFirst J hJ C hC) (cubicFirst_bijective J hJ C hC)

/-- Exact fixed-subgroup order after taking the scalar quotient. -/
theorem torus_fixed_card [Finite F] :
    Nat.card (torus J hJ C hC ⊓ centralizer ({cycle J hJ} : Set _) :
      Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = Nat.gcd (Nat.card C) 3 := by
  rw [← Nat.card_congr (cubicFixedEquiv J hJ C hC).toEquiv,
    IsCyclic.card_powMonoidHom_ker]

/-- The coordinate cycle fixes at most three elements of any such torus. -/
theorem torus_fixed_card_le [Finite F] :
    Nat.card (torus J hJ C hC ⊓ centralizer ({cycle J hJ} : Set _) :
      Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ 3 := by
  rw [torus_fixed_card]
  exact Nat.gcd_le_right _ (by decide)

/-- The literal fixed-cardinality bound consumed by the torus configuration. -/
theorem normOneTorus_fixed_card_le [Finite F] :
    Nat.card (normOneTorus J hJ ⊓ centralizer ({cycle J hJ} : Set _) :
      Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ 3 :=
  torus_fixed_card_le J hJ (EvenInner.normOne J) (normOne_norm J)

/-- The norm-one fixed subgroup has order `gcd(q+1,3)` for every quadratic field. -/
theorem normOneTorus_fixed_card [Finite F] {q : ℕ}
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q) :
    Nat.card (normOneTorus J hJ ⊓ centralizer ({cycle J hJ} : Set _) :
      Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = Nat.gcd (q + 1) 3 := by
  rw [normOneTorus, torus_fixed_card, EvenInner.normOne_card J hcard hconj]

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.ThreePrimary.MatrixTorus
