module

public import Theory.SpecificGroups.ClassicalUnitary.A02ParabolicSections.Geometry
public import Theory.SpecificGroups.ClassicalUnitary.TheoremDRootNormalizer
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicTorus

/-!
# Coordinates for the swapped unitary three-tori

A coordinate interchange conjugates a diagonal matrix by permuting its entries.
In dimension at least six, three tail entries carry the parameters and their
inverse product occupies a fourth coordinate. In dimension five, the parameters
are changed to `(abc,a⁻²,b⁻²)`, giving diagonal entries `(abc,abc,a⁻²,b⁻²,c⁻²)`.
The change is injective because squaring is injective in characteristic two.

The conjugation identities use product invariance and the three distinguished
coordinates, without expanding dense matrix products. These are the concrete
swapped tori used in Aschbacher--Smith A.2.18, printed p.40.
-/

@[expose] public noncomputable section
open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.ClassicalUnitary.A02ParabolicSections.SwappedTori
variable {F : Type*} [Field F] [CharP F 2]

/-- Coordinate interchanges conjugate diagonal special-unitary matrices. -/
theorem swap_diagonal {d : ℕ} (J : HermitianForm d F) (hJ : J.form = 1)
    (i j : Fin d) (hij : i ≠ j) (A B : J.specialSubgroup)
    (a b : Fin d → F) (hA : A.val.val = diagonal a) (hB : B.val.val = diagonal b)
    (hab : ∀ x, a (Equiv.swap i j x) = b x) :
    swapSpecial J hJ i j hij * A * (swapSpecial J hJ i j hij)⁻¹ = B := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  apply Units.ext
  change (Equiv.swap i j).permMatrix F * A.val.val = B.val.val * (Equiv.swap i j).permMatrix F
  rw [hA, hB]
  ext x y
  rw [mul_diagonal, diagonal_mul]
  by_cases he : Equiv.swap i j x = y
  · subst y
    simp [hab]
  · simp [he]

/-- The three distinguished tail coordinates in dimension `6+k`. -/
def tailSix (k : ℕ) (i : Fin 3) : Fin (6+k) := Fin.castAdd k (![2,3,4] i)

theorem tailSix_val (k : ℕ) (i : Fin 3) : (tailSix k i).val = 2+i.val := by
  fin_cases i <;> rfl

theorem tailSix_injective (k : ℕ) : Function.Injective (tailSix k) := by
  intro i j h
  have he := congrArg Fin.val h
  simp only [tailSix_val] at he
  apply Fin.ext
  omega

theorem triple_swap {C : Type*} [CommGroup C] (a : Fin 3 → C) (i j : Fin 3) :
    a (Equiv.swap i j 0)*a (Equiv.swap i j 1)*a (Equiv.swap i j 2) = a 0*a 1*a 2 := by
  simpa [Fin.prod_univ_succ, mul_assoc] using (Equiv.prod_comp (Equiv.swap i j) a)

omit [CharP F 2] in
theorem six_tail (k : ℕ) (C : Subgroup Fˣ) (a : Fin 3 → C) (i : Fin 3) :
    Theory.SpecificGroups.UnitaryRootNormalizer.torusEntries k C a (tailSix k i) = a i := by
  fin_cases i <;> simp [tailSix, Theory.SpecificGroups.UnitaryRootNormalizer.torusEntries]

theorem six_swap_fixed (k : ℕ) (i j : Fin 3) (x : Fin (6+k))
    (hx : x.val < 2 ∨ 5 ≤ x.val) : Equiv.swap (tailSix k i) (tailSix k j) x = x := by
  apply Equiv.swap_apply_of_ne_of_ne <;> intro h
  all_goals
    have hh := congrArg Fin.val h
    simp only [tailSix_val] at hh
    omega

omit [CharP F 2] in
theorem six_entries (k : ℕ) (C : Subgroup Fˣ) (a : Fin 3 → C)
    (i j : Fin 3) (x : Fin (6+k)) :
    Theory.SpecificGroups.UnitaryRootNormalizer.torusEntries k C a
      (Equiv.swap (tailSix k i) (tailSix k j) x) =
    Theory.SpecificGroups.UnitaryRootNormalizer.torusEntries k C
      (a ∘ Equiv.swap i j) x := by
  have ht (l : Fin 3) :
      Theory.SpecificGroups.UnitaryRootNormalizer.torusEntries k C a
        (Equiv.swap (tailSix k i) (tailSix k j) (tailSix k l)) =
      Theory.SpecificGroups.UnitaryRootNormalizer.torusEntries k C (a ∘ Equiv.swap i j) (tailSix k l) := by
    rw [← (tailSix_injective k).map_swap, six_tail, six_tail]
    rfl
  refine Fin.addCases ?_ ?_ x
  · intro l
    fin_cases l
    · rw [six_swap_fixed k i j _ (Or.inl (by simp))]
      simp [Theory.SpecificGroups.UnitaryRootNormalizer.torusEntries]
    · rw [six_swap_fixed k i j _ (Or.inl (by simp))]
      simp [Theory.SpecificGroups.UnitaryRootNormalizer.torusEntries]
    · exact ht 0
    · exact ht 1
    · exact ht 2
    · rw [six_swap_fixed k i j _ (Or.inr (by simp))]
      exact congrArg Inv.inv (triple_swap a i j).symm
  · intro l
    rw [six_swap_fixed k i j _ (Or.inr (by simp; omega))]
    simp [Theory.SpecificGroups.UnitaryRootNormalizer.torusEntries]

/-- The parameter change making the five-dimensional torus symmetric in three axes. -/
def fiveParameters (C : Subgroup Fˣ) : (Fin 3 → C) →* (Fin 3 → C) where
  toFun a := ![a 0*a 1*a 2, (a 0 ^ 2)⁻¹, (a 1 ^ 2)⁻¹]
  map_one' := by ext i; fin_cases i <;> simp
  map_mul' a b := by
    ext i
    fin_cases i <;> simp [mul_pow, mul_assoc, mul_comm, mul_left_comm]

omit [CharP F 2] in
theorem five_shape (C : Subgroup Fˣ) (a : Fin 3 → C) :
    Theory.SpecificGroups.UnitaryFive.torusEntries C (fiveParameters C a) =
      ![a 0*a 1*a 2, a 0*a 1*a 2, (a 0 ^ 2)⁻¹, (a 1 ^ 2)⁻¹, (a 2 ^ 2)⁻¹] := by
  ext i
  fin_cases i <;> simp [Theory.SpecificGroups.UnitaryFive.torusEntries, fiveParameters,
    mul_pow, mul_assoc, mul_comm, mul_left_comm]

omit [CharP F 2] in
theorem five_tail (C : Subgroup Fˣ) (a : Fin 3 → C) (i : Fin 3) :
    Theory.SpecificGroups.UnitaryFive.torusEntries C (fiveParameters C a) (Fin.natAdd 2 i) =
      (a i ^ 2)⁻¹ := by
  rw [five_shape]
  fin_cases i <;> rfl

theorem five_swap_fixed (i j : Fin 3) (x : Fin 5) (hx : x.val < 2) :
    Equiv.swap (Fin.natAdd 2 i) (Fin.natAdd 2 j) x = x := by
  apply Equiv.swap_apply_of_ne_of_ne <;> intro h
  all_goals
    have hh := congrArg Fin.val h
    simp only [Fin.val_natAdd] at hh
    omega

omit [CharP F 2] in
theorem five_entries (C : Subgroup Fˣ) (a : Fin 3 → C) (i j : Fin 3) (x : Fin 5) :
    Theory.SpecificGroups.UnitaryFive.torusEntries C (fiveParameters C a)
      (Equiv.swap (Fin.natAdd 2 i) (Fin.natAdd 2 j) x) =
    Theory.SpecificGroups.UnitaryFive.torusEntries C (fiveParameters C (a ∘ Equiv.swap i j)) x := by
  have ht (l : Fin 3) :
      Theory.SpecificGroups.UnitaryFive.torusEntries C (fiveParameters C a)
        (Equiv.swap (Fin.natAdd 2 i) (Fin.natAdd 2 j) (Fin.natAdd 2 l)) =
      Theory.SpecificGroups.UnitaryFive.torusEntries C (fiveParameters C (a ∘ Equiv.swap i j))
        (Fin.natAdd 2 l) := by
    rw [← (Fin.natAdd_injective 3 2).map_swap, five_tail, five_tail]
    rfl
  fin_cases x
  · rw [five_swap_fixed i j _ (by decide), five_shape, five_shape]
    exact (triple_swap a i j).symm
  · rw [five_swap_fixed i j _ (by decide), five_shape, five_shape]
    exact (triple_swap a i j).symm
  · exact ht 0
  · exact ht 1
  · exact ht 2

/-- Characteristic-two square injectivity makes the parameter change faithful. -/
theorem fiveParameters_injective (C : Subgroup Fˣ) : Function.Injective (fiveParameters C) := by
  have hs : Function.Injective (fun u : C => u ^ 2) := by
    intro u v h
    apply Subtype.ext
    apply Units.ext
    have he := congrArg (fun u : C => (u.val : F)) h
    change (u.val : F)^2 = (v.val : F)^2 at he
    simpa [sq_eq_sq_iff_eq_or_eq_neg, CharTwo.neg_eq] using he
  intro a b h
  have h0 : a 0 = b 0 := hs (inv_injective (congrFun h 1))
  have h1 : a 1 = b 1 := hs (inv_injective (congrFun h 2))
  have h2 := congrFun h 0
  change a 0*a 1*a 2 = b 0*b 1*b 2 at h2
  rw [h0, h1] at h2
  have h2' := mul_left_cancel h2
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2'

end Theory.SpecificGroups.ClassicalUnitary.A02ParabolicSections.SwappedTori
