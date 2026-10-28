module

public import Stellmacher.Recognition.FongWreathedRationalConstituents
public import Stellmacher.Recognition.FongWreathedInducedCharacters
public import Stellmacher.Recognition.FongWreathedLocalBlocks
public import Theory.Character.AntiRealNormFour
public import Theory.Character.ModularBlock.EightColumnSaturation

/-!
# The eight exceptional irreducible characters

The first packet consists of the principal character and the three rational
irreducibles already extracted from the first induced character. The second
induced character is anti-real. Conjugation and integral multiplicities show
that none of the first four characters occurs in it. This establishes the
disjointness needed for the eight-character column calculation independently
of the scalar-product orthogonality of the two induced functions.

Norm four extracts the second packet as two complex-conjugate pairs. The
eight genuine principal-block members saturate the column norm at F and F³;
the two signed induced-character values therefore force all eight entries.
`EightConstituents` retains the irreducibles, their membership, both signed
decompositions, and the two columns of equation (10).

Source: P. Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)*, J. Algebra 6 (1967), printed pp.72–73, equation (10).
-/

public section
noncomputable section
open Theory.Character BenderGlauberman
open scoped BigOperators
attribute [local instance] Fintype.ofFinite

namespace Stellmacher.Recognition
variable {G : Type*} [Group G] [Finite G]

namespace FongRationalConstituents
variable {Θ : ClassFunction G} {J : G} (r : FongRationalConstituents Θ J)

/-- The rational packet, with the principal character first. -/
@[expose] def four : Fin 4 → ClassFunction G := ![1, r.χ₂, r.χ₃, r.χ₄]

omit [Finite G] in
theorem four_irreducible (i : Fin 4) : IsIrreducibleCharacter (r.four i) := by
  fin_cases i
  · exact _root_.isIrreducibleCharacter_one
  · exact r.irreducible.1
  · exact r.irreducible.2.1
  · exact r.irreducible.2.2

omit [Finite G] in
theorem four_injective : Function.Injective r.four := by
  intro i j he
  have hn := r.nonprincipal
  have hd := r.distinct
  fin_cases i <;> fin_cases j <;>
    simp_all [four, Ne.symm]

omit [Finite G] in
theorem four_integer (i : Fin 4) (g : G) : ∃ z : ℤ, r.four i g = (z : ℂ) := by
  fin_cases i
  · exact ⟨1, by simp [four]⟩
  · exact r.integer_values.1 g
  · exact r.integer_values.2.1 g
  · exact r.integer_values.2.2 g

omit [Finite G] in
theorem four_real (i : Fin 4) (g : G) : star (r.four i g) = r.four i g := by
  obtain ⟨z, hz⟩ := r.four_integer i g
  simp [hz]

/-- Each rational constituent occurs, with the prescribed sign. -/
theorem four_coefficient (i : Fin 4) :
    scalarProduct G Θ (r.four i) = (![1, 1, -1, -1] : Fin 4 → ℂ) i := by
  conv_lhs => arg 2; rw [r.decomposition]
  simp only [_root_.scalarProduct_sub_left, _root_.scalarProduct_add_left]
  have h₀ := _root_.isIrreducibleCharacter_one (G := G)
  rw [scalarProduct_irr_ite h₀ (r.four_irreducible i),
    scalarProduct_irr_ite r.irreducible.1 (r.four_irreducible i),
    scalarProduct_irr_ite r.irreducible.2.1 (r.four_irreducible i),
    scalarProduct_irr_ite r.irreducible.2.2 (r.four_irreducible i)]
  have hn := r.nonprincipal
  have hd := r.distinct
  fin_cases i <;> simp_all [four, Ne.symm]

end FongRationalConstituents

namespace FongWreathedInduction

/-- The local second inducing function is anti-real. -/
theorem InducingData.thetaTwo_antiReal (d : InducingData G) (h : d.H) :
    star (thetaTwo d.alpha d.beta h) = -thetaTwo d.alpha d.beta h := by
  have hb : star (d.beta h) = d.beta h := by
    rcases sq_eq_one_iff.mp (d.beta_two h) with he | he <;> simp [he]
  rw [thetaTwo_conj_formula d.alpha d.beta d.alpha_four]
  simp only [star_mul, star_sub, star_star, star_add, star_one, hb]
  ring

/-- Induction preserves the anti-reality of the second function. -/
theorem actualInducedTwo_antiReal (S : Sylow 2 G)
    (P : ABG.Wreathed.Presentation S 2) (g : G) :
    star (actualInducedTwo S P g) = -actualInducedTwo S P g := by
  let a := actualInducingData S P
  change star (inducedClassFunction a.H (thetaTwo a.alpha a.beta) g) =
    -inducedClassFunction a.H (thetaTwo a.alpha a.beta) g
  have ht := ringEquiv_inducedClassFunction (starRingAut : ℂ ≃+* ℂ)
    a.H (thetaTwo a.alpha a.beta) g
  change star (inducedClassFunction a.H (thetaTwo a.alpha a.beta) g) =
    inducedClassFunction a.H (fun h => star (thetaTwo a.alpha a.beta h)) g at ht
  rw [ht]
  simp only [a.thetaTwo_antiReal]
  exact congrFun (inducedClassFunction_neg a.H (thetaTwo a.alpha a.beta)) g

/-- Every rational irreducible has zero coefficient in the second function. -/
theorem actualInducedTwo_rational_coefficient (S : Sylow 2 G)
    (P : ABG.Wreathed.Presentation S 2) {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hint : ∀ g, ∃ z : ℤ, χ g = (z : ℂ)) :
    scalarProduct G (actualInducedTwo S P) χ = 0 := by
  apply (actual_induced_gram_data S P).2.1.scalarProduct_eq_zero_of_antiReal_of_real
    (actualInducedTwo_antiReal S P) hχ
  intro g
  obtain ⟨z, hz⟩ := hint g
  simp [hz]

/-- No member of the first packet occurs in the second induced character. -/
theorem actualInducedTwo_four_coefficient (S : Sylow 2 G)
    (P : ABG.Wreathed.Presentation S 2)
    (r : FongRationalConstituents (actualInducedOne S P)
      ((FongWreathedIntrinsic.J P : S) : G)) (i : Fin 4) :
    scalarProduct G (actualInducedTwo S P) (r.four i) = 0 :=
  actualInducedTwo_rational_coefficient S P (r.four_irreducible i) (r.four_integer i)

/-- Actual nonzero constituents of the second function are disjoint from
the rational packet. The premise is a coefficient, not packet orthogonality. -/
theorem actualInducedTwo_constituent_ne_four (S : Sylow 2 G)
    (P : ABG.Wreathed.Presentation S 2)
    (r : FongRationalConstituents (actualInducedOne S P)
      ((FongWreathedIntrinsic.J P : S) : G)) {χ : ClassFunction G}
    (hχ : scalarProduct G (actualInducedTwo S P) χ ≠ 0) (i : Fin 4) :
    χ ≠ r.four i := by
  intro he
  exact hχ (he ▸ actualInducedTwo_four_coefficient S P r i)

/-- Concatenating the rational packet with four distinct actual constituents
of the second function gives eight distinct characters. -/
theorem eight_injective (S : Sylow 2 G) (P : ABG.Wreathed.Presentation S 2)
    (r : FongRationalConstituents (actualInducedOne S P)
      ((FongWreathedIntrinsic.J P : S) : G))
    (q : Fin 4 → ClassFunction G) (hq : Function.Injective q)
    (hcoeff : ∀ i, scalarProduct G (actualInducedTwo S P) (q i) ≠ 0) :
    Function.Injective (Fin.append r.four q) := by
  apply Fin.append_injective_iff.mpr
  exact ⟨r.four_injective, hq,
    fun i j => (actualInducedTwo_constituent_ne_four S P r (hcoeff j) i).symm⟩

/-- The combined family consists of genuine irreducible characters. -/
theorem eight_irreducible (S : Sylow 2 G) (P : ABG.Wreathed.Presentation S 2)
    (r : FongRationalConstituents (actualInducedOne S P)
      ((FongWreathedIntrinsic.J P : S) : G))
    (q : Fin 4 → ClassFunction G) (hq : ∀ i, IsIrreducibleCharacter (q i))
    (i : Fin 8) : IsIrreducibleCharacter (Fin.append r.four q i) := by
  refine Fin.addCases (m := 4) (n := 4) (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.append_left] using r.four_irreducible j
  · simpa only [Fin.append_right] using hq j

/-- Membership of all nonzero constituents in the given principal block
transfers to the eight actual characters, with their block indices retained. -/
theorem eight_in_block (S : Sylow 2 G) (P : ABG.Wreathed.Presentation S 2)
    (d : ModularBlock.PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (r : FongRationalConstituents (actualInducedOne S P)
      ((FongWreathedIntrinsic.J P : S) : G))
    (hblock : ∀ χ : ClassFunction G, IsIrreducibleCharacter χ →
      (scalarProduct G (actualInducedOne S P) χ ≠ 0 ∨
        scalarProduct G (actualInducedTwo S P) χ ≠ 0) →
      ∃ j ∈ d.block, ∀ g, χ g = d.chi j (ConjClasses.mk g))
    (q : Fin 4 → ClassFunction G) (hq : ∀ i, IsIrreducibleCharacter (q i))
    (hcoeff : ∀ i, scalarProduct G (actualInducedTwo S P) (q i) ≠ 0)
    (i : Fin 8) :
    ∃ j ∈ d.block, ∀ g, Fin.append r.four q i g = d.chi j (ConjClasses.mk g) := by
  apply hblock _ (eight_irreducible S P r q hq i)
  refine Fin.addCases (m := 4) (n := 4) (fun j => ?_) (fun j => ?_) i
  · left
    rw [Fin.append_left, r.four_coefficient]
    fin_cases j <;> norm_num
  · right
    simpa only [Fin.append_right] using hcoeff j

/-- The values required for the second exceptional column. -/
theorem actual_induced_at_F_cube (S : Sylow 2 G)
    (P : ABG.Wreathed.Presentation S 2) :
    actualInducedOne S P ((FongWreathedIntrinsic.F P ^ 3 : S) : G) = 4 ∧
    actualInducedTwo S P ((FongWreathedIntrinsic.F P ^ 3 : S) : G) =
      -(4 * Complex.I) := by
  have h := actual_induced_on_odd_coset S P (3 : Fin 8) (by decide) 1
  simpa [pow_succ, Complex.I_sq] using h

/-- The eight genuine exceptional characters, with the rational packet first,
and the two columns in Fong's equation (10). -/
structure EightConstituents (S : Sylow 2 G) (P : ABG.Wreathed.Presentation S 2)
    (d : ModularBlock.PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (r : FongRationalConstituents (actualInducedOne S P)
      ((FongWreathedIntrinsic.J P : S) : G)) where
  chi : Fin 8 → ClassFunction G
  irreducible : ∀ i, IsIrreducibleCharacter (chi i)
  injective : Function.Injective chi
  in_block : ∀ i, ∃ j ∈ d.block, ∀ g, chi i g = d.chi j (ConjClasses.mk g)
  first_four : chi 0 = 1 ∧ chi 1 = r.χ₂ ∧ chi 2 = r.χ₃ ∧ chi 3 = r.χ₄
  decomposition_one : actualInducedOne S P = chi 0 + chi 1 - chi 2 - chi 3
  decomposition_two : actualInducedTwo S P = chi 4 - chi 5 + chi 6 - chi 7
  second_coefficients : ∀ i : Fin 4,
    scalarProduct G (actualInducedTwo S P) (chi (i.natAdd 4)) =
      (![1, -1, 1, -1] : Fin 4 → ℂ) i
  conjugate_pairs : chi 5 = (fun g => star (chi 4 g)) ∧
    chi 7 = (fun g => star (chi 6 g))
  F_values : ∀ i, chi i ((FongWreathedIntrinsic.F P : S) : G) =
    (![1, 1, -1, -1, Complex.I, -Complex.I, Complex.I, -Complex.I] : Fin 8 → ℂ) i
  F_cube_values : ∀ i, chi i ((FongWreathedIntrinsic.F P ^ 3 : S) : G) =
    (![1, 1, -1, -1, -Complex.I, Complex.I, -Complex.I, Complex.I] : Fin 8 → ℂ) i

/-- Extract the second packet using anti-reality and norm four, prove its
disjointness from the rational packet, and saturate both block columns. -/
theorem actual_eight_constituents (S : Sylow 2 G)
    (P : ABG.Wreathed.Presentation S 2)
    (d : ModularBlock.PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (hc : FongWreathedIntrinsic.LocalPrincipalColumnNormData S P d)
    (r : FongRationalConstituents (actualInducedOne S P)
      ((FongWreathedIntrinsic.J P : S) : G))
    (hblock : ∀ χ : ClassFunction G, IsIrreducibleCharacter χ →
      (scalarProduct G (actualInducedOne S P) χ ≠ 0 ∨
        scalarProduct G (actualInducedTwo S P) χ ≠ 0) →
      ∃ j ∈ d.block, ∀ g, χ g = d.chi j (ConjClasses.mk g)) :
    Nonempty (EightConstituents S P d r) := by
  obtain ⟨q, hq, hqi, hdec, hcoeff, hconj₁, hconj₂⟩ :=
    (actual_induced_gram_data S P).2.1.exists_four_irreducibles_of_antiReal_norm_four
      (actual_induced_gram_data S P).2.2.2.1 (actualInducedTwo_antiReal S P)
  have hnz (i : Fin 4) : scalarProduct G (actualInducedTwo S P) (q i) ≠ 0 := by
    rw [hcoeff]
    fin_cases i <;> norm_num
  let χ : Fin 8 → ClassFunction G := Fin.append r.four q
  have hinj : Function.Injective χ := eight_injective S P r q hqi hnz
  have hmem : ∀ i, ∃ j ∈ d.block, ∀ g, χ i g = d.chi j (ConjClasses.mk g) :=
    eight_in_block S P d r hblock q hq hnz
  have hfirst : actualInducedOne S P = χ 0 + χ 1 - χ 2 - χ 3 := r.decomposition
  have hsecond : actualInducedTwo S P = χ 4 - χ 5 + χ 6 - χ 7 := hdec
  have hF : ∀ i, χ i ((FongWreathedIntrinsic.F P : S) : G) =
      (![1, 1, -1, -1, Complex.I, -Complex.I, Complex.I, -Complex.I] : Fin 8 → ℂ) i := by
    apply d.eight_values_eq_of_column_sum χ hinj hmem _ Complex.I
      (by norm_num) hc.F_column
    · simpa only [hfirst, Pi.sub_apply, Pi.add_apply] using (actual_induced_at_F S P).1
    · simpa only [hsecond, Pi.sub_apply, Pi.add_apply] using (actual_induced_at_F S P).2
  have hF3 : ∀ i, χ i ((FongWreathedIntrinsic.F P ^ 3 : S) : G) =
      (![1, 1, -1, -1, -Complex.I, Complex.I, -Complex.I, Complex.I] : Fin 8 → ℂ) i := by
    have he := d.eight_values_eq_of_column_sum χ hinj hmem
      ((FongWreathedIntrinsic.F P ^ 3 : S) : G) (-Complex.I)
      (by norm_num) hc.F_cube_column
      (by simpa only [hfirst, Pi.sub_apply, Pi.add_apply] using (actual_induced_at_F_cube S P).1)
      (by simpa only [hsecond, Pi.sub_apply, Pi.add_apply, mul_neg] using
        (actual_induced_at_F_cube S P).2)
    simpa only [neg_neg] using he
  exact ⟨{
    chi := χ
    irreducible := eight_irreducible S P r q hq
    injective := hinj
    in_block := hmem
    first_four := ⟨rfl, rfl, rfl, rfl⟩
    decomposition_one := hfirst
    decomposition_two := hsecond
    second_coefficients := fun i => by simpa only [χ, Fin.append_right] using hcoeff i
    conjugate_pairs := ⟨hconj₁, hconj₂⟩
    F_values := hF
    F_cube_values := hF3 }⟩

end FongWreathedInduction
end Stellmacher.Recognition
