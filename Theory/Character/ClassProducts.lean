module

public import Theory.Character.Divisibility
public import Theory.Character.SimpleCriteria

/-!
# Normalized character values on products of conjugacy classes

When an irreducible complex character is constant on all products of an
element from each of two conjugacy classes, its values divided by its
degree multiply like those of a linear character.

The class-sum multiplication coefficient counts factorizations of a chosen
representative. Simultaneous conjugation proves independence of that choice.
The trivial character gives the weighted sum of those coefficients; the
irreducible class-sum scalar formula gives the same identity with character
ratios. Constancy lets the character value factor out of the sum, and
cancelling the nonzero class sizes proves the normalized identity.

These are the ordinary-character calculations in step (VI) of Glauberman's
Z-star argument, ported from historical
`Submission/ZStar/CharacterArgument.lean` at commit `c3503435`.
The statements require no modular-block assumptions.
-/

public section
noncomputable section
open scoped BigOperators
namespace CharacterClassProducts
universe u v
attribute [local instance] Fintype.ofFinite

private def conjugateCarrierEquiv
    {G : Type u} [Group G] (C : ConjClasses G) (c : G) :
    C.carrier ≃ C.carrier where
  toFun x := ⟨c * x.1 * c⁻¹, by
    apply ConjClasses.mem_carrier_iff_mk_eq.mpr
    exact ((ConjClasses.mk_eq_mk_iff_isConj.mpr
      (isConj_iff.mpr ⟨c, rfl⟩)).symm).trans
        (ConjClasses.mem_carrier_iff_mk_eq.mp x.2)⟩
  invFun x := ⟨c⁻¹ * x.1 * (c⁻¹)⁻¹, by
    apply ConjClasses.mem_carrier_iff_mk_eq.mpr
    exact ((ConjClasses.mk_eq_mk_iff_isConj.mpr
      (isConj_iff.mpr ⟨c⁻¹, rfl⟩)).symm).trans
        (ConjClasses.mem_carrier_iff_mk_eq.mp x.2)⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]

private theorem pairCount_eq_of_isConj
    {G : Type u} [Group G] [Finite G]
    (Ci Cj : ConjClasses G) {x y : G} (hxy : IsConj x y) :
    Nat.card {p : Ci.carrier × Cj.carrier // p.1.1 * p.2.1 = x} =
      Nat.card {p : Ci.carrier × Cj.carrier // p.1.1 * p.2.1 = y} := by
  rcases isConj_iff.mp hxy with ⟨c, hc⟩
  let ei := conjugateCarrierEquiv Ci c
  let ej := conjugateCarrierEquiv Cj c
  apply Nat.card_congr
  exact {
    toFun := fun p => ⟨(ei p.1.1, ej p.1.2), by
      dsimp [ei, ej, conjugateCarrierEquiv]
      have hprod :
          c * p.1.1.1 * c⁻¹ * (c * p.1.2.1 * c⁻¹) = c * x * c⁻¹ := by
        simpa [mul_assoc] using congrArg (fun z : G => c * z * c⁻¹) p.2
      exact hprod.trans hc⟩
    invFun := fun p => ⟨(ei.symm p.1.1, ej.symm p.1.2), by
      dsimp [ei, ej, conjugateCarrierEquiv]
      simpa [mul_assoc] using
        congrArg (fun z : G => c⁻¹ * z * (c⁻¹)⁻¹) (p.2.trans hc.symm)⟩
    left_inv := by
      intro p
      apply Subtype.ext
      apply Prod.ext <;> simp [ei, ej]
    right_inv := by
      intro p
      apply Subtype.ext
      apply Prod.ext <;> simp [ei, ej] }

/-- The coefficient of the class `Ck` in the product of the class sums of
`Ci` and `Cj`.  It is the number of factorizations of one (hence every)
element of `Ck` as a product of an element of `Ci` and an element of `Cj`. -/
@[expose] def classProductCoeff
    {G : Type u} [Group G] [Finite G]
    (Ci Cj Ck : ConjClasses G) : ℕ :=
  Nat.card {p : Ci.carrier × Cj.carrier //
    p.1.1 * p.2.1 = Quotient.out Ck}

/-- `classProductCoeff` is independent of the representative chosen in its
output conjugacy class. -/
theorem classProductCoeff_spec
    {G : Type u} [Group G] [Finite G]
    (Ci Cj Ck : ConjClasses G) (x : G) (hx : x ∈ Ck.carrier) :
    classProductCoeff Ci Cj Ck =
      Nat.card {p : Ci.carrier × Cj.carrier // p.1.1 * p.2.1 = x} := by
  apply pairCount_eq_of_isConj
  apply ConjClasses.mk_eq_mk_iff_isConj.mp
  exact (Quotient.out_eq Ck).trans
    (ConjClasses.mem_carrier_iff_mk_eq.mp hx).symm

/-- Counting all pairs in two conjugacy classes by the conjugacy class of
their product gives the weighted class-multiplication identity. -/
theorem classProductCoeff_weighted_sum
    {G : Type u} [Group G] [Finite G]
    (Ci Cj : ConjClasses G) :
    (Nat.card Ci.carrier : ℂ) * (Nat.card Cj.carrier : ℂ) =
      (@Finset.univ (ConjClasses G) (Fintype.ofFinite (ConjClasses G))).sum
        (fun Ck =>
          (classProductCoeff Ci Cj Ck : ℂ) * (Nat.card Ck.carrier : ℂ)) := by
  classical
  let rho0 : Representation ℂ G ℂ := Representation.trivial ℂ G ℂ
  let : Representation.IsIrreducible rho0 :=
    trivial_complex_irreducible
  have hmul := classSumScalar_mul_eq_sum_of_coefficients
    (ρ := rho0) (a := classProductCoeff)
    (hdata := fun i j s x hx => classProductCoeff_spec i j s x hx) Ci Cj
  have hscalar (C : ConjClasses G) :
      classSumScalar (ρ := rho0) C =
        (Nat.card C.carrier : ℂ) := by
    rw [classSumScalar_eq_card_mul_character_div
      (ρ := rho0) C
      (ConjClasses.mem_carrier_iff_mk_eq.mpr (Quotient.out_eq C))]
    simp [rho0, Representation.character]
  simpa [hscalar] using hmul

/-- If an irreducible character is constant on every product of a conjugate
of `u` with a conjugate of `v`, then its normalized values multiply:

`(chi(u) / chi(1)) (chi(v) / chi(1)) = chi(uv) / chi(1)`.

This is the class-sum calculation in Step (VI) of Glauberman's proof. -/
theorem characterRatio_mul_eq_of_classProducts_constant
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) [Representation.IsIrreducible rho]
    (u v : G)
    (hconstant : ∀ x : G, x ∈ (ConjClasses.mk u).carrier →
      ∀ y : G, y ∈ (ConjClasses.mk v).carrier →
        rho.character (x * y) = rho.character (u * v)) :
    (rho.character u / rho.character 1) *
        (rho.character v / rho.character 1) =
      rho.character (u * v) / rho.character 1 := by
  classical
  let Ci : ConjClasses G := ConjClasses.mk u
  let Cj : ConjClasses G := ConjClasses.mk v
  have hsupport (Ck : ConjClasses G)
      (hk : classProductCoeff Ci Cj Ck ≠ 0) :
      rho.character (Quotient.out Ck) = rho.character (u * v) := by
    have hne : Nonempty
        {p : Ci.carrier × Cj.carrier //
          p.1.1 * p.2.1 = Quotient.out Ck} :=
      (Nat.card_ne_zero.mp hk).1
    let p := Classical.choice hne
    have hp := hconstant p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2
    simpa [p.2] using hp
  have hmul := classSumScalar_mul_eq_sum_of_coefficients
    (ρ := rho) (a := classProductCoeff)
    (hdata := fun i j s x hx => classProductCoeff_spec i j s x hx) Ci Cj
  have hCi :
      classSumScalar (ρ := rho) Ci =
        (Nat.card Ci.carrier : ℂ) * rho.character u / rho.character 1 := by
    exact classSumScalar_eq_card_mul_character_div
      (ρ := rho) Ci ConjClasses.mem_carrier_mk
  have hCj :
      classSumScalar (ρ := rho) Cj =
        (Nat.card Cj.carrier : ℂ) * rho.character v / rho.character 1 := by
    exact classSumScalar_eq_card_mul_character_div
      (ρ := rho) Cj ConjClasses.mem_carrier_mk
  have hrhs :
      (@Finset.univ (ConjClasses G) (Fintype.ofFinite (ConjClasses G))).sum
          (fun Ck => (classProductCoeff Ci Cj Ck : ℂ) *
            classSumScalar (ρ := rho) Ck) =
        (rho.character (u * v) / rho.character 1) *
          (@Finset.univ (ConjClasses G) (Fintype.ofFinite (ConjClasses G))).sum
            (fun Ck => (classProductCoeff Ci Cj Ck : ℂ) *
              (Nat.card Ck.carrier : ℂ)) := by
    calc
      (@Finset.univ (ConjClasses G) (Fintype.ofFinite (ConjClasses G))).sum
          (fun Ck => (classProductCoeff Ci Cj Ck : ℂ) *
            classSumScalar (ρ := rho) Ck) =
          (@Finset.univ (ConjClasses G) (Fintype.ofFinite (ConjClasses G))).sum
            (fun Ck => (rho.character (u * v) / rho.character 1) *
              ((classProductCoeff Ci Cj Ck : ℂ) *
                (Nat.card Ck.carrier : ℂ))) := by
            refine Finset.sum_congr rfl ?_
            intro Ck _
            by_cases hk : classProductCoeff Ci Cj Ck = 0
            · simp [hk]
            · rw [classSumScalar_eq_card_mul_character_div
                (ρ := rho) Ck
                (ConjClasses.mem_carrier_iff_mk_eq.mpr (Quotient.out_eq Ck)),
                hsupport Ck hk]
              ring
      _ = (rho.character (u * v) / rho.character 1) *
          (@Finset.univ (ConjClasses G) (Fintype.ofFinite (ConjClasses G))).sum
            (fun Ck => (classProductCoeff Ci Cj Ck : ℂ) *
              (Nat.card Ck.carrier : ℂ)) := by
            rw [Finset.mul_sum]
  rw [hCi, hCj] at hmul
  have hmul' := hmul.trans hrhs
  rw [← classProductCoeff_weighted_sum Ci Cj] at hmul'
  let : Nonempty Ci.carrier :=
    ⟨⟨u, by simpa [Ci] using (ConjClasses.mem_carrier_mk (a := u))⟩⟩
  let : Nonempty Cj.carrier :=
    ⟨⟨v, by simpa [Cj] using (ConjClasses.mem_carrier_mk (a := v))⟩⟩
  have hCi_ne : (Nat.card Ci.carrier : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Ci.carrier)).ne'
  have hCj_ne : (Nat.card Cj.carrier : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Cj.carrier)).ne'
  apply mul_left_cancel₀ (mul_ne_zero hCi_ne hCj_ne)
  calc
    ((Nat.card Ci.carrier : ℂ) * (Nat.card Cj.carrier : ℂ)) *
          ((rho.character u / rho.character 1) *
            (rho.character v / rho.character 1)) =
        ((Nat.card Ci.carrier : ℂ) * rho.character u / rho.character 1) *
          ((Nat.card Cj.carrier : ℂ) * rho.character v / rho.character 1) := by
            ring
    _ = (rho.character (u * v) / rho.character 1) *
          ((Nat.card Ci.carrier : ℂ) * (Nat.card Cj.carrier : ℂ)) := hmul'
    _ = ((Nat.card Ci.carrier : ℂ) * (Nat.card Cj.carrier : ℂ)) *
          (rho.character (u * v) / rho.character 1) := by ring

/-- Class-function wrapper for `characterRatio_mul_eq_of_classProducts_constant`. -/
theorem irreducibleCharacterRatio_mul_eq_of_classProducts_constant
    {G : Type u} [Group G] [Finite G]
    (chi : ConjClassFunction G)
    (hchi : IsIrreducibleConjCharacter chi)
    (u v : G)
    (hconstant : ∀ x : G, x ∈ (ConjClasses.mk u).carrier →
      ∀ y : G, y ∈ (ConjClasses.mk v).carrier →
        chi (ConjClasses.mk (x * y)) = chi (ConjClasses.mk (u * v))) :
    (chi (ConjClasses.mk u) / chi (ConjClasses.mk (1 : G))) *
        (chi (ConjClasses.mk v) / chi (ConjClasses.mk (1 : G))) =
      chi (ConjClasses.mk (u * v)) / chi (ConjClasses.mk (1 : G)) := by
  rcases hchi.1 with ⟨n, rho, rfl⟩
  have hirr : Representation.IsIrreducible rho :=
    (irreducible_iff_character_norm_one (ρ := rho)).2 hchi.2
  let : Representation.IsIrreducible rho := hirr
  refine characterRatio_mul_eq_of_classProducts_constant rho u v ?_
  intro x hx y hy
  exact hconstant x hx y hy


end CharacterClassProducts

