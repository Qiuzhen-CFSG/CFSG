module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Spinor.Character
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.Scalars
/-!
# Reflection characters on the literal minus coordinates

Identity extension through `fullBlockHom` preserves every reflection-value
character: the embedded vector is `splitCoordinates.symm (0, a)`, its quadratic
value is unchanged, and reflection generation determines the character.

For negation, each hyperbolic coordinate plane is negated by reflections in
`e + f` and `e - f`, of values `1` and `-1`. The final anisotropic plane is
negated by reflections in `(1, 0)` and `(-1, 2)`, of values `1` and
`-(1 + 4 * parameter F)`. Multiplying these literal coordinate actions gives
negation on the entire carrier, with character value the class of
`(-1)^(r + 1) * (1 + 4 * parameter F)`. Discriminant nonvanishing follows from
`parameter_discriminant_nonsquare`, without repeating its square-class arithmetic.

The results take reflection characters as explicit inputs. They discharge the
computational premises of `Spinor.lean`; construction of the characters and the
unconditional commutator applications belong to its assembly. The calculations
work for every rank, hence include rank one and the field of three elements.

Sources: GLS3 §2.7, printed pp.87–89; Aschbacher–Smith A.2.17, printed p.39.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Theory.AlgebraicGroup
open ClassicalOrthogonal.Quadratic ClassicalOrthogonal.ReflectionGeneration
open ClassicalOrthogonal.SpinorInvariants
namespace ClassicalOrthogonal.Fundamental.MinusCentralizer.CoordinateValues
variable {F : Type*} [Field F] [Finite F]

/-- The actual embedding of the complement, with zero marked four-space coordinate. -/
def complementVector (r : ℕ) (a : Minus.Space F r) : Minus.Space F (r + 2) :=
  (splitCoordinates r).symm (0, a)

/-- Identity extension preserves the quadratic value of the reflecting vector. -/
theorem complementVector_value (r : ℕ) (a : Minus.Space F r) :
    Minus.quadraticForm F (r + 3) (complementVector r a) =
      Minus.quadraticForm F (r + 1) a := by
  change Minus.form F (r + 2) _ _ = Minus.form F r _ _
  rw [splitCoordinates_form]
  simp [complementVector]

/-- The embedded vector pairs only with the complementary coordinate. -/
theorem complementVector_polar (r : ℕ) (x : Minus.Space F (r + 2)) (a : Minus.Space F r) :
    (Minus.quadraticForm F (r + 3)).polarBilin x (complementVector r a) =
      (Minus.quadraticForm F (r + 1)).polarBilin (splitCoordinates r x).2 a := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  change Minus.form F (r + 2) (Minus.parameter F) (x + complementVector r a) -
    Minus.form F (r + 2) (Minus.parameter F) x -
    Minus.form F (r + 2) (Minus.parameter F) (complementVector r a) =
    Minus.form F r (Minus.parameter F) ((splitCoordinates r x).2 + a) -
    Minus.form F r (Minus.parameter F) (splitCoordinates r x).2 -
    Minus.form F r (Minus.parameter F) a
  rw [splitCoordinates_form, splitCoordinates_form, splitCoordinates_form]
  simp only [map_add, complementVector, LinearEquiv.apply_symm_apply, Prod.fst_add,
    Prod.snd_add, add_zero, map_zero]
  ring

/-- The literal identity block extension sends a reflection to the embedded reflection. -/
theorem fullBlockHom_reflection (r : ℕ) (a : Minus.Space F r)
    (ha : Minus.quadraticForm F (r + 1) a ≠ 0) :
    fullBlockHom r (1, reflectionElement _ a ha) =
      reflectionElement _ (complementVector r a) ((complementVector_value r a) ▸ ha) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply (splitCoordinates r).injective
  have hb : fullBlockHom r (1, reflectionElement _ a ha) =
      blockHom r (Minus.parameter F) (1, reflectionElement _ a ha) := by
    change blockHom r (Minus.parameter F)
      ((((elementarySubgroup (formD 2 F)).subtype.comp fourRight) 1), _) = _
    rw [map_one]
    rfl
  rw [hb, blockHom_coordinates]
  change ((splitCoordinates r x).1,
    reflectionLinear (Minus.quadraticForm F (r + 1)) a ha (splitCoordinates r x).2) =
    splitCoordinates r (reflectionLinear (Minus.quadraticForm F (r + 3))
      (complementVector r a) ((complementVector_value r a) ▸ ha) x)
  rw [reflectionLinear_apply, reflectionLinear_apply, complementVector_value,
    complementVector_polar, map_sub, map_smul]
  apply Prod.ext <;> simp [complementVector]

/-- The identity block extension preserves any two prescribed reflection characters. -/
theorem fullBlockHom_character (r : ℕ) (h2 : (2 : F) ≠ 0)
    (χ : ReflectionCharacter (Minus.quadraticForm F (r + 1)))
    (ψ : ReflectionCharacter (Minus.quadraticForm F (r + 3)))
    (u : Minus.Orthogonal F (Minus.Space F r) (Minus.quadraticForm F (r + 1))) :
    ψ.hom (fullBlockHom r (1, u)) = χ.hom u := by
  have he : ψ.hom.comp ((fullBlockHom r).comp (MonoidHom.inr _ _)) = χ.hom := by
    apply MonoidHom.eq_of_eqOn_dense (reflectionSubgroup_eq_top _
      (Minus.quadraticForm_nonsingular F (r + 1)) h2)
    rintro g ⟨a, ha, rfl⟩
    change ψ.hom (fullBlockHom r (1, reflectionElement _ a ha)) = _
    rw [fullBlockHom_reflection, ψ.reflection_value, χ.reflection_value]
    congr 1
    apply Units.ext
    exact complementVector_value r a
  exact DFunLike.congr_fun he u

open ClassicalOrthogonal.Minus

/-- Negate precisely the hyperbolic coordinate planes indexed by `s`. -/
def hyperNegation (r : ℕ) (s : Finset (Fin r)) : Orthogonal F (Space F r) (quadraticForm F (r + 1)) := by
  classical
  refine ⟨(LinearEquiv.piCongrRight (fun i : Fin r =>
    if i ∈ s then LinearEquiv.neg F else LinearEquiv.refl F (F × F))).prodCongr
      (LinearEquiv.refl F (F × F)), (mem_quadraticIsometrySubgroup _ _).mpr ?_⟩
  intro x
  change form F r _ _ = form F r _ _
  simp only [form_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ s <;> simp [hi]

@[simp] theorem hyperNegation_apply (r : ℕ) (s : Finset (Fin r)) (x : Space F r) :
    (hyperNegation r s).val x = ((fun i => if i ∈ s then -(x.1 i) else x.1 i), x.2) := by
  classical
  apply Prod.ext
  · funext i
    by_cases hi : i ∈ s <;> simp [hyperNegation, hi]
  · rfl

theorem hyperNegation_empty (r : ℕ) : hyperNegation (F := F) r ∅ = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  simp

theorem hyperNegation_insert (r : ℕ) (s : Finset (Fin r)) (i : Fin r) (hi : i ∉ s) :
    hyperNegation (F := F) r (insert i s) = hyperNegation r {i} * hyperNegation r s := by
  classical
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (hyperNegation r (insert i s)).val x =
    (hyperNegation r {i}).val ((hyperNegation r s).val x)
  simp only [hyperNegation_apply]
  apply Prod.ext
  · funext j
    by_cases hji : j = i
    · subst j; simp [hi]
    · simp [hji]
  · rfl

/-- The vector `eᵢ + c fᵢ` in the actual hyperbolic coordinates. -/
def hyperVector (r : ℕ) (i : Fin r) (c : F) : Space F r :=
  (fun j => if j = i then (1,c) else 0, 0)

@[simp] theorem hyperVector_value (r : ℕ) (i : Fin r) (c : F) :
    quadraticForm F (r + 1) (hyperVector r i c) = c := by
  classical
  simp [quadraticForm, hyperVector, apply_ite]

theorem hyperVector_polar (r : ℕ) (i : Fin r) (c : F) (x : Space F r) :
    (quadraticForm F (r + 1)).polarBilin x (hyperVector r i c) =
      (x.1 i).1 * c + (x.1 i).2 := by
  classical
  change (form F r _).polarBilin _ _ = _
  rw [form_polar, plane_polar]
  rw [Finset.sum_eq_single i]
  · simp [hyperVector]
  · intro j _ hji
    simp [hyperVector, hji]
  · simp

/-- Two orthogonal reflections negate one hyperbolic plane and fix every other coordinate. -/
theorem hyperNegation_reflections (r : ℕ) (i : Fin r) :
    hyperNegation (F := F) r {i} =
      reflectionElement (quadraticForm F (r + 1)) (hyperVector r i 1) (by rw [hyperVector_value (F := F) r i 1]; exact one_ne_zero) *
      reflectionElement (quadraticForm F (r + 1)) (hyperVector r i (-1)) (by rw [hyperVector_value (F := F) r i (-1)]; exact neg_ne_zero.mpr one_ne_zero) := by
  classical
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (hyperNegation r {i}).val x =
    reflectionLinear (quadraticForm F (r + 1)) (hyperVector r i 1)
      (by rw [hyperVector_value (F := F) r i 1]; exact one_ne_zero)
      (reflectionLinear (quadraticForm F (r + 1)) (hyperVector r i (-1))
        (by rw [hyperVector_value (F := F) r i (-1)]; exact neg_ne_zero.mpr one_ne_zero) x)
  simp only [hyperNegation_apply, reflectionLinear_apply, hyperVector_value,
    hyperVector_polar, inv_one, inv_neg, one_mul]
  apply Prod.ext
  · funext j
    by_cases hji : j = i
    · subst j
      apply Prod.ext <;> simp [hyperVector]
    · simp [hyperVector, hji]
  · simp [hyperVector]

/-- Negation of just the final anisotropic plane. -/
def planeNegation (r : ℕ) : Orthogonal F (Space F r) (quadraticForm F (r + 1)) :=
  ⟨(LinearEquiv.refl F _).prodCongr (LinearEquiv.neg F),
    (mem_quadraticIsometrySubgroup _ _).mpr (by
      intro x
      change form F r _ (x.1, -x.2) = form F r _ x
      simp only [form_apply, QuadraticMap.map_neg])⟩

/-- A vector supported on the final anisotropic plane. -/
def planeVector (r : ℕ) (a b : F) : Space F r := (0, (a,b))

@[simp] theorem planeVector_value (r : ℕ) (a b : F) :
    quadraticForm F (r + 1) (planeVector r a b) = a ^ 2 + a * b - parameter F * b ^ 2 := by
  simp [planeVector, quadraticForm]

theorem planeVector_polar (r : ℕ) (a b : F) (x : Space F r) :
    (quadraticForm F (r + 1)).polarBilin x (planeVector r a b) =
      2 * x.2.1 * a + x.2.1 * b + x.2.2 * a - 2 * parameter F * x.2.2 * b := by
  change (form F r _).polarBilin _ _ = _
  rw [form_polar, plane_polar]
  simp [planeVector]

/-- The anisotropic-plane discriminant cannot vanish in odd characteristic. -/
theorem discriminant_ne_zero (h2 : (2 : F) ≠ 0) : 1 + 4 * parameter F ≠ 0 := by
  intro h
  exact parameter_discriminant_nonsquare h2 (h ▸ IsSquare.zero)

theorem planeVector_last_ne_zero (r : ℕ) (h2 : (2 : F) ≠ 0) :
    quadraticForm F (r + 1) (planeVector r (-1) 2) ≠ 0 := by
  rw [planeVector_value]
  convert neg_ne_zero.mpr (discriminant_ne_zero h2) using 1
  ring

/-- The explicit orthogonal pair `(1,0), (-1,2)` factors final-plane negation. -/
theorem planeNegation_reflections (r : ℕ) (h2 : (2 : F) ≠ 0) :
    planeNegation (F := F) r =
      reflectionElement (quadraticForm F (r + 1)) (planeVector r 1 0) (by rw [planeVector_value (F := F) r 1 0]; simp) *
      reflectionElement (quadraticForm F (r + 1)) (planeVector r (-1) 2) (planeVector_last_ne_zero r h2) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (x.1, -x.2) =
    reflectionLinear (quadraticForm F (r + 1)) (planeVector r 1 0)
      (by rw [planeVector_value (F := F) r 1 0]; simp)
      (reflectionLinear (quadraticForm F (r + 1)) (planeVector r (-1) 2)
        (planeVector_last_ne_zero r h2) x)
  have hv : quadraticForm F (r + 1) (planeVector r (-1) 2) = -(1 + 4 * parameter F) := by
    rw [planeVector_value]
    ring
  have hv1 : quadraticForm F (r + 1) (planeVector r 1 0) = 1 := by
    simpa using planeVector_value (F := F) r 1 0
  have hd := discriminant_ne_zero (F := F) h2
  have hr2 : reflectionLinear (quadraticForm F (r + 1)) (planeVector r (-1) 2)
      (planeVector_last_ne_zero r h2) x = (x.1, (x.2.1 + x.2.2, -x.2.2)) := by
    rw [reflectionLinear_apply, hv, planeVector_polar]
    have hp : 2 * x.2.1 * (-1) + x.2.1 * 2 + x.2.2 * (-1) - 2 * parameter F * x.2.2 * 2 =
        -(1 + 4 * parameter F) * x.2.2 := by ring
    rw [hp, ← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr hd), one_mul]
    apply Prod.ext
    · simp [planeVector]
    · apply Prod.ext <;> simp [planeVector]
      ring
  rw [hr2, reflectionLinear_apply, hv1, planeVector_polar]
  apply Prod.ext
  · simp [planeVector]
  · apply Prod.ext <;> simp [planeVector]
    ring

/-- Each negated hyperbolic plane contributes the square class of `-1`. -/
theorem hyperNegation_character (r : ℕ)
    (χ : ReflectionCharacter (quadraticForm F (r + 1))) (s : Finset (Fin r)) :
    χ.hom (hyperNegation r s) = Atlas.squareClass F (-1) ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hyperNegation_empty]
  | @insert i s hi ih =>
    rw [hyperNegation_insert r s i hi, map_mul, ih, hyperNegation_reflections,
      map_mul, χ.reflection_value, χ.reflection_value]
    have hp : Units.mk0 (quadraticForm F (r + 1) (hyperVector r i 1)) (by rw [hyperVector_value (F := F) r i 1]; exact one_ne_zero) = 1 :=
      Units.ext (hyperVector_value r i 1)
    have hn : Units.mk0 (quadraticForm F (r + 1) (hyperVector r i (-1))) (by rw [hyperVector_value (F := F) r i (-1)]; exact neg_ne_zero.mpr one_ne_zero) = -1 :=
      Units.ext (hyperVector_value r i (-1))
    rw [hp, hn, map_one, one_mul, Finset.card_insert_of_notMem hi, pow_succ']

/-- The coordinate negations multiply to the published full complementary negation. -/
theorem negativeComplement_factorization (r : ℕ) :
    negativeComplement (F := F) r = hyperNegation r Finset.univ * planeNegation r := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change -x = (hyperNegation r Finset.univ).val (x.1, -x.2)
  simp only [hyperNegation_apply, Finset.mem_univ, ite_true]
  rfl

/-- Nonvanishing of the scalar representing the full negation character. -/
theorem minus_discriminant_ne_zero (r : ℕ) (h2 : (2 : F) ≠ 0) :
    (-1 : F) ^ (r + 1) * (1 + 4 * parameter F) ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (discriminant_ne_zero h2)

/-- The concrete reflection-character value of the literal complementary negation. -/
theorem negativeComplement_character (r : ℕ) (h2 : (2 : F) ≠ 0)
    (χ : ReflectionCharacter (quadraticForm F (r + 1))) :
    χ.hom (negativeComplement r) = Atlas.squareClass F
      (Units.mk0 ((-1 : F) ^ (r + 1) * (1 + 4 * parameter F)) (minus_discriminant_ne_zero r h2)) := by
  rw [negativeComplement_factorization, map_mul, hyperNegation_character,
    planeNegation_reflections r h2, map_mul, χ.reflection_value, χ.reflection_value]
  have hp : Units.mk0 (quadraticForm F (r + 1) (planeVector r 1 0)) (by rw [planeVector_value (F := F) r 1 0]; simp) = 1 := by
    apply Units.ext
    change quadraticForm F (r + 1) (planeVector r 1 0) = 1
    simpa using planeVector_value (F := F) r 1 0
  rw [hp, map_one, one_mul, ← map_pow, ← map_mul]
  congr 1
  apply Units.ext
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    Units.val_mk0, planeVector_value, Finset.card_univ, Fintype.card_fin]
  ring

/-- Negation has trivial character exactly when its computed discriminant is square. -/
theorem negativeComplement_character_eq_one_iff (r : ℕ) (h2 : (2 : F) ≠ 0)
    (χ : ReflectionCharacter (quadraticForm F (r + 1))) :
    χ.hom (negativeComplement r) = 1 ↔
      IsSquare ((-1 : F) ^ (r + 1) * (1 + 4 * parameter F)) := by
  rw [negativeComplement_character r h2 χ, Atlas.squareClass_mk0_eq_one]

end ClassicalOrthogonal.Fundamental.MinusCentralizer.CoordinateValues
