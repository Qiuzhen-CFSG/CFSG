module
public import Theory.Representation.BinaryTensorThree.Group

/-!
# The two line-parabolic radicals on the binary tensor square

Each radical sends the two quotient basis vectors into the fixed first line.
On the tensor square, the two radicals fix the marked pure tensor. Every
nontrivial subgroup of their product therefore has a pure tensor whose
translation coefficient is a nonzero binary character. The kernel is the
hyperplane used in the source weak-closure argument.

The representation is the existing literal tensor action, with both factor
markings retained. The group-action companion transports this calculation to
an elementary abelian subgroup of an arbitrary ambient group.
Source: Aschbacher--Smith, H.4.4 and the proof of 8.3.14,
printed pp.383--385,727 (refs/quasithin.pdf).
-/

@[expose] public section

open scoped TensorProduct
namespace BinaryTensorThree

/-- Coordinates on the radical fixing the first line and its quotient. -/
abbrev Radical := Multiplicative (Fin 2 → ZMod 2)

/-- A line-parabolic transvection in the original natural three-space. -/
noncomputable def radicalEquiv (a : Fin 2 → ZMod 2) : Factor where
  toFun x := ![x 0 + a 0 * x 1 + a 1 * x 2, x 1, x 2]
  invFun x := ![x 0 + a 0 * x 1 + a 1 * x 2, x 1, x 2]
  left_inv x := by
    ext i
    fin_cases i <;> simp
    ring_nf
    simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, add_zero]
  right_inv x := by
    ext i
    fin_cases i <;> simp
    ring_nf
    simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, add_zero]
  map_add' x y := by
    ext i
    fin_cases i <;> simp
    ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp
    ring

/-- The additive two-space as the actual line-parabolic radical. -/
noncomputable def radical : Radical →* Factor where
  toFun a := radicalEquiv a.toAdd
  map_one' := by ext x i; fin_cases i <;> simp [radicalEquiv]
  map_mul' a b := by
    ext x i
    change radicalEquiv (a.toAdd + b.toAdd) x i = radicalEquiv a.toAdd (radicalEquiv b.toAdd x) i
    fin_cases i <;> simp [radicalEquiv]
    ring

/-- Both marked radicals inside the genuine tensor action group. -/
noncomputable def radicalPair : Radical × Radical →* Group :=
  baseEmbedding.comp (radical.prodMap radical)

def basisVector (i : Fin 3) : Natural := Pi.single i 1

/-- The source point on the tensor product of the two fixed lines. -/
noncomputable def point : Space := coordinates (basisVector 0 ⊗ₜ[ZMod 2] basisVector 0)
noncomputable def leftProbe (j : Fin 2) : Space :=
  coordinates (basisVector j.succ ⊗ₜ[ZMod 2] basisVector 0)
noncomputable def rightProbe (j : Fin 2) : Space :=
  coordinates (basisVector 0 ⊗ₜ[ZMod 2] basisVector j.succ)

def radicalCoordinate (j : Fin 2) : Radical →* Multiplicative (ZMod 2) where
  toFun a := Multiplicative.ofAdd (a.toAdd j)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem radical_basis_zero (a : Radical) : radical a (basisVector 0) = basisVector 0 := by
  ext i
  fin_cases i <;> simp [radical, radicalEquiv, basisVector]

theorem radical_basis_succ (a : Radical) (j : Fin 2) :
    radical a (basisVector j.succ) = basisVector j.succ + a.toAdd j • basisVector 0 := by
  ext i
  fin_cases i <;> fin_cases j <;> simp [radical, radicalEquiv, basisVector]

theorem point_ne_zero : point ≠ 0 := by
  intro h
  have hh := congrArg (fun X : Space => X 0 0) h
  simp [point, coordinates_tmul, basisVector] at hh

theorem radicalPair_leftProbe (a : Radical × Radical) (j : Fin 2) :
    action (radicalPair a) (leftProbe j) = leftProbe j + a.1.toAdd j • point := by
  change baseAction (radical a.1, radical a.2)
    (coordinates (basisVector j.succ ⊗ₜ[ZMod 2] basisVector 0)) = _
  rw [baseAction_tmul, radical_basis_succ, radical_basis_zero,
    TensorProduct.add_tmul, TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_add, map_smul]
  rfl

theorem radicalPair_rightProbe (a : Radical × Radical) (j : Fin 2) :
    action (radicalPair a) (rightProbe j) = rightProbe j + a.2.toAdd j • point := by
  change baseAction (radical a.1, radical a.2)
    (coordinates (basisVector 0 ⊗ₜ[ZMod 2] basisVector j.succ)) = _
  rw [baseAction_tmul, radical_basis_zero, radical_basis_succ,
    TensorProduct.tmul_add, TensorProduct.tmul_smul, map_add, map_smul]
  rfl

/-- Every nontrivial radical image supplies a surjective binary character and
a vector translated by its value times the marked point. No injectivity of
the map from the original actor is required. -/
theorem exists_binary_translation {A : Type*} [_root_.Group A]
    (q : A →* Radical × Radical) (hq : ∃ a : A, q a ≠ 1) :
    ∃ (χ : A →* Multiplicative (ZMod 2)) (w : Space),
      Function.Surjective χ ∧ ∀ a : A,
        action (radicalPair (q a)) w = w + (χ a).toAdd • point := by
  have hsurj (χ : A →* Multiplicative (ZMod 2)) (a : A)
      (ha : (χ a).toAdd ≠ 0) : Function.Surjective χ := by
    have hbinary : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    have haone := (hbinary (χ a).toAdd).resolve_left ha
    intro y
    rcases hbinary y.toAdd with hy | hy
    · refine ⟨1, ?_⟩
      rw [map_one]
      exact congrArg Multiplicative.ofAdd hy.symm
    · exact ⟨a, congrArg Multiplicative.ofAdd (haone.trans hy.symm)⟩
  obtain ⟨a,ha⟩ := hq
  by_cases hleft : (q a).1 = 1
  · have hright : (q a).2 ≠ 1 := by
      intro hr
      exact ha (Prod.ext hleft hr)
    obtain ⟨j,hj⟩ : ∃ j : Fin 2, (q a).2.toAdd j ≠ 0 := by
      by_contra h
      push Not at h
      apply hright
      exact congrArg Multiplicative.ofAdd (funext h)
    let χ := (radicalCoordinate j).comp ((MonoidHom.snd Radical Radical).comp q)
    refine ⟨χ,rightProbe j,hsurj χ a hj,?_⟩
    intro b
    exact radicalPair_rightProbe (q b) j
  · obtain ⟨j,hj⟩ : ∃ j : Fin 2, (q a).1.toAdd j ≠ 0 := by
      by_contra h
      push Not at h
      apply hleft
      exact congrArg Multiplicative.ofAdd (funext h)
    let χ := (radicalCoordinate j).comp ((MonoidHom.fst Radical Radical).comp q)
    refine ⟨χ,leftProbe j,hsurj χ a hj,?_⟩
    intro b
    exact radicalPair_leftProbe (q b) j

end BinaryTensorThree
