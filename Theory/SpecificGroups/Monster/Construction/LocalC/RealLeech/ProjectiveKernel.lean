module

public import Theory.SpecificGroups.Monster.Construction.LocalC.RealLeech.Extension

/-!
# The scalar kernel of the actual Leech actions

An isometry fixing every minimal-vector line is scalar. The short glue
vector has nonzero pairing with each `4(e_i + e_j)`, so fixation of the
glue vector forces fixation of every such pair vector. Three pair vectors
recover `8e_i`; these span the real space. Composing with lattice negation
handles the other sign. Short-class uniqueness then gives the exact kernel
of the actual action on `Λ/2Λ`, without Conway simplicity or order.

Source: Aschbacher, *Sporadic Groups*, Sections 22–23, especially Lemma
23.3, and Section 27, printed pp. 147–149. The concrete lattice vectors
and short-class uniqueness are reused from Gerald Höhn's ATLAS ports.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix
open Atlas.Codes Atlas.Lattices
namespace Sporadic.Monster.Construction.LocalC

private def glueShort : LeechShell 4 :=
  ⟨⟨oddGlue ((0,0),0), oddGlue_mem _⟩, oddGlue_norm _⟩

private def pairVector (a b : Omega) : leech :=
  ⟨coordinateVector a 4 + coordinateVector b 4, coordinate_pair_mem a b⟩

private theorem pair_glue_nonzero (a b : Omega) (hab : a ≠ b) :
    integerDot glueShort.val.val (pairVector a b).val ≠ 0 := by
  change integerDot (oddGlue ((0,0),0)) (coordinateVector a 4 + coordinateVector b 4) ≠ 0
  rw [integerDot_add_right, integerDot_coordinateVector, integerDot_coordinateVector]
  simp only [oddGlue]
  split_ifs <;> simp_all

private theorem pair_fixed (g : LeechIsometryGroup)
    (hg : ∀ x : LeechShell 4, g.val x.val = x.val ∨ g.val x.val = -x.val)
    (hu : g.val glueShort.val = glueShort.val) (a b : Omega) (hab : a ≠ b) :
    g.val (pairVector a b) = pairVector a b := by
  rcases hg ⟨pairVector a b, pair_norm a b hab⟩ with h | h
  · exact h
  · have he := g.prop glueShort.val (pairVector a b)
    rw [hu, h] at he
    have hn : integerDot glueShort.val.val (-(pairVector a b)).val =
        -integerDot glueShort.val.val (pairVector a b).val := by
      simp [integerDot]
    rw [hn] at he
    exact False.elim (pair_glue_nonzero a b hab (by omega))

private theorem eq_one_of_glue_fixed (g : LeechIsometryGroup)
    (hg : ∀ x : LeechShell 4, g.val x.val = x.val ∨ g.val x.val = -x.val)
    (hu : g.val glueShort.val = glueShort.val) : g = 1 := by
  have haxis (i : Fin 24) : g.val (leechAxis i) = leechAxis i := by
    obtain ⟨j, hij⟩ := exists_ne i
    obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide)
    have he : leechAxis i = pairVector (coordinateMarking i) (coordinateMarking j) +
        pairVector (coordinateMarking i) (coordinateMarking k) -
        pairVector (coordinateMarking j) (coordinateMarking k) := by
      apply Subtype.ext
      ext a
      simp only [leechAxis, pairVector, Submodule.coe_sub, Submodule.coe_add,
        Pi.add_apply, Pi.sub_apply, coordinateVector, Pi.single_apply]
      split_ifs <;> ring
    rw [he, map_sub, map_add,
      pair_fixed g hg hu _ _ (coordinateMarking.injective.ne hij.symm),
      pair_fixed g hg hu _ _ (coordinateMarking.injective.ne hki.symm),
      pair_fixed g hg hu _ _ (coordinateMarking.injective.ne hkj.symm)]
  apply realLeechRepresentation_faithful
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun ℝ (Fin 24)).ext
  intro i
  have hi : realLeechRepresentation g (leechVector (leechAxis i)) =
      realLeechRepresentation 1 (leechVector (leechAxis i)) := by
    simp only [realLeechRepresentation_agrees, haxis]
    rfl
  rw [leechVector_axis, map_smul, map_smul] at hi
  exact (smul_right_injective _ (by positivity : (8 / Real.sqrt (8 : ℝ)) ≠ 0)) hi

/-- Fixing the actual short lines forces a single global sign. -/
theorem leech_short_lines_kernel (g : LeechIsometryGroup) :
    (∀ x : LeechShell 4, g.val x.val = x.val ∨ g.val x.val = -x.val) ↔
      g = 1 ∨ g = negationIsometry := by
  constructor
  · intro hg
    rcases hg glueShort with hu | hu
    · exact Or.inl (eq_one_of_glue_fixed g hg hu)
    · have hh : negationIsometry * g = 1 := by
        apply eq_one_of_glue_fixed
        · intro x
          change negationIsometry.val (g.val x.val) = x.val ∨
            negationIsometry.val (g.val x.val) = -x.val
          rw [negationIsometry_apply]
          rcases hg x with h | h
          · exact Or.inr (congrArg Neg.neg h)
          · exact Or.inl (by rw [h, neg_neg])
        · change negationIsometry.val (g.val glueShort.val) = glueShort.val
          rw [negationIsometry_apply, hu, neg_neg]
      right
      have he := congrArg (fun h : LeechIsometryGroup => negationIsometry * h) hh
      simpa only [← mul_assoc, negationIsometry_sq, one_mul, mul_one] using he
  · rintro (rfl | rfl) x
    · exact Or.inl rfl
    · exact Or.inr (negationIsometry_apply x.val)

/-- The binary action has precisely identity and lattice negation as kernel. -/
theorem leechModTwoRepresentation_kernel (g : LeechIsometryGroup) :
    leechModTwoRepresentation g = 1 ↔ g = 1 ∨ g = negationIsometry := by
  constructor
  · intro hg
    apply (leech_short_lines_kernel g).mp
    intro x
    have he : leechReduction (g.val x.val) = leechReduction x.val := by
      rw [← leechModTwoRepresentation_reduce, hg]
      rfl
    apply leech_congruent_short_unique _ _ he
    have hx := leech_shell_halfNorm 4 x
    have hy := leech_shell_halfNorm 4 (shellPermutation g 4 x)
    change 2 * leechHalfNorm (g.val x.val) = 4 at hy
    omega
  · rintro (rfl | rfl)
    · exact map_one _
    · apply LinearEquiv.ext
      intro a
      obtain ⟨x, rfl⟩ := leechReduction_surjective a
      rw [leechModTwoRepresentation_reduce, negationIsometry_apply, leechReduction_neg]
      rfl

end Sporadic.Monster.Construction.LocalC
