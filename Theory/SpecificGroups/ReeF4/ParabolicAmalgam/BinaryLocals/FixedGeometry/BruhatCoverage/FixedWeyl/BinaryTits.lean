module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.BruhatCoverage.Basic
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.WeylLifts
public import Theory.AlgebraicGroup.RootSystems.WeylGroupCoxeterPresentation

/-!
# Binary Tits matrices and the genuine F₄ Weyl group

Two numbered simple words give equal binary matrices exactly when they give the
same Weyl element. For one direction, Coxeter deletion and Matsumoto reduce the
words to a common reduced representative: the integral braid identities survive
specialization, and the diagonal cancellation signs become one in characteristic
two. Conversely, each root column is the basis vector indexed by the reflected
root, so equality of matrices implies equality of the reflection action. The
simple roots span the weight space, making this action faithful.

In particular the simple matrix lifts are involutions and every element of their
subgroup has a positive-word representative. This is the concrete comparison
needed for fixed Weyl descent; it does not assume a Tits system for the Ree group.

Source: the integral Tits relations of Steinberg, *Lectures on Chevalley Groups*,
and the Weyl/normalizer comparison in GLS3 §§1.8–1.9 and 2.3.4.
-/

public section
namespace ReeF4.Parabolics.Binary.FixedGeometry.BruhatCoverage.FixedWeyl

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction Matrix

noncomputable section
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private abbrev B := typeF4RootPairing_base.support
private abbrev F := ReeF4.CoefficientField 0

private theorem cancellation (i : B) : specializeMatrix (S := F) (titsCancellation i) = 1 := by
  ext x y
  cases y with
  | inl j =>
    have h := congrFun (titsCancellation_mulVec_u i j) x
    simpa [u, Matrix.mulVec_single_one, Pi.single_apply,
      specializeMatrix, Matrix.one_apply] using
      congrArg (Int.castRingHom F) h
  | inr j =>
    have h := congrFun (titsCancellation_mulVec_v i j) x
    have hs : (titsCancellationSign i j : F) = 1 := by
      simpa [mul_self_eq_one_iff, CharTwo.neg_eq] using
        congrArg (Int.castRingHom F) (titsCancellationSign_mul_self i j)
    simpa [v, Matrix.mulVec_single_one, Pi.single_apply, hs,
      specializeMatrix, Matrix.one_apply] using
      congrArg (Int.castRingHom F) h

private theorem sign (word : List B) (j : F4Chevalley.Root) :
    (titsWordSign word j : F) = 1 := by
  induction word with
  | nil => simp [titsWordSign]
  | cons i word ih => simp [titsWordSign, ih, CharTwo.neg_eq]

private theorem specialize_move (C : CoxeterMatrix B)
    (hC : ∀ i j : B,
      C i j = orderOf (typeF4RootPairing_base.simpleReflection i *
        typeF4RootPairing_base.simpleReflection j))
    {l k : List B} (h : CoxeterMove C l k) :
    specializeMatrix (S := F) (titsWord l) = specializeMatrix (titsWord k) := by
  rcases h with ⟨left, right, i, rfl, rfl⟩ | ⟨left, right, i, j, rfl, rfl⟩
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [titsWord_insert_cancellation, titsWord_append]
    simp only [specializeMatrix_mul, cancellation, Matrix.mul_one]
  · rw [titsWord_insert_braid C hC]

private theorem specialize_path (C : CoxeterMatrix B)
    (hC : ∀ i j : B,
      C i j = orderOf (typeF4RootPairing_base.simpleReflection i *
        typeF4RootPairing_base.simpleReflection j))
    {l k : List B} (h : Relation.ReflTransGen (CoxeterMove C) l k) :
    specializeMatrix (S := F) (titsWord l) = specializeMatrix (titsWord k) := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (specialize_move C hC hstep)

private theorem specialize_eq {l k : List B}
    (h : typeF4RootPairing_base.wordProd l = typeF4RootPairing_base.wordProd k) :
    specializeMatrix (S := F) (titsWord l) = specializeMatrix (titsWord k) := by
  obtain ⟨C, _, hC, _⟩ := typeF4RootPairing_base.weylGroup_coxeterPresentation
  obtain ⟨l', hl', hredl, hpathl⟩ :=
    typeF4RootPairing_base.exists_reducedWord_reflTransGen_coxeterMove C hC l
  obtain ⟨k', hk', hredk, hpathk⟩ :=
    typeF4RootPairing_base.exists_reducedWord_reflTransGen_coxeterMove C hC k
  exact (specialize_path C hC hpathl).trans
    ((congrArg (specializeMatrix (S := F))
      (titsWord_eq_of_reducedWords C hC (hl'.trans (h.trans hk'.symm)) hredl hredk)).trans
        (specialize_path C hC hpathk).symm)

private theorem root_column (word : List B) (j : F4Chevalley.Root)
    (x : B ⊕ F4Chevalley.Root) :
    specializeMatrix (S := F) (titsWord word) x (.inr j) =
      if x = .inr (reflectionWord word j) then 1 else 0 := by
  have h := congrFun (titsWord_mulVec_v word j) x
  simpa [v, Matrix.mulVec_single_one, Pi.single_apply,
    specializeMatrix, sign] using congrArg (Int.castRingHom F) h

private theorem reflection_eq {l k : List B}
    (h : specializeMatrix (S := F) (titsWord l) = specializeMatrix (titsWord k))
    (j : F4Chevalley.Root) : reflectionWord l j = reflectionWord k j := by
  have he := congrArg (fun A => A (.inr (reflectionWord l j)) (.inr j)) h
  rw [root_column, root_column] at he
  simpa only [ite_true, Sum.inr.injEq, eq_ite_iff, one_ne_zero, and_false,
    or_false, and_true] using he

private theorem word_eq {l k : List B}
    (h : specializeMatrix (S := F) (titsWord l) = specializeMatrix (titsWord k)) :
    typeF4RootPairing_base.wordProd l = typeF4RootPairing_base.wordProd k := by
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective
  apply LinearEquiv.toLinearMap_injective
  apply typeF4RootPairing_base.toWeightBasis.ext
  intro i
  simp only [LinearEquiv.coe_coe, RootPairing.Base.toWeightBasis_apply]
  change typeF4RootPairing_base.wordProd l • typeF4RootPairing.root i =
    typeF4RootPairing_base.wordProd k • typeF4RootPairing.root i
  rw [← root_reflectionWord, ← root_reflectionWord, reflection_eq h]

/-- Evaluation of a numbered word in the genuine F₄ reflection group. -/
@[expose] def rootWord (l : List (Fin 4)) : typeF4RootPairing.weylGroup :=
  typeF4RootPairing_base.wordProd (l.map typeF4RootPairing_baseEquiv)

/-- Concatenation of simple matrix words is matrix multiplication. -/
theorem simpleWord_append (m : ℕ) (l k : List (Fin 4)) :
    simpleWord m (l ++ k) = simpleWord m l * simpleWord m k := by
  simp [simpleWord, List.map_append, List.prod_append]

/-- Concatenation of reflection words is Weyl-group multiplication. -/
theorem rootWord_append (l k : List (Fin 4)) :
    rootWord (l ++ k) = rootWord l * rootWord k := by
  simp [rootWord]

/-- Binary Tits matrices have exactly the equalities of the genuine Weyl group. -/
theorem simpleWord_eq_iff_rootWord_eq (l k : List (Fin 4)) :
    simpleWord 0 l = simpleWord 0 k ↔ rootWord l = rootWord k := by
  constructor
  · intro h
    apply word_eq
    have h' := congrArg (fun x : ReeF4.SplitGroup 0 => (x : ReeF4.MatrixUnits 0)) h
    rw [simpleWord_coe, simpleWord_coe] at h'
    exact congrArg Units.val h'
  · intro h
    apply Subtype.ext
    rw [simpleWord_coe, simpleWord_coe]
    apply Units.ext
    exact specialize_eq h

/-- The torus sign disappears in characteristic two, so simple lifts are involutions. -/
theorem simpleWord_simple_inv (i : Fin 4) :
    (simpleWord 0 [i])⁻¹ = simpleWord 0 [i] := by
  apply inv_eq_of_mul_eq_one_right
  rw [← simpleWord_append]
  change simpleWord 0 [i, i] = simpleWord 0 []
  apply (simpleWord_eq_iff_rootWord_eq _ _).mpr
  simp [rootWord]

/-- Every element of the split Weyl subgroup is a positive word in the four lifts. -/
theorem exists_simpleWord_of_mem {n : ReeF4.SplitGroup 0}
    (hn : n ∈ splitWeylSubgroup) : ∃ l : List (Fin 4), simpleWord 0 l = n := by
  induction hn using Subgroup.closure_induction'' with
  | one => exact ⟨[], rfl⟩
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨[i], rfl⟩
  | inv_mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨[i], (simpleWord_simple_inv i).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l, rfl⟩ := hx
    obtain ⟨k, rfl⟩ := hy
    exact ⟨l ++ k, simpleWord_append 0 l k⟩

end
end ReeF4.Parabolics.Binary.FixedGeometry.BruhatCoverage.FixedWeyl
