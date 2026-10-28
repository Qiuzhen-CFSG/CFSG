module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.Torus
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.BruhatCoverage.FixedWeyl.BinaryTits

/-!
# Weyl words over every Ree coefficient field

The integral Tits cancellation and braid relations specialize in characteristic
two with all signs equal to one. Thus equality of simple matrix words is exactly
equality in the genuine F₄ Weyl group, over every coefficient field. Root columns
record this action with scalar one; arbitrary torus factors are kept separate.

This extends the binary proof in `BruhatCoverage/FixedWeyl/BinaryTits.lean`.
Source: Steinberg's integral Tits relations and GLS3 2.3.2–4,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace ReeF4.SectionGeometry.BNPair.QuotientGeometry
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction Matrix
open Parabolics Parabolics.Binary.FixedGeometry
open Parabolics.Binary.FixedGeometry.BruhatCoverage.FixedWeyl
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
open NormalizerGeometry
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private abbrev B := typeF4RootPairing_base.support
private abbrev F (m : ℕ) := ReeF4.CoefficientField m

variable {m : ℕ}

private theorem cancellation (i : B) : specializeMatrix (S := F m) (titsCancellation i) = 1 := by
  ext x y
  cases y with
  | inl j =>
    have h := congrFun (titsCancellation_mulVec_u i j) x
    simpa [u, Matrix.mulVec_single_one, Pi.single_apply,
      specializeMatrix, Matrix.one_apply] using
      congrArg (Int.castRingHom (F m)) h
  | inr j =>
    have h := congrFun (titsCancellation_mulVec_v i j) x
    have hs : (titsCancellationSign i j : F m) = 1 := by
      simpa [mul_self_eq_one_iff, CharTwo.neg_eq] using
        congrArg (Int.castRingHom (F m)) (titsCancellationSign_mul_self i j)
    simpa [v, Matrix.mulVec_single_one, Pi.single_apply, hs,
      specializeMatrix, Matrix.one_apply] using
      congrArg (Int.castRingHom (F m)) h

private theorem sign (word : List B) (j : F4Chevalley.Root) :
    (titsWordSign word j : F m) = 1 := by
  induction word with
  | nil => simp [titsWordSign]
  | cons i word ih => simp [titsWordSign, ih, CharTwo.neg_eq]

private theorem specialize_move (C : CoxeterMatrix B)
    (hC : ∀ i j : B,
      C i j = orderOf (typeF4RootPairing_base.simpleReflection i *
        typeF4RootPairing_base.simpleReflection j))
    {l k : List B} (h : CoxeterMove C l k) :
    specializeMatrix (S := F m) (titsWord l) = specializeMatrix (titsWord k) := by
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
    specializeMatrix (S := F m) (titsWord l) = specializeMatrix (titsWord k) := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (specialize_move C hC hstep)

private theorem specialize_eq {l k : List B}
    (h : typeF4RootPairing_base.wordProd l = typeF4RootPairing_base.wordProd k) :
    specializeMatrix (S := F m) (titsWord l) = specializeMatrix (titsWord k) := by
  obtain ⟨C, _, hC, _⟩ := typeF4RootPairing_base.weylGroup_coxeterPresentation
  obtain ⟨l', hl', hredl, hpathl⟩ :=
    typeF4RootPairing_base.exists_reducedWord_reflTransGen_coxeterMove C hC l
  obtain ⟨k', hk', hredk, hpathk⟩ :=
    typeF4RootPairing_base.exists_reducedWord_reflTransGen_coxeterMove C hC k
  exact (specialize_path C hC hpathl).trans
    ((congrArg (specializeMatrix (S := F m))
      (titsWord_eq_of_reducedWords C hC (hl'.trans (h.trans hk'.symm)) hredl hredk)).trans
        (specialize_path C hC hpathk).symm)

private theorem root_column (word : List B) (j : F4Chevalley.Root)
    (x : B ⊕ F4Chevalley.Root) :
    specializeMatrix (S := F m) (titsWord word) x (.inr j) =
      if x = .inr (reflectionWord word j) then 1 else 0 := by
  have h := congrFun (titsWord_mulVec_v word j) x
  simpa [v, Matrix.mulVec_single_one, Pi.single_apply,
    specializeMatrix, sign] using congrArg (Int.castRingHom (F m)) h

private theorem reflection_eq {l k : List B}
    (h : specializeMatrix (S := F m) (titsWord l) = specializeMatrix (titsWord k))
    (j : F4Chevalley.Root) : reflectionWord l j = reflectionWord k j := by
  have he := congrArg (fun A => A (.inr (reflectionWord l j)) (.inr j)) h
  rw [root_column, root_column] at he
  simpa only [ite_true, Sum.inr.injEq, eq_ite_iff, one_ne_zero, and_false,
    or_false, and_true] using he

private theorem word_eq {l k : List B}
    (h : specializeMatrix (S := F m) (titsWord l) = specializeMatrix (titsWord k)) :
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

/-- In every coefficient field, Tits matrices have exactly the equalities of the genuine Weyl group. -/
theorem simpleWord_eq_iff (m : ℕ) (l k : List (Fin 4)) :
    simpleWord m l = simpleWord m k ↔ rootWord l = rootWord k := by
  constructor
  · intro h
    apply word_eq
    have h' := congrArg (fun x : ReeF4.SplitGroup m => (x : ReeF4.MatrixUnits m)) h
    rw [simpleWord_coe, simpleWord_coe] at h'
    exact congrArg Units.val h'
  · intro h
    apply Subtype.ext
    rw [simpleWord_coe, simpleWord_coe]
    apply Units.ext
    exact specialize_eq h


/-- Every simple word lies in the actual split normalizer-word subgroup. -/
theorem simpleWord_mem_splitNormalizerWords (m : ℕ) (l : List (Fin 4)) :
    simpleWord m l ∈ splitNormalizerWords m := by
  induction l with
  | nil => exact (splitNormalizerWords m).one_mem
  | cons i l ih =>
    exact (splitNormalizerWords m).mul_mem
      (weylWord_mem_splitNormalizerWords m (typeF4SimpleRootIndex i) 1) ih

/-- Simple Weyl words have their genuine Weyl permutation and unit root scalars. -/
theorem simpleWord_rootMonomial (m : ℕ) (l : List (Fin 4)) :
    RootMonomial (simpleWord m l).val.val
      (typeF4RootPairing.weylGroupToPerm (rootWord l)) (fun _ => 1) := by
  obtain ⟨e, c, hc⟩ := splitNormalizerWords_rootMonomial
    (simpleWord_mem_splitNormalizerWords m l)
  refine ⟨?_, hc.2⟩
  intro i r
  have he := congrArg Units.val (simpleWord_coe m l)
  rw [he]
  change specializeMatrix (S := CoefficientField m)
    (titsWord (l.map typeF4RootPairing_baseEquiv)) i (.inr r) = _
  rw [root_column, reflectionWord_eq_weylGroupToPerm]
  rfl

end ReeF4.SectionGeometry.BNPair.QuotientGeometry
