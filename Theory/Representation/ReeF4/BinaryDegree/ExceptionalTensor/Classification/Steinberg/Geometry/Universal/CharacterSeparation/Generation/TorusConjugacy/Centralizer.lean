module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.TorusConjugacy.MatrixSupport
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism.ShortTransport
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Simple.RootGeometry

/-!
# The literal F4 split-torus centralizer in characteristic two

A matrix in the root-generated Chevalley carrier that commutes with every
concrete torus matrix is itself a concrete torus matrix. This holds over any
algebraically closed field of characteristic two, in particular over the
algebraic closure of any finite field of characteristic two.

The weight-support calculation leaves a Cartan block and one scalar per root.
Adjoint equivariance for the actual root-generated group, together with the
trivial common kernel of the short root operators, forces the Cartan block to
be the identity. The opposite-simple-root equations give inverse root scalars.
The inverse Cartan matrix then supplies a torus element with the same four
simple-root scalars. After division by this element, the matrix commutes with
the positive and negative simple root operators. For every F4 root-string step,
one of the forward and reverse coefficients is one: otherwise the string would
have endpoints differing by three times a root. Induction by simple-root
addition therefore fixes every root coordinate and proves the normalized
matrix is the identity.

All group constraints come from the literal carrier and its checked adjoint
transport. Neither maximality of this torus nor an abstract root-model
identification is used. The parent can use the resulting matrix theorem to
establish maximality and assemble its model-conjugacy argument.

Sources: GLS3, Sections 1.4 and 1.9 (`refs/KGroup/GLS3/Chapter1.tex`),
and the integral admissible-lattice construction in
`F4IntegralChevalleyRepresentation` and `IntegralChevalleyTorusConjugation`.
-/

public section

open scoped Matrix BigOperators Classical
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open ReeF4.WordRelations.ShortOperators
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism

namespace Theory.AlgebraicGroup.F4Chevalley.TorusConjugacy
noncomputable section
variable {k : Type*} [Field k] [IsAlgClosed k]
local instance : InvolutiveNeg Root := typeF4RootPairing.indexNeg

private lemma matrix_mem_generated_of_mem_ambient
    (A : (Matrix BasisIndex BasisIndex k)ˣ)
    (hA : matrixToAmbient A ∈ ambientCarrierSubgroup (k := k)) :
    A ∈ matrixGroup k := by
  have hle : ambientCarrierSubgroup (k := k) ≤ (matrixGroup k).map matrixToAmbient := by
    change Subgroup.closure _ ≤ _
    apply (Subgroup.closure_le _).2
    intro x hx
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
    obtain ⟨t, rfl⟩ := hr
    refine Subgroup.mem_map.mpr ⟨rootCurve r (Multiplicative.toAdd
      (additiveGroupPointEquiv k t)), Subgroup.subset_closure ⟨(_, _), rfl⟩, ?_⟩
    rw [matrixToAmbient_root, kPlusPoint_coordinate]
  obtain ⟨B, hB, he⟩ := Subgroup.mem_map.mp (hle hA)
  exact (matrixToAmbient_bijective.1 he) ▸ hB

private lemma matrix_root_column
    (A : (Matrix BasisIndex BasisIndex k)ˣ)
    (hA : ∀ u : Fin 4 → kˣ, Commute A (torusElement u)) (r : Root) :
    (A : Matrix BasisIndex BasisIndex k) *ᵥ Pi.single (Sum.inr r) 1 =
      (A.val (Sum.inr r) (Sum.inr r)) • Pi.single (Sum.inr r) 1 := by
  ext i
  by_cases hi : i = Sum.inr r
  · subst i
    simp
  · simpa [Matrix.mulVec_single_one, Pi.single_apply, hi] using
      matrix_root_column_support A hA r i hi

private lemma matrix_root_diagonal_ne_zero
    (A : (Matrix BasisIndex BasisIndex k)ˣ)
    (hA : ∀ u : Fin 4 → kˣ, Commute A (torusElement u)) (r : Root) :
    A.val (Sum.inr r) (Sum.inr r) ≠ 0 := by
  intro hz
  have h := matrix_root_column A hA r
  rw [hz, zero_smul] at h
  have hi := congrArg (fun v => ((A⁻¹).val : Matrix BasisIndex BasisIndex k) *ᵥ v) h
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at hi
  have := congrFun hi (Sum.inr r)
  simp at this

private abbrev rootMatrix (r : Root) : Matrix BasisIndex BasisIndex k :=
  (integralOperators.rootOperator r).map (Int.castRingHom k)

private lemma matrix_root_intertwines [CharP k 2]
    (A : (Matrix BasisIndex BasisIndex k)ˣ)
    (hmem : matrixToAmbient A ∈ ambientCarrierSubgroup (k := k))
    (hA : ∀ u : Fin 4 → kˣ, Commute A (torusElement u)) (r : Root) :
    (A.val (Sum.inr r) (Sum.inr r)) • (rootMatrix r * A.val) =
      A.val * rootMatrix r := by
  have he := adjointMap_equivariant A (matrix_mem_generated_of_mem_ambient A hmem)
    (Pi.single (Sum.inr r) 1)
  rw [matrix_root_column A hA, map_smul, adjointMap_root_single, Matrix.smul_mul] at he
  exact he

/-- Every Cartan basis vector is fixed by a carrier matrix centralizing the split torus. -/
lemma matrix_cartan_column [CharP k 2]
    (A : (Matrix BasisIndex BasisIndex k)ˣ)
    (hmem : matrixToAmbient A ∈ ambientCarrierSubgroup (k := k))
    (hA : ∀ u : Fin 4 → kˣ, Commute A (torusElement u))
    (j : typeF4RootPairing_base.support) :
    A.val *ᵥ Pi.single (Sum.inl j) 1 = Pi.single (Sum.inl j) 1 := by
  apply sub_eq_zero.mp
  apply rootOperator_commonKernel
  intro r _
  rw [Matrix.mulVec_sub, sub_eq_zero]
  apply smul_right_injective (BasisIndex → k) (matrix_root_diagonal_ne_zero A hA r)
  have he := congrArg (fun B : Matrix BasisIndex BasisIndex k =>
    B *ᵥ Pi.single (Sum.inl j) 1) (matrix_root_intertwines A hmem hA r)
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    rootOperator_cartanColumn, Matrix.mulVec_smul, matrix_root_column A hA] at he
  rw [rootOperator_cartanColumn]
  exact he.trans (smul_comm _ _ _)

omit [IsAlgClosed k] in
private lemma simple_opposite_column (i : typeF4RootPairing_base.support) :
    rootMatrix (k := k) i *ᵥ Pi.single (Sum.inr (-i.val)) 1 =
      Pi.single (Sum.inl i) 1 := by
  have he := congrArg (fun v : BasisIndex → ℤ => (Int.castRingHom k) ∘ v)
    (eMatrix_mulVec_v_neg (P := typeF4RootPairing) i)
  have hm (M : Matrix BasisIndex BasisIndex ℤ) (v : BasisIndex → ℤ) :
      (Int.castRingHom k) ∘ (M *ᵥ v) =
        M.map (Int.castRingHom k) *ᵥ ((Int.castRingHom k) ∘ v) := by
    ext j
    exact (Int.castRingHom k).map_mulVec M v j
  have hs (j : BasisIndex) : (Int.castRingHom k) ∘ Pi.single j (1 : ℤ) =
      Pi.single j 1 := by
    ext l
    simp [Pi.single_apply]
  simp only [hm, v, u, hs] at he
  simpa only [rootMatrix, integralOperators, integralChevalleyRootOperators,
    rootOperator_simple] using he

private lemma matrix_simple_opposite_diagonal [CharP k 2]
    (A : (Matrix BasisIndex BasisIndex k)ˣ)
    (hmem : matrixToAmbient A ∈ ambientCarrierSubgroup (k := k))
    (hA : ∀ u : Fin 4 → kˣ, Commute A (torusElement u))
    (i : typeF4RootPairing_base.support) :
    A.val (Sum.inr i.val) (Sum.inr i.val) *
      A.val (Sum.inr (-i.val)) (Sum.inr (-i.val)) = 1 := by
  have he := congrArg (fun B : Matrix BasisIndex BasisIndex k =>
    B *ᵥ Pi.single (Sum.inr (-i.val)) 1) (matrix_root_intertwines A hmem hA i.val)
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    matrix_root_column A hA, Matrix.mulVec_smul, simple_opposite_column,
    matrix_cartan_column A hmem hA] at he
  have := congrFun he (Sum.inl i)
  simpa using this

private lemma root_neg (r : Root) : typeF4RootPairing.root (-r) = -typeF4RootPairing.root r := by
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm r r) = _
  rw [typeF4RootPairing.root_reflectionPerm, typeF4RootPairing.reflection_apply_self]

private lemma root_string_step_one (s r t : Root)
    (h : typeF4RootPairing.root t = typeF4RootPairing.root s + typeF4RootPairing.root r) :
    typeF4RootPairing.chainBotCoeff s r = 0 ∨
      typeF4RootPairing.chainBotCoeff (-s) t = 0 := by
  by_contra hz
  push Not at hz
  have hr := typeF4RootPairing.linearIndependent_of_add_mem_range_root' ⟨t, h⟩
  have hs : typeF4RootPairing.root r = typeF4RootPairing.root (-s) +
      typeF4RootPairing.root t := by
    rw [root_neg, h]
    abel
  have ht := typeF4RootPairing.linearIndependent_of_add_mem_range_root' ⟨r, hs⟩
  obtain ⟨a, ha⟩ := (typeF4RootPairing.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hr).mpr
    (show 1 ≤ typeF4RootPairing.chainBotCoeff s r by omega)
  obtain ⟨b, hb⟩ := (typeF4RootPairing.root_sub_nsmul_mem_range_iff_le_chainBotCoeff ht).mpr
    (show 1 ≤ typeF4RootPairing.chainBotCoeff (-s) t by omega)
  apply ReeF4.WordRelations.root_ne_add_three_nsmul s a b
  rw [ha, hb, one_smul, one_smul, root_neg, h]
  module

private lemma matrix_diagonal_eq_of_operator_column
    (A : (Matrix BasisIndex BasisIndex k)ˣ)
    (hA : ∀ u : Fin 4 → kˣ, Commute A (torusElement u))
    (s r t : Root) (hc : Commute A.val (rootMatrix s))
    (hcol : rootMatrix (k := k) s *ᵥ Pi.single (Sum.inr r) 1 =
      Pi.single (Sum.inr t) 1) :
    A.val (Sum.inr t) (Sum.inr t) = A.val (Sum.inr r) (Sum.inr r) := by
  have he := congrArg (fun B : Matrix BasisIndex BasisIndex k =>
    B *ᵥ Pi.single (Sum.inr r) 1) hc.eq
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol,
    matrix_root_column A hA, matrix_root_column A hA, Matrix.mulVec_smul, hcol] at he
  simpa using congrFun he (Sum.inr t)

private lemma matrix_diagonal_eq_of_root_add [CharP k 2]
    (A : (Matrix BasisIndex BasisIndex k)ˣ)
    (hA : ∀ u : Fin 4 → kˣ, Commute A (torusElement u))
    (s r t : Root) (hc : Commute A.val (rootMatrix s))
    (hn : Commute A.val (rootMatrix (-s)))
    (hadd : typeF4RootPairing.root t =
      typeF4RootPairing.root s + typeF4RootPairing.root r) :
    A.val (Sum.inr t) (Sum.inr t) = A.val (Sum.inr r) (Sum.inr r) := by
  rcases root_string_step_one s r t hadd with h | h
  · apply matrix_diagonal_eq_of_operator_column A hA s r t hc
    simpa only [h, Nat.cast_zero, zero_add, one_smul] using
      rootOperator_rootColumn_add (K := k) s r t hadd
  · symm
    apply matrix_diagonal_eq_of_operator_column A hA (-s) t r hn
    have he : typeF4RootPairing.root r =
        typeF4RootPairing.root (-s) + typeF4RootPairing.root t := by
      rw [root_neg, hadd]
      abel
    simpa only [h, Nat.cast_zero, zero_add, one_smul] using
      rootOperator_rootColumn_add (K := k) (-s) t r he

private lemma matrix_eq_one_of_simple_diagonal [CharP k 2]
    (A : (Matrix BasisIndex BasisIndex k)ˣ)
    (hmem : matrixToAmbient A ∈ ambientCarrierSubgroup (k := k))
    (hA : ∀ u : Fin 4 → kˣ, Commute A (torusElement u))
    (hsimple : ∀ i : typeF4RootPairing_base.support,
      A.val (Sum.inr i.val) (Sum.inr i.val) = 1) : A = 1 := by
  have hneg (i : typeF4RootPairing_base.support) :
      A.val (Sum.inr (-i.val)) (Sum.inr (-i.val)) = 1 := by
    simpa only [hsimple, one_mul] using matrix_simple_opposite_diagonal A hmem hA i
  have hc (r : Root) (hr : A.val (Sum.inr r) (Sum.inr r) = 1) :
      Commute A.val (rootMatrix r) := by
    have h := matrix_root_intertwines A hmem hA r
    rw [hr, one_smul] at h
    exact h.symm
  have hroot (r : Root) : A.val (Sum.inr r) (Sum.inr r) = 1 ∧
      A.val (Sum.inr (-r)) (Sum.inr (-r)) = 1 := by
    apply typeF4RootPairing_base.induction_add r
    · intro s hs
      change A.val (Sum.inr (-s)) (Sum.inr (-s)) = 1 ∧
        A.val (Sum.inr (-(-s))) (Sum.inr (-(-s))) = 1
      simpa only [neg_neg] using And.symm hs
    · intro s hs
      exact ⟨hsimple ⟨s, hs⟩, hneg ⟨s, hs⟩⟩
    · intro s i t he hs hi
      let j : typeF4RootPairing_base.support := ⟨i, hi⟩
      constructor
      · exact (matrix_diagonal_eq_of_root_add A hA i s t
          (hc i (hsimple j)) (hc (-i) (hneg j))
          (he.trans (add_comm _ _))).trans hs.1
      · have ht : typeF4RootPairing.root (-t) =
            typeF4RootPairing.root (-i) + typeF4RootPairing.root (-s) := by
          simp only [root_neg, he]
          abel
        exact (matrix_diagonal_eq_of_root_add A hA (-i) (-s) (-t)
          (hc (-i) (hneg j)) (by simpa only [neg_neg] using hc i (hsimple j)) ht).trans hs.2
  apply Units.ext
  ext i j
  have hcol : A.val *ᵥ Pi.single j 1 = Pi.single j 1 := by
    cases j with
    | inl j => exact matrix_cartan_column A hmem hA j
    | inr r => simpa only [(hroot r).1, one_smul] using matrix_root_column A hA r
  have he := congrFun hcol i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using he

omit [IsAlgClosed k] in
private lemma exists_torusElement_simple_diagonal (d : Fin 4 → kˣ) :
    ∃ u : Fin 4 → kˣ, ∀ j : Fin 4,
      basisTorusUnit u (Sum.inr (typeF4SimpleRootIndex j)) = d j := by
  refine ⟨fun i => ∏ j, (d j)⁻¹ ^ torusRecoveryExponent i j, ?_⟩
  intro j
  simp only [basisTorusUnit_simple, Fin.prod_univ_four]
  fin_cases j <;>
    norm_num [torusRecoveryExponent, typeF4CartanMatrix, Fin.ext_iff,
      Matrix.cons_val_two, Matrix.cons_val_three]
  all_goals
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    field_simp
    <;> ring_nf
    <;> rfl

/-- A carrier matrix commuting with the concrete split torus belongs to it. -/
theorem matrix_centralizer_eq_torusElement [CharP k 2]
    (A : (Matrix BasisIndex BasisIndex k)ˣ)
    (hmem : matrixToAmbient A ∈ ambientCarrierSubgroup (k := k))
    (hA : ∀ u : Fin 4 → kˣ, Commute A (torusElement u)) :
    ∃ u : Fin 4 → kˣ, A = torusElement u := by
  let d (j : Fin 4) : kˣ := Units.mk0
    (A.val (Sum.inr (typeF4SimpleRootIndex j)) (Sum.inr (typeF4SimpleRootIndex j)))
    (matrix_root_diagonal_ne_zero A hA _)
  obtain ⟨u, hu⟩ := exists_torusElement_simple_diagonal d
  let B := A * (torusElement u)⁻¹
  have hBmem : matrixToAmbient B ∈ ambientCarrierSubgroup (k := k) := by
    simp only [B, map_mul, map_inv]
    exact Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ (matrixToAmbient_torus_mem (torusParameter u)))
  have hBcomm (v : Fin 4 → kˣ) : Commute B (torusElement v) := by
    have ht : Commute (torusElement u) (torusElement v) := by
      change torusElement u * torusElement v = torusElement v * torusElement u
      rw [← torusElement_mul, ← torusElement_mul, mul_comm]
    exact (hA v).mul_left ht.inv_left
  have hBsimple (i : typeF4RootPairing_base.support) :
      B.val (Sum.inr i.val) (Sum.inr i.val) = 1 := by
    obtain ⟨j, rfl⟩ := typeF4RootPairing_baseEquiv.surjective i
    change (A.val * Matrix.diagonal (fun a : BasisIndex =>
      (↑((basisTorusUnit u a)⁻¹) : k))) (Sum.inr (typeF4SimpleRootIndex j))
        (Sum.inr (typeF4SimpleRootIndex j)) = 1
    rw [Matrix.mul_diagonal, hu]
    change (d j : k) * ((d j)⁻¹ : kˣ) = 1
    exact Units.mul_inv _
  refine ⟨u, ?_⟩
  exact mul_inv_eq_one.mp (matrix_eq_one_of_simple_diagonal B hBmem hBcomm hBsimple)

end
end Theory.AlgebraicGroup.F4Chevalley.TorusConjugacy
