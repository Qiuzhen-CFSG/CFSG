module

public import Mathlib.GroupTheory.Perm.Support
public import Theory.AlgebraicGroup.RootSubgroups.Tangent
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.TypeASLDiagonalTorus
public import Theory.AlgebraicGroup.RootSystems.Classical

/-!
# Tangent root support for the special-linear diagonal torus

For the explicit diagonal maximal torus of `SL_(m+1)`, this module identifies
every nontrivial weight occurring in the identity tangent representation with
a unique ordered pair of distinct matrix coordinates.  With the inverse-weight
convention of `oneParameterTangent_isWeightVector`, that pair gives exactly
`typeASLRootWeight`.

The proof is the direct matrix-coordinate calculation.  Coordinate functions
generate the special-linear coordinate algebra and therefore separate tangent
derivations.  Differentiating the determinant-one relation gives the usual
trace-zero condition.  Diagonal conjugation scales the `(a,b)` coordinate by
`z_a * z_b⁻¹`; cancellation at a nonzero tangent coordinate identifies the
weight character.  The full Laurent character model of the diagonal torus and
the concrete type-A root embedding then prove uniqueness.  Thus the argument
uses no root-system classification theorem and supplies the coordinate support
input required by `TypeASLTorusRootClassification`.
-/

open scoped BigOperators

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

open StandardRootSystem

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

public section

noncomputable section

noncomputable abbrev typeASLTorus (m : ℕ) :=
  typeASLDiagonalTorus (k := k) m

@[expose]
public noncomputable def typeASLRootWeight (m : ℕ) (r : TypeARootIndex m) :
    TorusWeight (typeASLTorus (k := k) m) :=
  typeASLDiagonalCharacter (k := k) m
    (typeASLDiagonalEntryExponent m r.1.2 -
      typeASLDiagonalEntryExponent m r.1.1)

/-- The root indexed by `(i,j)` is the quotient of the `j`-th and `i`-th
diagonal entry characters. -/
public theorem typeASLRootWeight_eq_entryCharacters
    (m : ℕ) (r : TypeARootIndex m) :
    typeASLRootWeight (k := k) m r =
      typeASLDiagonalEntryCharacter (k := k) m r.1.2 *
        (typeASLDiagonalEntryCharacter (k := k) m r.1.1)⁻¹ := by
  apply Additive.ofMul.injective
  simp [typeASLRootWeight, typeASLDiagonalEntryCharacter,
    ← typeASLDiagonalCharacterAddEquiv_apply, sub_eq_add_neg]

private def matrixCoordinate (m : ℕ) (a b : Fin (m + 1)) :
    Variety.PolynomialFunction (slVariety k (m + 1)) :=
  Variety.PolynomialFunction.ofPolynomial _
    (MvPolynomial.X (ULift.up (a, b)))

private lemma matrixCoordinate_apply (m : ℕ) (a b : Fin (m + 1))
    (x : Variety.Point (slVariety k (m + 1))) :
    matrixCoordinate (k := k) m a b x = slPointMatrix (m + 1) x a b := by
  change evalPolynomial x.val (MvPolynomial.X (ULift.up (a, b))) = _
  rw [evalPolynomial_X]
  rfl

private lemma matrixCoordinate_one (m : ℕ) (a b : Fin (m + 1)) :
    matrixCoordinate (k := k) m a b 1 = if a = b then 1 else 0 := by
  rw [matrixCoordinate_apply]
  change (1 : Matrix.SpecialLinearGroup (Fin (m + 1)) k).1 a b = _
  exact Matrix.one_apply

private lemma matrixCoordinate_conjugation (m : ℕ)
    (a b : Fin (m + 1)) (g : Variety.Point (slVariety k (m + 1)))
    (z : Fin (m + 1) → kˣ)
    (hdiag : slPointMatrix (m + 1) g =
      Matrix.diagonal (fun i => (z i : k))) :
    (AlgebraicGroup.conjugationByMorphism (slVariety k (m + 1)) g).pullbackAlgHom
        (matrixCoordinate (k := k) m a b) =
      ((z a : k) * (z b : k)⁻¹) • matrixCoordinate m a b := by
  apply Variety.PolynomialFunction.ext
  intro x
  change (matrixCoordinate m a b)
      ((AlgebraicGroup.conjugationByMorphism
        (slVariety k (m + 1)) g).toFun x) = _
  rw [AlgebraicGroup.conjugationByMorphism_apply,
    matrixCoordinate_apply]
  simp only [polynomialFunction_smul_apply, matrixCoordinate_apply]
  have hginv : slPointMatrix (m + 1) g⁻¹ =
      Matrix.diagonal (fun i => ((z i : k)⁻¹)) := by
    have hmul : slPointMatrix (m + 1) g * slPointMatrix (m + 1) g⁻¹ = 1 := by
      change slPointMatrix (m + 1) (g * g⁻¹) = 1
      rw [mul_inv_cancel]
      rfl
    ext i j
    by_cases hij : i = j
    · subst j
      have he := congrFun (congrFun hmul i) i
      rw [hdiag, Matrix.mul_apply] at he
      have hsum : (z i : k) * slPointMatrix (m + 1) g⁻¹ i i = 1 := by
        simpa [Matrix.diagonal_apply, Matrix.one_apply] using he
      rw [Matrix.diagonal_apply_eq]
      exact eq_inv_of_mul_eq_one_right hsum
    · have he := congrFun (congrFun hmul i) j
      rw [hdiag, Matrix.mul_apply] at he
      have hzero : (z i : k) * slPointMatrix (m + 1) g⁻¹ i j = 0 := by
        simpa [Matrix.diagonal_apply, Matrix.one_apply, hij] using he
      have hzi : (z i : k) ≠ 0 := Units.ne_zero _
      have : slPointMatrix (m + 1) g⁻¹ i j = 0 :=
        (mul_eq_zero.mp hzero).resolve_left hzi
      simpa [Matrix.diagonal_apply_ne _ hij] using this
  rw [show slPointMatrix (m + 1) (g * x * g⁻¹) =
      slPointMatrix (m + 1) g * slPointMatrix (m + 1) x *
        slPointMatrix (m + 1) g⁻¹ by rfl, hdiag, hginv]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

private lemma exists_matrixCoordinate_ne_zero (m : ℕ)
    (D : IdentityPointDerivation (slVariety k (m + 1))) (hD : D ≠ 0) :
    ∃ a b : Fin (m + 1), D (matrixCoordinate (k := k) m a b) ≠ 0 := by
  by_contra h
  push Not at h
  apply hD
  apply Derivation.ext_of_adjoin_eq_top
    (Set.range fun i : (slVariety k (m + 1)).Coordinates =>
      Variety.PolynomialFunction.ofPolynomial _ (MvPolynomial.X i))
  · rw [Algebra.adjoin_range_eq_range_aeval]
    apply (AlgHom.range_eq_top _).2
    intro f
    obtain ⟨p, hp⟩ := f.representedBy
    refine ⟨p, ?_⟩
    apply Variety.PolynomialFunction.ext
    intro x
    rw [hp]
    have haeval :
        MvPolynomial.aeval (fun i : (slVariety k (m + 1)).Coordinates =>
          Variety.PolynomialFunction.ofPolynomial _ (MvPolynomial.X i)) =
          evaluationAlgHom (slVariety k (m + 1)) := by
      apply MvPolynomial.algHom_ext
      intro i
      apply Variety.PolynomialFunction.ext
      intro y
      rw [MvPolynomial.aeval_X]
      rfl
    rw [haeval]
    rfl
  · rintro _ ⟨q, rfl⟩
    simpa [matrixCoordinate] using h q.down.1 q.down.2

omit [IsAlgClosed k] in
private lemma identityPointDerivation_prod
    {G : Variety k} [AlgebraicGroup G] (D : IdentityPointDerivation G)
    {I : Type*} [DecidableEq I] (s : Finset I)
    (q : I → G.PolynomialFunction) :
    D (∏ i ∈ s, q i) =
      ∑ i ∈ s, (∏ j ∈ s.erase i, q j 1) * D (q i) := by
  induction s using Finset.induction_on with
  | empty => simp [D.map_one_eq_zero]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, D.leibniz, ih]
      have hsmul (f : G.PolynomialFunction) (c : k) :
          f • c = f 1 * c := rfl
      rw [hsmul, hsmul]
      have heval (t : Finset I) :
          (∏ i ∈ t, q i) 1 = ∏ i ∈ t, q i 1 := by
        let ev := polynomialFunctionPointAlgHom G 1
        change ev (∏ i ∈ t, q i) = _
        simp only [map_prod]
        rfl
      rw [heval]
      change q a 1 *
          (∑ i ∈ s, (∏ j ∈ s.erase i, q j 1) * D (q i)) +
          (∏ i ∈ s, q i 1) * D (q a) = _
      rw [Finset.sum_insert ha]
      simp only [Finset.erase_insert, ha, not_false_eq_true]
      rw [Finset.mul_sum]
      rw [add_comm]
      apply congrArg (fun z => (∏ j ∈ s, q j 1) * D (q a) + z)
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.erase_insert_of_ne (ne_of_mem_of_not_mem hi ha).symm]
      rw [Finset.prod_insert]
      · ring
      · exact fun hai => ha (Finset.mem_of_mem_erase hai)

omit [IsAlgClosed k] in
private lemma identityPointDerivation_det_at_identity
    {G : Variety k} [AlgebraicGroup G] (D : IdentityPointDerivation G)
    {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I G.PolynomialFunction)
    (hM : ∀ i j, M i j 1 = if i = j then 1 else 0) :
    D M.det = ∑ i, D (M i i) := by
  rw [Matrix.det_apply', map_sum]
  simp_rw [D.leibniz]
  simp only [Derivation.map_intCast]
  have hsmul (f : G.PolynomialFunction) (c : k) :
      f • c = f 1 * c := rfl
  simp_rw [hsmul]
  simp only [mul_zero, add_zero]
  simp_rw [identityPointDerivation_prod D Finset.univ]
  have hcast (z : ℤ) : ((z : G.PolynomialFunction) 1) = (z : k) := by
    exact map_intCast (polynomialFunctionPointAlgHom G 1) z
  simp_rw [hcast, hM]
  rw [Finset.sum_eq_single (1 : Equiv.Perm I)]
  · simp
  · intro σ hσ hne
    suffices (∑ i, (∏ j ∈ Finset.univ.erase i,
        if σ j = j then (1 : k) else 0) * D (M (σ i) i)) = 0 by
      rw [this, mul_zero]
    apply Finset.sum_eq_zero
    intro i hi
    suffices (∏ j ∈ Finset.univ.erase i,
        if σ j = j then (1 : k) else 0) = 0 by
      rw [this, zero_mul]
    have hmoved : ∃ j, j ≠ i ∧ σ j ≠ j := by
      by_contra h
      push Not at h
      have hsupport : σ.support ⊆ {i} := by
        intro j hj
        by_contra hji
        exact (Equiv.Perm.mem_support.mp hj)
          (h j (Finset.notMem_singleton.mp hji))
      have hcard : σ.support.card ≤ 1 := by
        calc
          σ.support.card ≤ ({i} : Finset I).card :=
            Finset.card_le_card hsupport
          _ = 1 := Finset.card_singleton i
      exact hne (Equiv.Perm.card_support_le_one.mp hcard)
    obtain ⟨j, hji, hj⟩ := hmoved
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
    simp [hj]
  · simp

private lemma tangent_trace_zero (m : ℕ)
    (D : IdentityPointDerivation (slVariety k (m + 1))) :
    ∑ i, D (matrixCoordinate (k := k) m i i) = 0 := by
  classical
  let M : Matrix (Fin (m + 1)) (Fin (m + 1))
      (Variety.PolynomialFunction (slVariety k (m + 1))) :=
    fun i j => matrixCoordinate (k := k) m i j
  have hMone (i j : Fin (m + 1)) :
      M i j 1 = if i = j then 1 else 0 := by
    exact matrixCoordinate_one m i j
  rw [← identityPointDerivation_det_at_identity D M hMone]
  have hdet : M.det = 1 := by
    apply Variety.PolynomialFunction.ext
    intro x
    let ev := polynomialFunctionPointAlgHom (slVariety k (m + 1)) x
    change ev M.det = 1
    rw [AlgHom.map_det]
    rw [show ev.mapMatrix M = slPointMatrix (m + 1) x by
      ext i j
      exact matrixCoordinate_apply m i j x]
    exact slPoint_det_eq_one (m + 1) x
  rw [hdet, D.map_one_eq_zero]

private lemma entryExponent_eq_rootCoordinate (m : ℕ)
    (i : Fin (m + 1)) (q : Fin m) :
    (typeASLDiagonalEntryExponent m i q : ℝ) =
      basisVector i q.castSucc - basisVector i (Fin.last m) := by
  induction i using Fin.lastCases with
  | last => simp [typeASLDiagonalEntryExponent, basisVector]
  | cast i =>
      simp [typeASLDiagonalEntryExponent, basisVector, Pi.single_apply]

private lemma rootExponent_injective (m : ℕ) :
    Function.Injective (fun r : TypeARootIndex m =>
      typeASLDiagonalEntryExponent m r.1.2 -
        typeASLDiagonalEntryExponent m r.1.1) := by
  intro r s hrs
  apply (typeARootEmbedding m).injective
  let c : ℝ :=
    typeARootEmbedding m r (Fin.last m) -
      typeARootEmbedding m s (Fin.last m)
  have hcast (q : Fin m) :
      typeARootEmbedding m r q.castSucc -
          typeARootEmbedding m s q.castSucc = c := by
    have hq := congrFun hrs q
    change typeASLDiagonalEntryExponent m r.1.2 q -
        typeASLDiagonalEntryExponent m r.1.1 q =
      typeASLDiagonalEntryExponent m s.1.2 q -
        typeASLDiagonalEntryExponent m s.1.1 q at hq
    have hrj := entryExponent_eq_rootCoordinate m r.1.2 q
    have hri := entryExponent_eq_rootCoordinate m r.1.1 q
    have hsj := entryExponent_eq_rootCoordinate m s.1.2 q
    have hsi := entryExponent_eq_rootCoordinate m s.1.1 q
    have hqreal := congrArg (fun z : ℤ => (z : ℝ)) hq
    norm_num at hqreal
    rw [hrj, hri, hsj, hsi] at hqreal
    change (basisVector r.1.1 - basisVector r.1.2) q.castSucc -
        (basisVector s.1.1 - basisVector s.1.2) q.castSucc =
      (basisVector r.1.1 - basisVector r.1.2) (Fin.last m) -
        (basisVector s.1.1 - basisVector s.1.2) (Fin.last m)
    simp only [Pi.sub_apply]
    linarith
  have hconst (i : Fin (m + 1)) :
      typeARootEmbedding m r i - typeARootEmbedding m s i = c := by
    refine Fin.lastCases ?_ (fun q => hcast q) i
    rfl
  have hsum (t : TypeARootIndex m) :
      ∑ i, typeARootEmbedding m t i = 0 := by
    simp [typeARootEmbedding_apply, basisVector, Pi.single_apply]
  have hzero : (∑ i : Fin (m + 1), c) = 0 := by
    calc
      (∑ i : Fin (m + 1), c) =
          ∑ i, (typeARootEmbedding m r i - typeARootEmbedding m s i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hconst i).symm
      _ = 0 := by rw [Finset.sum_sub_distrib, hsum, hsum, sub_zero]
  have hc : c = 0 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (by positivity)
  funext i
  exact sub_eq_zero.mp ((hconst i).trans hc)

/-- Distinct ordered coordinate pairs give distinct special-linear root
characters. -/
public theorem typeASLRootWeight_injective (m : ℕ) :
    Function.Injective (typeASLRootWeight (k := k) m) := by
  intro r s hrs
  apply rootExponent_injective m
  apply (typeASLDiagonalCharacterAddEquiv (k := k) m).injective
  rw [typeASLDiagonalCharacterAddEquiv_apply,
    typeASLDiagonalCharacterAddEquiv_apply]
  exact congrArg Additive.ofMul hrs

omit [IsAlgClosed k] in
private lemma pointCharacter_inv
    {T : Variety k} [AlgebraicGroup T]
    (chi : TorusCharacter T) (s : Variety.Point T) :
    (chi⁻¹).pointCharacter s = (chi.pointCharacter s)⁻¹ := by
  change ((dPointEquiv 1 ((chi.onPoints s)⁻¹) 0 : k)) =
    ((dPointEquiv 1 (chi.onPoints s) 0 : k))⁻¹
  have hmul := congrFun
    (dPointEquiv_mul 1 (chi.onPoints s)⁻¹ (chi.onPoints s)) 0
  rw [inv_mul_cancel, dPointEquiv_one] at hmul
  simp only [Pi.one_apply, Pi.mul_apply] at hmul
  have hu : dPointEquiv 1 ((chi.onPoints s)⁻¹) 0 =
      (dPointEquiv 1 (chi.onPoints s) 0)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    exact hmul.symm
  simpa using congrArg Units.val hu

omit [IsAlgClosed k] in
private lemma pointCharacter_mul
    {T : Variety k} [AlgebraicGroup T]
    (chi psi : TorusCharacter T) (s : Variety.Point T) :
    (chi * psi).pointCharacter s =
      chi.pointCharacter s * psi.pointCharacter s := by
  change (dPointEquiv 1 (chi.onPoints s * psi.onPoints s) 0 : k) = _
  rw [dPointEquiv_mul]
  rfl

/-- Evaluation of a type-A root weight on the diagonal torus is the quotient
of the corresponding diagonal entries. -/
public theorem typeASLRootWeight_pointCharacter
    (m : ℕ) (r : TypeARootIndex m) :
    letI := (typeASLTorus (k := k) m).carrierAlgebraicGroup
    ∀ s : Variety.Point (typeASLTorus (k := k) m).carrierVariety,
      (typeASLRootWeight (k := k) m r).pointCharacter s =
        (typeASLDiagonalEntryCharacter (k := k) m r.1.2).pointCharacter s *
          ((typeASLDiagonalEntryCharacter (k := k) m r.1.1).pointCharacter s)⁻¹ := by
  letI := (typeASLTorus (k := k) m).carrierAlgebraicGroup
  intro s
  rw [typeASLRootWeight_eq_entryCharacters, pointCharacter_mul,
    pointCharacter_inv]

private lemma typeASLRootWeight_inv (m : ℕ) (r : TypeARootIndex m) :
    (typeASLRootWeight (k := k) m r)⁻¹ =
      typeASLDiagonalEntryCharacter (k := k) m r.1.1 *
        (typeASLDiagonalEntryCharacter (k := k) m r.1.2)⁻¹ := by
  apply Additive.ofMul.injective
  simp [typeASLRootWeight, typeASLDiagonalEntryCharacter,
    ← typeASLDiagonalCharacterAddEquiv_apply, sub_eq_add_neg]

/-- A nonzero identity tangent of nontrivial inverse weight for the diagonal
torus of `SL_(m+1)` is supported on a unique off-diagonal matrix coordinate,
and its character is the corresponding type-A root weight. -/
public theorem typeASLTangentWeight_eq_rootWeight (m : ℕ)
    {chi : TorusWeight (typeASLTorus (k := k) m)}
    {D : IdentityPointDerivation (slVariety k (m + 1))}
    (hchi : chi ≠ 1)
    (hD : IsWeightVector (identityTangentRepresentation (slVariety k (m + 1)))
      (typeASLTorus (k := k) m) D chi⁻¹) :
    ∃! r : TypeARootIndex m, chi = typeASLRootWeight (k := k) m r := by
  letI := (typeASLTorus (k := k) m).carrierAlgebraicGroup
  obtain ⟨a, b, hab⟩ := exists_matrixCoordinate_ne_zero m D hD.1
  have hcharInv : chi⁻¹ =
      typeASLDiagonalEntryCharacter (k := k) m a *
        (typeASLDiagonalEntryCharacter (k := k) m b)⁻¹ := by
    apply TorusCharacter.pointCharacter_injective
    ext s
    let z : Fin (m + 1) → kˣ := fun i =>
      dPointEquiv 1
        ((typeASLDiagonalEntryCharacter (k := k) m i).onPoints s) 0
    have hdiag : slPointMatrix (m + 1)
        ((typeASLTorus (k := k) m).includePoint s) =
        Matrix.diagonal (fun i => (z i : k)) := by
      simpa [z] using typeASLDiagonalTorus_includePoint_matrix (k := k) m s
    have heig := congrArg
      (fun E : IdentityPointDerivation (slVariety k (m + 1)) =>
        E (matrixCoordinate (k := k) m a b)) (hD.2 s)
    rw [identityTangentRepresentation_action_apply,
      matrixCoordinate_conjugation m a b _ z hdiag] at heig
    change D.toLinearMap (((z a : k) * (z b : k)⁻¹) •
        matrixCoordinate m a b) =
      (chi⁻¹).pointCharacter s * D (matrixCoordinate m a b) at heig
    rw [D.toLinearMap.map_smul] at heig
    change ((z a : k) * (z b : k)⁻¹) * D (matrixCoordinate m a b) =
      (chi⁻¹).pointCharacter s * D (matrixCoordinate m a b) at heig
    have hpoint : (chi⁻¹).pointCharacter s =
        (z a : k) * (z b : k)⁻¹ := by
      apply (mul_right_cancel₀ hab)
      exact heig.symm
    rw [pointCharacter_mul,
      pointCharacter_inv (typeASLDiagonalEntryCharacter (k := k) m b) s]
    change (chi⁻¹).pointCharacter s = (z a : k) * (z b : k)⁻¹
    exact hpoint
  have hne : a ≠ b := by
    intro heq
    subst b
    have hone : chi⁻¹ = 1 := by simpa using hcharInv
    apply hchi
    simpa using congrArg Inv.inv hone
  let r : TypeARootIndex m := ⟨(a, b), hne⟩
  have hrootInv : (typeASLRootWeight (k := k) m r)⁻¹ =
      typeASLDiagonalEntryCharacter (k := k) m a *
        (typeASLDiagonalEntryCharacter (k := k) m b)⁻¹ := by
    simpa [r] using typeASLRootWeight_inv (k := k) m r
  have hmain : chi = typeASLRootWeight (k := k) m r := by
    apply inv_injective
    exact hcharInv.trans hrootInv.symm
  refine ⟨r, hmain, ?_⟩
  intro s hs
  exact typeASLRootWeight_injective m (hs.symm.trans hmain)

end

end

end Theory.AlgebraicGroup
