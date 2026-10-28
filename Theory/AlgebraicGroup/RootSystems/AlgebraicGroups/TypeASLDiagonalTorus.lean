module

public import Theory.AlgebraicGroup.ClosedSubgroup.Centralizer
public import Theory.AlgebraicGroup.Instance.SL
public import Theory.AlgebraicGroup.Morphism.ClosedEmbedding
public import Theory.AlgebraicGroup.RootSubgroups.Cocharacter
public import Theory.AlgebraicGroup.Tori.Character.Duality
public import Theory.AlgebraicGroup.Tori.Character.Image
public import Theory.AlgebraicGroup.Tori.Character.Tuple

/-!
The standard determinant-one diagonal torus in the type-A special-linear model.

The morphism from `D_m` sends `(a_0, ..., a_{m-1})` to the diagonal
matrix with final entry `(a_0 ... a_{m-1})⁻¹`.  Polynomial inverse
coordinates on `D_m` make this a closed embedding, so its image is a torus.
An SL matrix centralizing the image has zero off-diagonal entries: Laurent
characters separate any two diagonal positions, and the corresponding matrix
entry of the commutation equation is
`(a_i - a_j) g_{ij} = 0`.  Thus the centralizer is the diagonal image itself,
which proves maximality directly.

The final declarations transport Laurent characters and tuple cocharacters
across the explicit `D_m` isomorphism.  Their pairing is the usual integral
dot product.  These coordinates provide the torus input for the concrete SL
root datum.  The construction is the standard diagonal model of type A
(GLS, Part I, Chapter A, Sections 1.9-1.10).
-/

set_option linter.style.haveILetI false

open scoped BigOperators

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public section

@[expose]
noncomputable def typeASLDiagonalEntries (m : Nat)
    (x : Variety.Point (dVariety k m)) : Fin (m + 1) -> kˣ :=
  Fin.lastCases (∏ i, dPointEquiv m x i)⁻¹ (dPointEquiv m x)

omit [IsAlgClosed k] in
lemma typeASLDiagonalEntries_castSucc (m : Nat)
    (x : Variety.Point (dVariety k m)) (i : Fin m) :
    typeASLDiagonalEntries m x i.castSucc = dPointEquiv m x i := by
  simp [typeASLDiagonalEntries]

omit [IsAlgClosed k] in
lemma typeASLDiagonalEntries_last (m : Nat)
    (x : Variety.Point (dVariety k m)) :
    typeASLDiagonalEntries m x (Fin.last m) =
      (∏ i, dPointEquiv m x i)⁻¹ := by
  simp [typeASLDiagonalEntries]

omit [IsAlgClosed k] in
lemma typeASLDiagonalEntries_prod (m : Nat)
    (x : Variety.Point (dVariety k m)) :
    ∏ i, typeASLDiagonalEntries m x i = 1 := by
  rw [Fin.prod_univ_castSucc]
  simp [typeASLDiagonalEntries]

omit [IsAlgClosed k] in
lemma typeASLDiagonalEntries_mul (m : Nat)
    (x y : Variety.Point (dVariety k m)) :
    typeASLDiagonalEntries m (x * y) =
      typeASLDiagonalEntries m x * typeASLDiagonalEntries m y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [typeASLDiagonalEntries, dPointEquiv_mul,
      Finset.prod_mul_distrib, mul_comm]
  · simp [typeASLDiagonalEntries, dPointEquiv_mul]

@[expose]
noncomputable def typeASLDiagonalMatrix (m : Nat)
    (x : Variety.Point (dVariety k m)) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  Matrix.diagonal fun i => (typeASLDiagonalEntries m x i : k)

omit [IsAlgClosed k] in
lemma typeASLDiagonalMatrix_det (m : Nat)
    (x : Variety.Point (dVariety k m)) :
    (typeASLDiagonalMatrix m x).det = 1 := by
  rw [typeASLDiagonalMatrix, Matrix.det_diagonal]
  simpa using congrArg Units.val (typeASLDiagonalEntries_prod m x)

@[expose]
noncomputable def typeASLDiagonalPoint (m : Nat)
    (x : Variety.Point (dVariety k m)) :
    Variety.Point (slVariety k (m + 1)) :=
  (slPointEquiv (m + 1)).symm
    (show Matrix.SpecialLinearGroup (Fin (m + 1)) k from
      ⟨typeASLDiagonalMatrix m x, typeASLDiagonalMatrix_det m x⟩)

lemma typeASLDiagonalPoint_matrix (m : Nat)
    (x : Variety.Point (dVariety k m)) :
    slPointMatrix (m + 1) (typeASLDiagonalPoint m x) =
      typeASLDiagonalMatrix m x := by
  change ((slPointEquiv (m + 1)) (typeASLDiagonalPoint m x)).1 = _
  rw [typeASLDiagonalPoint, Equiv.apply_symm_apply]

noncomputable def typeASLDiagonalEntryPolynomial (m : Nat)
    (i : Fin (m + 1)) : MvPolynomial (dVariety k m).Coordinates k :=
  Fin.lastCases
    (∏ r : Fin m, MvPolynomial.X (Sum.inr (ULift.up r)))
    (fun r => MvPolynomial.X (Sum.inl (ULift.up r))) i

omit [IsAlgClosed k] in
lemma typeASLDiagonalEntryPolynomial_eval (m : Nat)
    (x : Variety.Point (dVariety k m)) (i : Fin (m + 1)) :
    evalPolynomial x.val (typeASLDiagonalEntryPolynomial m i) =
      (typeASLDiagonalEntries m x i : k) := by
  refine Fin.lastCases ?_ (fun i => ?_) i
  ·
    rw [typeASLDiagonalEntries_last]
    simp only [typeASLDiagonalEntryPolynomial, Fin.lastCases_last]
    simp [evalPolynomial]
    calc
      (∏ r, x.val (Sum.inr (ULift.up r))) =
          ∏ r, (dPointEntry m x r)⁻¹ := by
            apply Finset.prod_congr rfl
            intro r hr
            exact (dPoint_entry_inv m x r).symm
      _ = (∏ r, dPointEntry m x r)⁻¹ :=
        by
          rw [Finset.prod_inv_distrib]
      _ = (∏ r, (dPointEquiv m x r : k))⁻¹ := by rfl
  · rw [typeASLDiagonalEntries_castSucc]
    simp [typeASLDiagonalEntryPolynomial, evalPolynomial, dPointEquiv,
      dPointEntry]

@[expose]
noncomputable def typeASLDiagonalMorphism (m : Nat) :
    AlgebraicGroup.Morphism (dVariety k m) (slVariety k (m + 1)) where
  toVariety :=
    { toFun := typeASLDiagonalPoint m
      regular := by
        rintro ⟨⟨i, j⟩⟩
        by_cases hij : i = j
        · subst j
          refine ⟨typeASLDiagonalEntryPolynomial m i, ?_⟩
          intro x
          change slPointMatrix (m + 1) (typeASLDiagonalPoint m x) i i = _
          rw [typeASLDiagonalPoint_matrix, typeASLDiagonalMatrix,
            Matrix.diagonal_apply_eq]
          exact (typeASLDiagonalEntryPolynomial_eval m x i).symm
        · refine ⟨0, ?_⟩
          intro x
          change slPointMatrix (m + 1) (typeASLDiagonalPoint m x) i j = _
          rw [typeASLDiagonalPoint_matrix, typeASLDiagonalMatrix,
            Matrix.diagonal_apply_ne _ hij]
          simp [evalPolynomial] }
  map_one := by
    apply (slPointEquiv (m + 1)).injective
    apply Subtype.ext
    change typeASLDiagonalMatrix m 1 = 1
    ext i j
    by_cases hij : i = j
    · subst j
      rw [typeASLDiagonalMatrix, Matrix.diagonal_apply_eq]
      refine Fin.lastCases ?_ (fun r => ?_) i <;>
        simp [typeASLDiagonalEntries, dPointEquiv_one]
    · simp [typeASLDiagonalMatrix, hij]
  map_mul := by
    intro x y
    apply (slPointEquiv (m + 1)).injective
    apply Subtype.ext
    change typeASLDiagonalMatrix m (x * y) =
      typeASLDiagonalMatrix m x * typeASLDiagonalMatrix m y
    rw [typeASLDiagonalMatrix, typeASLDiagonalMatrix,
      typeASLDiagonalMatrix, Matrix.diagonal_mul_diagonal,
      typeASLDiagonalEntries_mul]
    rfl

lemma typeASLDiagonalMorphism_matrix (m : Nat)
    (x : Variety.Point (dVariety k m)) :
    slPointMatrix (m + 1) ((typeASLDiagonalMorphism m).onPoints x) =
      typeASLDiagonalMatrix m x :=
  typeASLDiagonalPoint_matrix m x

lemma typeASLDiagonalMorphism_injective (m : Nat) :
    Function.Injective (typeASLDiagonalMorphism (k := k) m).onPoints := by
  intro x y hxy
  apply (dPointEquiv m).injective
  funext i
  apply Units.ext
  have hmatrix := congrArg (slPointMatrix (k := k) (m + 1)) hxy
  rw [typeASLDiagonalMorphism_matrix, typeASLDiagonalMorphism_matrix] at hmatrix
  have hentry := congrFun (congrFun hmatrix i.castSucc) i.castSucc
  simpa [typeASLDiagonalMatrix, Matrix.diagonal_apply_eq,
    typeASLDiagonalEntries_castSucc] using hentry

omit [IsAlgClosed k] in
lemma typeASLDiagonalEntries_prod_erase_castSucc (m : Nat)
    (x : Variety.Point (dVariety k m)) (i : Fin m) :
    (∏ j ∈ Finset.univ.erase i.castSucc,
        (typeASLDiagonalEntries m x j : k)) = dPointEntryInv m x i := by
  have hall := typeASLDiagonalEntries_prod m x
  have herase :
      (∏ j ∈ Finset.univ.erase i.castSucc,
          typeASLDiagonalEntries m x j) *
          typeASLDiagonalEntries m x i.castSucc = 1 := by
    rw [Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i.castSucc)]
    exact hall
  have hinv :
      (∏ j ∈ Finset.univ.erase i.castSucc,
          typeASLDiagonalEntries m x j) =
        (typeASLDiagonalEntries m x i.castSucc)⁻¹ :=
    eq_inv_of_mul_eq_one_left herase
  have hval := congrArg Units.val hinv
  calc
    (∏ j ∈ Finset.univ.erase i.castSucc,
        (typeASLDiagonalEntries m x j : k)) =
        ((↑(∏ j ∈ Finset.univ.erase i.castSucc,
          typeASLDiagonalEntries m x j) : k)) := by
            push_cast
            rfl
    _ = (↑((typeASLDiagonalEntries m x i.castSucc)⁻¹) : k) := hval
    _ = dPointEntryInv m x i := by
      rw [typeASLDiagonalEntries_castSucc]
      simp [dPointEquiv]

noncomputable def typeASLDiagonalInverseCoordinatePolynomial (m : Nat)
    (i : Fin m) :
    MvPolynomial (slVariety k (m + 1)).Coordinates k :=
  ∏ j ∈ Finset.univ.erase i.castSucc,
    MvPolynomial.X (ULift.up (j, j))

lemma typeASLDiagonalMorphism_coordinate_preimage (m : Nat)
    (c : (dVariety k m).Coordinates) :
    ∃ q : Variety.PolynomialFunction (slVariety k (m + 1)),
      Variety.PolynomialFunction.pullback
          (typeASLDiagonalMorphism m).toVariety q =
        Variety.PolynomialFunction.ofPolynomial (dVariety k m)
          (MvPolynomial.X c) := by
  cases c with
  | inl i =>
      let q : Variety.PolynomialFunction (slVariety k (m + 1)) :=
        Variety.PolynomialFunction.ofPolynomial _
          (MvPolynomial.X (ULift.up (i.down.castSucc, i.down.castSucc)))
      refine ⟨q, ?_⟩
      apply Variety.PolynomialFunction.ext
      intro x
      change q ((typeASLDiagonalMorphism m).onPoints x) =
        Variety.PolynomialFunction.ofPolynomial (dVariety k m)
          (MvPolynomial.X (Sum.inl i)) x
      dsimp only [q, Variety.PolynomialFunction.ofPolynomial,
        Variety.PolynomialFunction.toFun]
      simp only [evalPolynomial_X]
      change slPointMatrix (m + 1)
          ((typeASLDiagonalMorphism m).onPoints x)
            i.down.castSucc i.down.castSucc = x.val (Sum.inl i)
      rw [typeASLDiagonalMorphism_matrix, typeASLDiagonalMatrix,
        Matrix.diagonal_apply_eq, typeASLDiagonalEntries_castSucc]
      rfl
  | inr i =>
      let q : Variety.PolynomialFunction (slVariety k (m + 1)) :=
        Variety.PolynomialFunction.ofPolynomial _
          (typeASLDiagonalInverseCoordinatePolynomial m i.down)
      refine ⟨q, ?_⟩
      apply Variety.PolynomialFunction.ext
      intro x
      change q ((typeASLDiagonalMorphism m).onPoints x) =
        Variety.PolynomialFunction.ofPolynomial (dVariety k m)
          (MvPolynomial.X (Sum.inr i)) x
      dsimp only [q, Variety.PolynomialFunction.ofPolynomial,
        Variety.PolynomialFunction.toFun]
      simp only [evalPolynomial_X]
      change evalPolynomial
          ((typeASLDiagonalMorphism m).onPoints x).val
            (typeASLDiagonalInverseCoordinatePolynomial m i.down) =
        x.val (Sum.inr i)
      simp only [typeASLDiagonalInverseCoordinatePolynomial,
        evalPolynomial, MvPolynomial.eval₂_prod, MvPolynomial.eval₂_X]
      change (∏ j ∈ Finset.univ.erase i.down.castSucc,
        slPointMatrix (m + 1) ((typeASLDiagonalMorphism m).onPoints x) j j) =
          x.val (Sum.inr i)
      simp_rw [typeASLDiagonalMorphism_matrix, typeASLDiagonalMatrix,
        Matrix.diagonal_apply_eq]
      rw [typeASLDiagonalEntries_prod_erase_castSucc]
      rfl

@[expose]
noncomputable def typeASLDiagonalTorus (m : Nat) :
    ClosedSubgroup (slVariety k (m + 1)) :=
  (typeASLDiagonalMorphism m).imageClosedSubgroup

lemma typeASLDiagonalTorus_mem_iff (m : Nat)
    (g : Variety.Point (slVariety k (m + 1))) :
    g ∈ (typeASLDiagonalTorus m).toSubgroup ↔
      ∃ x : Variety.Point (dVariety k m),
        (typeASLDiagonalMorphism m).onPoints x = g := by
  change g ∈ (typeASLDiagonalMorphism m).imageClosedSubgroup ↔ _
  change g ∈ (typeASLDiagonalMorphism m).image ↔ _
  rfl

lemma typeASLDiagonalTorus_isSubtorus (m : Nat) :
    IsSubtorus (typeASLDiagonalTorus (k := k) m) :=
  morphism_image_isTorus (typeASLDiagonalMorphism m)
    (dVariety_isTorus m)

noncomputable def typeASLDiagonalTorusIso (m : Nat) :
    letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
    AlgebraicGroup.Iso (dVariety k m)
      (typeASLDiagonalTorus m).carrierVariety := by
  letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
  exact Classical.choose
    ((typeASLDiagonalMorphism m).iso_imageClosedSubgroup_of_coordinate_preimage
      (typeASLDiagonalMorphism_injective m)
      (typeASLDiagonalMorphism_coordinate_preimage m))

lemma typeASLDiagonalTorusIso_hom (m : Nat) :
    letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
    (typeASLDiagonalTorusIso (k := k) m).hom =
      (typeASLDiagonalMorphism m).codRestrictClosedSubgroup
        (typeASLDiagonalTorus m) (fun y => ⟨y, rfl⟩) := by
  letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
  exact Classical.choose_spec
    ((typeASLDiagonalMorphism m).iso_imageClosedSubgroup_of_coordinate_preimage
      (typeASLDiagonalMorphism_injective m)
      (typeASLDiagonalMorphism_coordinate_preimage m))

lemma typeASLDiagonalTorusIso_inclusion_hom (m : Nat)
    (x : Variety.Point (dVariety k m)) :
    letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
    (typeASLDiagonalTorus m).inclusion.onPoints
        ((typeASLDiagonalTorusIso m).hom.onPoints x) =
      (typeASLDiagonalMorphism m).onPoints x := by
  letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
  rw [typeASLDiagonalTorusIso_hom]
  exact AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply
    (typeASLDiagonalMorphism m) (typeASLDiagonalTorus m)
      (fun y => show
        (typeASLDiagonalMorphism m).onPoints y ∈
          (typeASLDiagonalTorus m).toSubgroup from ⟨y, rfl⟩) x

lemma typeASLDiagonalTorus_mem_iff_diagonal (m : Nat)
    (g : Variety.Point (slVariety k (m + 1))) :
    g ∈ (typeASLDiagonalTorus m).toSubgroup ↔
      ∀ i j, i ≠ j → slPointMatrix (m + 1) g i j = 0 := by
  constructor
  · rintro ⟨x, rfl⟩ i j hij
    rw [typeASLDiagonalMorphism_matrix, typeASLDiagonalMatrix,
      Matrix.diagonal_apply_ne _ hij]
  · intro hdiag
    let M := slPointMatrix (m + 1) g
    have hM : M = Matrix.diagonal (fun i => M i i) := by
      ext i j
      by_cases hij : i = j
      · subst j
        rw [Matrix.diagonal_apply_eq]
      · rw [Matrix.diagonal_apply_ne _ hij]
        exact hdiag i j hij
    have hprod : ∏ i, M i i = 1 := by
      have hdet := slPoint_det_eq_one (m + 1) g
      change M.det = 1 at hdet
      rw [hM, Matrix.det_diagonal] at hdet
      exact hdet
    have hne (i : Fin (m + 1)) : M i i ≠ 0 := by
      intro hi
      have hz : ∏ j, M j j = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hi
      rw [hprod] at hz
      exact one_ne_zero hz
    let a : Fin m → kˣ := fun i => Units.mk0 (M i.castSucc i.castSucc) (hne i.castSucc)
    let x : Variety.Point (dVariety k m) := (dPointEquiv m).symm a
    rw [typeASLDiagonalTorus_mem_iff]
    refine ⟨x, ?_⟩
    apply (slPointEquiv (m + 1)).injective
    apply Subtype.ext
    change typeASLDiagonalMatrix m x = M
    rw [hM, typeASLDiagonalMatrix]
    congr 1
    funext i
    refine Fin.lastCases ?_ (fun r => ?_) i
    · rw [typeASLDiagonalEntries_last]
      change (↑(∏ r, dPointEquiv m x r)⁻¹ : k) = M (Fin.last m) (Fin.last m)
      have hx : dPointEquiv m x = a := (dPointEquiv m).apply_symm_apply a
      rw [hx]
      rw [Units.val_inv_eq_inv_val]
      push_cast
      dsimp only [a]
      change (∏ r : Fin m, M r.castSucc r.castSucc)⁻¹ =
        M (Fin.last m) (Fin.last m)
      rw [Fin.prod_univ_castSucc] at hprod
      exact inv_eq_of_mul_eq_one_right hprod
    · rw [typeASLDiagonalEntries_castSucc]
      rw [(dPointEquiv m).apply_symm_apply a]
      rfl

@[expose]
noncomputable def typeASLDiagonalEntryExponent (m : Nat) :
    Fin (m + 1) → Fin m → ℤ :=
  Fin.lastCases (fun _ => -1) (fun i => Pi.single i 1)

lemma typeASLDiagonalEntryExponent_injective (m : Nat) :
    Function.Injective (typeASLDiagonalEntryExponent m) := by
  classical
  intro i j hij
  induction i using Fin.lastCases with
  | last =>
      induction j using Fin.lastCases with
      | last => rfl
      | cast s =>
          have h := congrFun hij s
          simp [typeASLDiagonalEntryExponent] at h
  | cast r =>
      induction j using Fin.lastCases with
      | last =>
          have h := congrFun hij r
          simp [typeASLDiagonalEntryExponent] at h
      | cast s =>
          congr 1
          by_contra hrs
          have h := congrFun hij r
          simp [typeASLDiagonalEntryExponent, hrs] at h

omit [IsAlgClosed k] in
lemma typeASLDiagonalEntryExponent_apply (m : Nat)
    (x : Variety.Point (dVariety k m)) (i : Fin (m + 1)) :
    dPointEquiv 1
        ((dLaurentCharacter m (typeASLDiagonalEntryExponent m i)).onPoints x) 0 =
      typeASLDiagonalEntries m x i := by
  classical
  refine Fin.lastCases ?_ (fun r => ?_) i
  · rw [typeASLDiagonalEntries_last, dLaurentCharacter_apply]
    simp [typeASLDiagonalEntryExponent, Finset.prod_inv_distrib]
  · rw [typeASLDiagonalEntries_castSucc, dLaurentCharacter_apply]
    simp [typeASLDiagonalEntryExponent, Pi.single_apply]

lemma typeASLDiagonalEntries_separate (m : Nat)
    {i j : Fin (m + 1)} (hij : i ≠ j) :
    ∃ x : Variety.Point (dVariety k m),
      typeASLDiagonalEntries m x i ≠ typeASLDiagonalEntries m x j := by
  classical
  by_contra hnone
  push Not at hnone
  have hchars :
      dLaurentCharacter (k := k) m (typeASLDiagonalEntryExponent m i) =
        dLaurentCharacter m (typeASLDiagonalEntryExponent m j) := by
    apply AlgebraicGroup.Morphism.ext
    funext x
    apply (dPointEquiv 1).injective
    funext q
    have hq : q = 0 := Subsingleton.elim _ _
    subst q
    exact (typeASLDiagonalEntryExponent_apply m x i).trans
      ((hnone x).trans (typeASLDiagonalEntryExponent_apply m x j).symm)
  have hexp := dLaurentCharacter_injective (k := k) m hchars
  exact hij (typeASLDiagonalEntryExponent_injective m hexp)

theorem typeASLDiagonalTorus_centralizer_eq (m : Nat) :
    (typeASLDiagonalTorus (k := k) m).centralizer =
      typeASLDiagonalTorus m := by
  apply SetLike.coe_injective
  ext g
  constructor
  · intro hg
    apply (typeASLDiagonalTorus_mem_iff_diagonal m g).mpr
    intro i j hij
    obtain ⟨x, hx⟩ := typeASLDiagonalEntries_separate (k := k) m hij
    have hfx : (typeASLDiagonalMorphism m).onPoints x ∈
        (typeASLDiagonalTorus m).toSubgroup := ⟨x, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hg _ hfx
    have hentry := congrArg
      (fun z : Variety.Point (slVariety k (m + 1)) =>
        slPointMatrix (m + 1) z i j) hcomm
    change (typeASLDiagonalMatrix m x * slPointMatrix (m + 1) g) i j =
      (slPointMatrix (m + 1) g * typeASLDiagonalMatrix m x) i j at hentry
    rw [typeASLDiagonalMatrix, Matrix.diagonal_mul,
      Matrix.mul_diagonal] at hentry
    have hx' : (typeASLDiagonalEntries m x i : k) ≠
        (typeASLDiagonalEntries m x j : k) := by
      exact_mod_cast hx
    have hfactor :
        ((typeASLDiagonalEntries m x i : k) -
            (typeASLDiagonalEntries m x j : k)) *
          slPointMatrix (m + 1) g i j = 0 := by
      rw [sub_mul, mul_comm (typeASLDiagonalEntries m x j : k)]
      exact sub_eq_zero.mpr hentry
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hx')
  · intro hg
    change g ∈ Subgroup.centralizer
      ((typeASLDiagonalTorus (k := k) m).toSubgroup :
        Set (Variety.Point (slVariety k (m + 1))))
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    let T := typeASLDiagonalTorus (k := k) m
    letI := T.carrierAlgebraicGroup
    let gt : Variety.Point T.carrierVariety :=
      T.pointEquiv.symm ⟨g, hg⟩
    let tt : Variety.Point T.carrierVariety :=
      T.pointEquiv.symm ⟨t, ht⟩
    have hcomm := typeASLDiagonalTorus_isSubtorus (k := k) m |>.isMulCommutative
    rw [isMulCommutative_iff] at hcomm
    have hamb := congrArg T.inclusion.onPoints (hcomm tt gt)
    have htt : T.inclusion.onPoints tt = t := by
      change (T.pointEquiv tt).val = t
      dsimp only [tt]
      rw [T.pointEquiv.apply_symm_apply]
    have hgt : T.inclusion.onPoints gt = g := by
      change (T.pointEquiv gt).val = g
      dsimp only [gt]
      rw [T.pointEquiv.apply_symm_apply]
    simpa only [map_mul, htt, hgt] using hamb

theorem typeASLDiagonalTorus_isMaximalTorus (m : Nat) :
    IsMaximalTorus (typeASLDiagonalTorus (k := k) m) := by
  refine ⟨typeASLDiagonalTorus_isSubtorus m, ?_⟩
  intro S hS hTS
  apply SetLike.coe_injective
  apply Set.Subset.antisymm
  · intro g hg
    have hgcentral : g ∈ Subgroup.centralizer
        ((typeASLDiagonalTorus (k := k) m).toSubgroup :
          Set (Variety.Point (slVariety k (m + 1)))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      letI := S.carrierAlgebraicGroup
      let gs : Variety.Point S.carrierVariety :=
        S.pointEquiv.symm ⟨g, hg⟩
      let ts : Variety.Point S.carrierVariety :=
        S.pointEquiv.symm ⟨t, hTS ht⟩
      have hcomm := hS.isMulCommutative
      rw [isMulCommutative_iff] at hcomm
      have hamb := congrArg S.inclusion.onPoints (hcomm ts gs)
      have hts : S.inclusion.onPoints ts = t := by
        change (S.pointEquiv ts).val = t
        dsimp only [ts]
        rw [S.pointEquiv.apply_symm_apply]
      have hgs : S.inclusion.onPoints gs = g := by
        change (S.pointEquiv gs).val = g
        dsimp only [gs]
        rw [S.pointEquiv.apply_symm_apply]
      simpa only [map_mul, hts, hgs] using hamb
    have hgclosed : g ∈
        Theory.AlgebraicGroup.ClosedSubgroup.centralizer
          (typeASLDiagonalTorus (k := k) m) := hgcentral
    rw [typeASLDiagonalTorus_centralizer_eq] at hgclosed
    exact hgclosed
  · exact hTS

@[expose]
noncomputable def typeASLDiagonalTorusPointEquiv (m : Nat) :
    letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
    Variety.Point (typeASLDiagonalTorus (k := k) m).carrierVariety ≃*
      Variety.Point (dVariety k m) := by
  letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
  exact (typeASLDiagonalTorusIso (k := k) m).toMulEquiv.symm

lemma typeASLDiagonalTorusPointEquiv_symm_inclusion (m : Nat)
    (x : Variety.Point (dVariety k m)) :
    letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
    (typeASLDiagonalTorus (k := k) m).inclusion.onPoints
        ((typeASLDiagonalTorusPointEquiv (k := k) m).symm x) =
      (typeASLDiagonalMorphism (k := k) m).onPoints x := by
  letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
  exact typeASLDiagonalTorusIso_inclusion_hom (k := k) m x

@[expose]
noncomputable def typeASLDiagonalCharacterTransport (m : Nat) :
    letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
    TorusCharacter (dVariety k m) ≃*
      TorusWeight (typeASLDiagonalTorus (k := k) m) := by
  letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
  let e := typeASLDiagonalTorusIso (k := k) m
  exact
    { toFun := TorusCharacter.pullback e.inv
      invFun := TorusCharacter.pullback e.hom
      left_inv := by
        intro chi
        apply AlgebraicGroup.Morphism.ext
        funext x
        change chi.onPoints (e.inv.onPoints (e.hom.onPoints x)) =
          chi.onPoints x
        rw [e.hom_inv_id]
      right_inv := by
        intro chi
        apply AlgebraicGroup.Morphism.ext
        funext x
        change chi.onPoints (e.hom.onPoints (e.inv.onPoints x)) =
          chi.onPoints x
        rw [e.inv_hom_id]
      map_mul' := (TorusCharacter.pullback e.inv).map_mul }

@[expose]
noncomputable def typeASLDiagonalCharacter (m : Nat) (z : Fin m → ℤ) :
    letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
    TorusWeight (typeASLDiagonalTorus (k := k) m) := by
  letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
  exact typeASLDiagonalCharacterTransport (k := k) m
    (dLaurentCharacter (k := k) m z)

lemma typeASLDiagonalCharacter_apply (m : Nat) (z : Fin m → ℤ)
    (x : Variety.Point (dVariety k m)) :
    letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
    dPointEquiv 1
        ((typeASLDiagonalCharacter (k := k) m z).onPoints
          ((typeASLDiagonalTorusIso (k := k) m).hom.onPoints x)) 0 =
      ∏ i, (dPointEquiv m x i) ^ z i := by
  letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
  change dPointEquiv 1
      ((dLaurentCharacter (k := k) m z).onPoints
        ((typeASLDiagonalTorusIso (k := k) m).inv.onPoints
          ((typeASLDiagonalTorusIso (k := k) m).hom.onPoints x))) 0 = _
  rw [(typeASLDiagonalTorusIso (k := k) m).hom_inv_id,
    dLaurentCharacter_apply]

@[expose]
noncomputable def typeASLDiagonalEntryCharacter (m : Nat)
    (i : Fin (m + 1)) :
    letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
    TorusWeight (typeASLDiagonalTorus (k := k) m) :=
  typeASLDiagonalCharacter (k := k) m (typeASLDiagonalEntryExponent m i)

lemma typeASLDiagonalEntryCharacter_apply (m : Nat)
    (i : Fin (m + 1)) (x : Variety.Point (dVariety k m)) :
    letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
    dPointEquiv 1
        ((typeASLDiagonalEntryCharacter (k := k) m i).onPoints
          ((typeASLDiagonalTorusIso (k := k) m).hom.onPoints x)) 0 =
      typeASLDiagonalEntries m x i := by
  letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
  change dPointEquiv 1
      ((dLaurentCharacter (k := k) m (typeASLDiagonalEntryExponent m i)).onPoints
        ((typeASLDiagonalTorusIso (k := k) m).inv.onPoints
          ((typeASLDiagonalTorusIso (k := k) m).hom.onPoints x))) 0 = _
  rw [(typeASLDiagonalTorusIso (k := k) m).hom_inv_id]
  exact typeASLDiagonalEntryExponent_apply (k := k) m x i

lemma typeASLDiagonalEntryCharacter_apply_point (m : Nat)
    (i : Fin (m + 1))
    (s : Variety.Point (typeASLDiagonalTorus (k := k) m).carrierVariety) :
    letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
    dPointEquiv 1
        ((typeASLDiagonalEntryCharacter (k := k) m i).onPoints s) 0 =
      typeASLDiagonalEntries m
        (typeASLDiagonalTorusPointEquiv (k := k) m s) i := by
  letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
  let x := typeASLDiagonalTorusPointEquiv (k := k) m s
  have hx : (typeASLDiagonalTorusIso (k := k) m).hom.onPoints x = s := by
    change (typeASLDiagonalTorusIso (k := k) m).hom.onPoints
        ((typeASLDiagonalTorusIso (k := k) m).inv.onPoints s) = s
    rw [(typeASLDiagonalTorusIso (k := k) m).inv_hom_id]
  have h := typeASLDiagonalEntryCharacter_apply (k := k) m i x
  rw [hx] at h
  exact h

theorem typeASLDiagonalTorus_includePoint_matrix (m : Nat)
    (s : Variety.Point (typeASLDiagonalTorus (k := k) m).carrierVariety) :
    letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
    slPointMatrix (m + 1)
        ((typeASLDiagonalTorus (k := k) m).includePoint s) =
      Matrix.diagonal (fun i =>
        (dPointEquiv 1
          ((typeASLDiagonalEntryCharacter (k := k) m i).onPoints s) 0 : k)) := by
  letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
  let x := typeASLDiagonalTorusPointEquiv (k := k) m s
  have hx : (typeASLDiagonalTorusIso (k := k) m).hom.onPoints x = s := by
    change (typeASLDiagonalTorusIso (k := k) m).hom.onPoints
        ((typeASLDiagonalTorusIso (k := k) m).inv.onPoints s) = s
    rw [(typeASLDiagonalTorusIso (k := k) m).inv_hom_id]
  have hinclusion := typeASLDiagonalTorusIso_inclusion_hom (k := k) m x
  rw [hx] at hinclusion
  have hmatrix := congrArg (slPointMatrix (k := k) (m + 1)) hinclusion
  rw [typeASLDiagonalMorphism_matrix, typeASLDiagonalMatrix] at hmatrix
  have hinclude :
      (typeASLDiagonalTorus (k := k) m).includePoint s =
        (typeASLDiagonalTorus (k := k) m).inclusion.onPoints s := by
    apply Variety.Point.ext
    funext j
    rfl
  rw [hinclude, hmatrix]
  congr 1
  funext i
  exact congrArg Units.val
    (typeASLDiagonalEntryCharacter_apply_point (k := k) m i s).symm

@[expose]
noncomputable def typeASLDiagonalCharacterAddEquiv (m : Nat) :
    letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
    (Fin m → ℤ) ≃+
      Additive (TorusWeight (typeASLDiagonalTorus (k := k) m)) := by
  letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
  exact (dLaurentCharacterAddEquiv (k := k) m).trans
    (typeASLDiagonalCharacterTransport (k := k) m).toAdditive

lemma typeASLDiagonalCharacterAddEquiv_apply (m : Nat) (z : Fin m → ℤ) :
    letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
    typeASLDiagonalCharacterAddEquiv (k := k) m z =
      Additive.ofMul (typeASLDiagonalCharacter (k := k) m z) := by
  letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
  rfl

@[expose]
noncomputable def typeASLDiagonalCocharacter (m : Nat) (z : Fin m → ℤ) :
    letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
    ClosedSubgroupTorusCocharacter (typeASLDiagonalTorus (k := k) m) := by
  letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
  exact (typeASLDiagonalTorusIso (k := k) m).hom.comp
    (dCharacterTupleMorphism (k := k) m 1 (fun i _ => z i))

lemma typeASLDiagonalCocharacter_inclusion_apply (m : Nat) (z : Fin m → ℤ)
    (t : Variety.Point (KMult k)) :
    letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
    (typeASLDiagonalTorus (k := k) m).inclusion.onPoints
        ((typeASLDiagonalCocharacter (k := k) m z).onPoints t) =
      (typeASLDiagonalMorphism (k := k) m).onPoints
        ((dCharacterTupleMorphism (k := k) m 1 (fun i _ => z i)).onPoints t) := by
  letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
  exact typeASLDiagonalTorusIso_inclusion_hom (k := k) m
    ((dCharacterTupleMorphism (k := k) m 1 (fun i _ => z i)).onPoints t)

theorem typeASLDiagonalCharacter_cocharacter_pairing
    (m : Nat) (z w : Fin m → ℤ) :
    letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
    WeightCocharacterEquation (typeASLDiagonalTorus (k := k) m)
      (typeASLDiagonalCharacter (k := k) m z)
      (typeASLDiagonalCocharacter (k := k) m w)
      (∑ i, z i * w i) := by
  letI := (typeASLDiagonalTorus (k := k) m).carrierAlgebraicGroup
  intro t
  change (dLaurentCharacter (k := k) m z).pointCharacter
      ((typeASLDiagonalTorusIso (k := k) m).inv.onPoints
        ((typeASLDiagonalTorusIso (k := k) m).hom.onPoints
          ((dCharacterTupleMorphism (k := k) m 1
            (fun i _ => w i)).onPoints t))) = _
  rw [(typeASLDiagonalTorusIso (k := k) m).hom_inv_id]
  rw [TorusCharacter.pointCharacter_dLaurentCharacter]
  change (↑(∏ i,
      (dPointEquiv m
        ((dCharacterTupleMorphism (k := k) m 1
          (fun i _ => w i)).onPoints t) i) ^ z i) : k) = _
  simp_rw [dCharacterTupleMorphism_apply]
  rw [prod_laurentMonomial_zpow]
  simp

end

end Theory.AlgebraicGroup
