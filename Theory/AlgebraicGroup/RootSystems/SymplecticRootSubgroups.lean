module

public import Theory.AlgebraicGroup.RootSystems.SymplecticAlgebraicQuotient
public import Theory.AlgebraicGroup.Morphism.ClosedEmbedding
public import Theory.AlgebraicGroup.RootSubgroups.Defs
public import Theory.AlgebraicGroup.Tori.Character.Tuple
public import Theory.AlgebraicGroup.Tori.Character.Operations
import all Theory.AlgebraicGroup.RootSystems.SymplecticClosedSubgroup

/-!
# Explicit root curves in the standard symplectic carrier

This module begins the concrete type-C root family.  The indexed matrices are
the elementary symplectic transvections: the pair indices give the four
weights `±e_i ± e_j`, while the long indices give `±2e_i`.  We expose the
matrix formulas and their additive and symplectic identities first; the
algebraic one-parameter images and diagonal-torus formulas below use these
identities directly.

A distinguished off-diagonal entry recovers the curve parameter.  The
coordinate-preimage closed-image theorem therefore identifies each polynomial
curve with a closed one-parameter subgroup.  Transpose realizes root
opposition, the standard root-vector equivalence supplies reflection indices,
and an entrywise diagonal calculation gives the Laurent monomial by which
inverse torus conjugation scales each parameter.

The construction follows the standard block-matrix realization of the
symplectic group (GLS, Part I, Chapter A, Sections 1.9-1.10).
-/

universe u

open scoped BigOperators

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

open StandardRootSystem

variable {k : Type u} [Field k] [IsAlgClosed k]

public abbrev symplecticSingle (m : ℕ) (i j : Fin m) (a : k) :
    Matrix (Fin m) (Fin m) k := Matrix.single i j a

omit [IsAlgClosed k] in
@[simp]
private lemma single_mul_self_zero (m : ℕ) (i j : Fin m) (hij : i ≠ j) (a b : k) :
    symplecticSingle (k := k) m i j a * symplecticSingle m i j b = 0 := by
  exact Matrix.single_mul_single_of_ne a i j i hij.symm b

omit [IsAlgClosed k] in
@[simp]
private lemma one_add_single_mul_one_sub_single
    (m : ℕ) (i j : Fin m) (hij : i ≠ j) (a : k) :
    (1 + symplecticSingle (k := k) m i j a) * (1 - symplecticSingle m i j a) = 1 := by
  simp [add_mul, mul_sub, single_mul_self_zero m i j hij]

omit [IsAlgClosed k] in
@[simp]
private lemma one_add_single_mul_one_add_single
    (m : ℕ) (i j : Fin m) (hij : i ≠ j) (a b : k) :
    (1 + symplecticSingle (k := k) m i j a) * (1 + symplecticSingle m i j b) =
      1 + symplecticSingle m i j (a + b) := by
  rw [add_mul, mul_add, mul_one, one_mul]
  rw [mul_add, mul_one, single_mul_self_zero m i j hij]
  simp only [add_zero]
  change 1 + Matrix.single i j b + Matrix.single i j a =
    1 + Matrix.single i j (a + b)
  rw [Matrix.single_add]
  abel

omit [IsAlgClosed k] in
@[simp]
private lemma one_sub_single_mul_one_sub_single
    (m : ℕ) (i j : Fin m) (hij : i ≠ j) (a b : k) :
    (1 - symplecticSingle (k := k) m i j a) * (1 - symplecticSingle m i j b) =
      1 - symplecticSingle m i j (a + b) := by
  simp [sub_eq_add_neg, add_mul, mul_add, single_mul_self_zero m i j hij,
    Matrix.single_add]
  abel

private lemma transpose_fromBlocks
    {a b c d : Type*} {R : Type*}
    (A : Matrix a c R) (B : Matrix a d R)
    (C : Matrix b c R) (D : Matrix b d R) :
    (Matrix.fromBlocks A B C D).transpose =
      Matrix.fromBlocks A.transpose C.transpose B.transpose D.transpose := by
  ext (i | i) (j | j) <;> rfl

@[expose]
public noncomputable def symplecticRootMatrix (m : ℕ) : TypeCRootIndex m → k →
    Matrix (symplecticStandardIndex m) (symplecticStandardIndex m) k
  | .inl ⟨⟨⟨i, j⟩, _⟩, s, t⟩, a =>
      if s.1 = 1 then
        if t.1 = 1 then
          Matrix.fromBlocks 1 (symplecticSingle m i j a + symplecticSingle m j i a) 0 1
        else
          Matrix.fromBlocks (1 + symplecticSingle m i j a) 0 0 (1 - symplecticSingle m j i a)
      else
        if t.1 = 1 then
          Matrix.fromBlocks (1 + symplecticSingle m j i a) 0 0 (1 - symplecticSingle m i j a)
        else
          Matrix.fromBlocks 1 0 (symplecticSingle m i j a + symplecticSingle m j i a) 1
  | .inr ⟨i, false⟩, a =>
      Matrix.fromBlocks 1 (symplecticSingle m i i a) 0 1
  | .inr ⟨i, true⟩, a =>
      Matrix.fromBlocks 1 0 (symplecticSingle m i i a) 1

omit [IsAlgClosed k] in
public lemma symplecticRootMatrix_mem (m : ℕ) (r : TypeCRootIndex m) (a : k) :
    symplecticRootMatrix (k := k) m r a ∈ Matrix.symplecticGroup (Fin m) k := by
  rcases r with r | ⟨i, b⟩
  · rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
    by_cases hs : s.1 = 1 <;> by_cases ht : t.1 = 1
    all_goals
      simp only [symplecticRootMatrix, hs, ht, if_true, if_false]
      rw [SymplecticGroup.fromBlocks_mem_iff]
    · refine ⟨by simp, ?_, by simp⟩
      simp [symplecticSingle, Matrix.transpose_add, Matrix.transpose_single]
      abel
    · refine ⟨by simp, by simp, ?_⟩
      simpa [symplecticSingle, Matrix.transpose_add, Matrix.transpose_single] using
        one_add_single_mul_one_sub_single (k := k) m j i hij.ne' a
    · refine ⟨by simp, by simp, ?_⟩
      simpa [symplecticSingle, Matrix.transpose_add, Matrix.transpose_single] using
        one_add_single_mul_one_sub_single (k := k) m i j hij.ne a
    · refine ⟨?_, by simp, by simp⟩
      simp [symplecticSingle, Matrix.transpose_add, Matrix.transpose_single]
      abel
  · cases b <;> simp only [symplecticRootMatrix] <;>
      rw [SymplecticGroup.fromBlocks_mem_iff] <;>
      simp [symplecticSingle, Matrix.transpose_single]

omit [IsAlgClosed k] in
public lemma symplecticRootMatrix_zero (m : ℕ) (r : TypeCRootIndex m) :
    symplecticRootMatrix (k := k) m r 0 = 1 := by
  rcases r with r | ⟨i, b⟩
  · rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
    by_cases hs : s.1 = 1 <;> by_cases ht : t.1 = 1
    all_goals simp [symplecticRootMatrix, hs, ht, symplecticSingle, Matrix.fromBlocks_one]
  · cases b <;> simp [symplecticRootMatrix, symplecticSingle, Matrix.fromBlocks_one]

omit [IsAlgClosed k] in
public lemma symplecticRootMatrix_add (m : ℕ) (r : TypeCRootIndex m) (a b : k) :
    symplecticRootMatrix (k := k) m r (a + b) =
      symplecticRootMatrix (k := k) m r a * symplecticRootMatrix (k := k) m r b := by
  rcases r with r | ⟨i, q⟩
  · rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
    by_cases hs : s.1 = 1 <;> by_cases ht : t.1 = 1
    all_goals
      simp only [symplecticRootMatrix, hs, ht, if_true, if_false,
        Matrix.fromBlocks_multiply]
      rw [Matrix.fromBlocks_inj]
    · simp [symplecticSingle, Matrix.single_add]
      abel
    · refine ⟨?_, by simp, by simp, ?_⟩
      · simpa using (one_add_single_mul_one_add_single (k := k) m i j hij.ne a b).symm
      · simpa using (one_sub_single_mul_one_sub_single (k := k) m j i hij.ne' a b).symm
    · refine ⟨?_, by simp, by simp, ?_⟩
      · simpa using (one_add_single_mul_one_add_single (k := k) m j i hij.ne' a b).symm
      · simpa using (one_sub_single_mul_one_sub_single (k := k) m i j hij.ne a b).symm
    · simp [symplecticSingle, Matrix.single_add]
      abel
  · cases q <;>
      simp [symplecticRootMatrix, symplecticSingle, Matrix.fromBlocks_multiply,
        Matrix.single_add]
    all_goals abel

@[expose]
public noncomputable def symplecticRootNeg (m : ℕ) : TypeCRootIndex m → TypeCRootIndex m
  | .inl ⟨ij, s, t⟩ => .inl ⟨ij, ⟨-s.1, by rcases s.2 with hs | hs <;> simp_all⟩,
      ⟨-t.1, by rcases t.2 with ht | ht <;> simp_all⟩⟩
  | .inr ⟨i, b⟩ => .inr ⟨i, !b⟩

public lemma symplecticRootNeg_involutive (m : ℕ) (r : TypeCRootIndex m) :
    symplecticRootNeg m (symplecticRootNeg m r) = r := by
  rcases r with ⟨ij, s, t⟩ | ⟨i, b⟩
  · apply congrArg Sum.inl
    apply Prod.ext
    · rfl
    apply Prod.ext <;> apply Subtype.ext <;> simp
  · cases b <;> rfl

public lemma symplecticRootNeg_vector (m : ℕ) (r : TypeCRootIndex m) :
    typeCRootVector m (symplecticRootNeg m r) = -typeCRootVector m r := by
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩ | ⟨i, b⟩
  · simp [symplecticRootNeg, typeCRootVector]
    module
  · cases b <;> simp [symplecticRootNeg, typeCRootVector]

omit [IsAlgClosed k] in
public lemma symplecticRootMatrix_neg_transpose (m : ℕ) (r : TypeCRootIndex m) (a : k) :
    symplecticRootMatrix (k := k) m (symplecticRootNeg m r) a =
      (symplecticRootMatrix (k := k) m r a).transpose := by
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩ | ⟨i, b⟩
  · rcases s with ⟨s, rfl | rfl⟩ <;> rcases t with ⟨t, rfl | rfl⟩ <;>
      norm_num [symplecticRootNeg, symplecticRootMatrix] <;>
      simp [transpose_fromBlocks, Matrix.transpose_single] <;>
      abel
  · cases b <;>
      simp [symplecticRootNeg, symplecticRootMatrix, transpose_fromBlocks,
        Matrix.transpose_single]

@[expose]
public noncomputable def symplecticRootReflect
    (m : ℕ) (r s : TypeCRootIndex m) : TypeCRootIndex m :=
  (typeCRootPairing m).reflectionPerm r s

public lemma symplecticRootReflect_root (m : ℕ) (r s : TypeCRootIndex m) :
    (typeCRootPairing m).root (symplecticRootReflect m r s) =
      (typeCRootPairing m).root s -
        (typeCRootPairing m).pairing s r • (typeCRootPairing m).root r := by
  rw [symplecticRootReflect, (typeCRootPairing m).root_reflectionPerm,
    (typeCRootPairing m).reflection_apply_root]

omit [IsAlgClosed k] in
public lemma symplecticRootMatrix_affine (m : ℕ) (r : TypeCRootIndex m) (a : k) :
    symplecticRootMatrix (k := k) m r a =
      1 + a • (symplecticRootMatrix (k := k) m r 1 - 1) := by
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩ | ⟨i, b⟩
  · by_cases hs : s.1 = 1 <;> by_cases ht : t.1 = 1 <;>
      ext (p | p) (q | q) <;>
      simp [symplecticRootMatrix, hs, ht, symplecticSingle,
        Matrix.one_apply, Matrix.single_apply] <;>
      split_ifs <;> ring
  · cases b <;>
      ext (p | p) (q | q) <;>
      simp [symplecticRootMatrix, symplecticSingle,
        Matrix.one_apply, Matrix.single_apply]

@[expose]
public noncomputable def symplecticRootFinMatrix (m : ℕ) (r : TypeCRootIndex m) (a : k) :
    Matrix (Fin (Module.finrank k (symplecticStandardSpace (k := k) m)))
      (Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) k :=
  Matrix.reindexAlgEquiv k k (symplecticStandardIndexEquiv (k := k) m)
    (symplecticRootMatrix m r a)

omit [IsAlgClosed k] in
public lemma symplecticRootFinMatrix_det (m : ℕ) (r : TypeCRootIndex m) (a : k) :
    (symplecticRootFinMatrix (k := k) m r a).det = 1 := by
  rw [symplecticRootFinMatrix, Matrix.coe_reindexAlgEquiv,
    Matrix.det_reindex_self]
  exact SymplecticGroup.det_eq_one (symplecticRootMatrix_mem m r a)

@[expose]
public noncomputable def symplecticRootGL (m : ℕ) (r : TypeCRootIndex m) (a : k) :
    GL (Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (symplecticRootFinMatrix m r a)
    (by rw [symplecticRootFinMatrix_det]; exact one_ne_zero)

@[expose]
public noncomputable def symplecticRootAmbientPoint (m : ℕ) (r : TypeCRootIndex m) (a : k) :
    Variety.Point (glVarietyOf k (symplecticStandardSpace (k := k) m)) :=
  (glPointEquiv (Module.finrank k (symplecticStandardSpace (k := k) m))).symm
    (symplecticRootGL m r a)

@[simp]
public lemma symplecticRootAmbientPoint_val (m : ℕ) (r : TypeCRootIndex m) (a : k)
    (p q : symplecticStandardIndex m) :
    (symplecticRootAmbientPoint m r a).val
        (Sum.inl (symplecticStandardIndexEquiv (k := k) m p,
          symplecticStandardIndexEquiv (k := k) m q)) =
      symplecticRootMatrix (k := k) m r a p q := by
  simp [symplecticRootAmbientPoint, symplecticRootGL, glPointEquiv,
    symplecticRootFinMatrix, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]

@[simp]
public lemma symplecticRootAmbientPoint_scalar (m : ℕ) (r : TypeCRootIndex m) (a : k) :
    (symplecticRootAmbientPoint m r a).val (Sum.inr PUnit.unit) = 1 := by
  simp [symplecticRootAmbientPoint, symplecticRootGL, glPointEquiv,
    symplecticRootFinMatrix_det]

omit [IsAlgClosed k] in
private lemma pi_repr_standardSymplecticBasis_symm
    (m : ℕ)
    (c : Fin (Module.finrank k (symplecticStandardSpace (k := k) m)) → k)
    (p : symplecticStandardIndex m) :
    (Pi.basisFun k (symplecticStandardIndex m)).repr
        ((symplecticStandardBasis (k := k) m).equivFun.symm c) p =
      c (symplecticStandardIndexEquiv (k := k) m p) := by
  calc
    (Pi.basisFun k (symplecticStandardIndex m)).repr
        ((symplecticStandardBasis (k := k) m).equivFun.symm c) p =
        (symplecticStandardBasis (k := k) m).equivFun.symm c p := by
          rw [Pi.basisFun_repr]
    _ = (symplecticStandardBasis (k := k) m).repr
        ((symplecticStandardBasis (k := k) m).equivFun.symm c)
          (symplecticStandardIndexEquiv (k := k) m p) :=
      (symplecticStandardBasis_repr_apply (k := k) m _ p).symm
    _ = c (symplecticStandardIndexEquiv (k := k) m p) :=
      congrFun ((symplecticStandardBasis (k := k) m).equivFun.apply_symm_apply c)
        (symplecticStandardIndexEquiv (k := k) m p)

public lemma symplecticRootAmbientPoint_symplecticMatrix
    (m : ℕ) (r : TypeCRootIndex m) (a : k) :
    symplecticMatrix (k := k) m
        (LinearMap.GeneralLinearGroup.generalLinearEquiv k
          (symplecticStandardSpace (k := k) m)
          (glPointEquivOf k (symplecticStandardSpace (k := k) m)
            (symplecticStandardBasis (k := k) m)
            (symplecticRootAmbientPoint m r a))) =
      symplecticRootMatrix (k := k) m r a := by
  ext p q
  rw [symplecticMatrix, LinearMap.toMatrix_apply]
  change (Pi.basisFun k (symplecticStandardIndex m)).repr
      ((glPointEquivOf k (symplecticStandardSpace (k := k) m)
        (symplecticStandardBasis (k := k) m)
        (symplecticRootAmbientPoint m r a)).1
          ((Pi.basisFun k (symplecticStandardIndex m)) q)) p = _
  rw [Pi.basisFun_apply,
    ← symplecticStandardBasis_apply (k := k) m q]
  rw [glPointEquivOf_apply_basis]
  rw [pi_repr_standardSymplecticBasis_symm]
  change (symplecticRootAmbientPoint m r a).val
      (Sum.inl (symplecticStandardIndexEquiv (k := k) m p,
        symplecticStandardIndexEquiv (k := k) m q)) = _
  exact symplecticRootAmbientPoint_val m r a p q

public lemma symplecticRootAmbientPoint_mem (m : ℕ) (r : TypeCRootIndex m) (a : k) :
    symplecticRootAmbientPoint (k := k) m r a ∈
      (standardSymplecticClosedSubgroup (k := k) m).toSubgroup := by
  rw [standardSymplecticClosedSubgroup_carrier]
  rw [mem_bilinearIsometrySubgroup_iff_symplecticMatrix]
  rw [symplecticRootAmbientPoint_symplecticMatrix]
  exact symplecticRootMatrix_mem m r a

@[expose]
public noncomputable def symplecticRootPoint (m : ℕ) (r : TypeCRootIndex m) (a : k) :
    Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety :=
  (standardSymplecticClosedSubgroup (k := k) m).pointEquiv.symm
    ⟨symplecticRootAmbientPoint m r a, symplecticRootAmbientPoint_mem m r a⟩

@[simp]
public lemma symplecticRootPoint_val (m : ℕ) (r : TypeCRootIndex m) (a : k)
    (p q : symplecticStandardIndex m) :
    (symplecticRootPoint m r a).val
        (Sum.inl (symplecticStandardIndexEquiv (k := k) m p,
          symplecticStandardIndexEquiv (k := k) m q)) =
      symplecticRootMatrix (k := k) m r a p q := by
  rw [← (standardSymplecticClosedSubgroup (k := k) m).pointEquiv_val
    (symplecticRootPoint m r a)]
  rw [symplecticRootPoint,
    (standardSymplecticClosedSubgroup (k := k) m).pointEquiv.apply_symm_apply]
  exact symplecticRootAmbientPoint_val m r a p q

@[expose]
public noncomputable def symplecticRootCoordinate (m : ℕ) :
    TypeCRootIndex m → symplecticStandardIndex m × symplecticStandardIndex m
  | .inl ⟨⟨⟨i, j⟩, _⟩, s, t⟩ =>
      if s.1 = 1 then
        if t.1 = 1 then (Sum.inl i, Sum.inr j)
        else (Sum.inl i, Sum.inl j)
      else
        if t.1 = 1 then (Sum.inl j, Sum.inl i)
        else (Sum.inr i, Sum.inl j)
  | .inr ⟨i, false⟩ => (Sum.inl i, Sum.inr i)
  | .inr ⟨i, true⟩ => (Sum.inr i, Sum.inl i)

omit [IsAlgClosed k] in
@[simp]
public lemma symplecticRootMatrix_coordinate (m : ℕ) (r : TypeCRootIndex m) (a : k) :
    symplecticRootMatrix (k := k) m r a
        (symplecticRootCoordinate m r).1 (symplecticRootCoordinate m r).2 = a := by
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩ | ⟨i, b⟩
  · by_cases hs : s.1 = 1 <;> by_cases ht : t.1 = 1 <;>
      simp [symplecticRootCoordinate, symplecticRootMatrix, hs, ht,
        symplecticSingle, hij.ne, hij.ne']
  · cases b <;> simp [symplecticRootCoordinate, symplecticRootMatrix, symplecticSingle]

omit [IsAlgClosed k] in
public lemma symplecticRootFinMatrix_zero (m : ℕ) (r : TypeCRootIndex m) :
    symplecticRootFinMatrix (k := k) m r 0 = 1 := by
  rw [symplecticRootFinMatrix, symplecticRootMatrix_zero, map_one]

omit [IsAlgClosed k] in
public lemma symplecticRootFinMatrix_add (m : ℕ) (r : TypeCRootIndex m) (a b : k) :
    symplecticRootFinMatrix (k := k) m r (a + b) =
      symplecticRootFinMatrix (k := k) m r a * symplecticRootFinMatrix (k := k) m r b := by
  simp only [symplecticRootFinMatrix, symplecticRootMatrix_add, map_mul]

omit [IsAlgClosed k] in
public lemma symplecticRootGL_zero (m : ℕ) (r : TypeCRootIndex m) :
    symplecticRootGL (k := k) m r 0 = 1 := by
  apply Units.ext
  exact symplecticRootFinMatrix_zero m r

omit [IsAlgClosed k] in
public lemma symplecticRootGL_add (m : ℕ) (r : TypeCRootIndex m) (a b : k) :
    symplecticRootGL (k := k) m r (a + b) =
      symplecticRootGL (k := k) m r a * symplecticRootGL (k := k) m r b := by
  apply Units.ext
  exact symplecticRootFinMatrix_add m r a b

public lemma symplecticRootAmbientPoint_zero (m : ℕ) (r : TypeCRootIndex m) :
    symplecticRootAmbientPoint (k := k) m r 0 = 1 := by
  let e : Variety.Point (glVarietyOf k (symplecticStandardSpace (k := k) m)) ≃*
      GL (Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) k := by
    exact translationGLPointMulEquiv
      (k := k) (Module.finrank k (symplecticStandardSpace (k := k) m))
  calc
    symplecticRootAmbientPoint (k := k) m r 0 = e.symm (symplecticRootGL m r 0) := rfl
    _ = e.symm 1 := congrArg _ (symplecticRootGL_zero m r)
    _ = 1 := map_one _

public lemma symplecticRootAmbientPoint_add (m : ℕ) (r : TypeCRootIndex m) (a b : k) :
    symplecticRootAmbientPoint (k := k) m r (a + b) =
      symplecticRootAmbientPoint (k := k) m r a * symplecticRootAmbientPoint m r b := by
  let e : Variety.Point (glVarietyOf k (symplecticStandardSpace (k := k) m)) ≃*
      GL (Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) k := by
    exact translationGLPointMulEquiv
      (k := k) (Module.finrank k (symplecticStandardSpace (k := k) m))
  calc
    symplecticRootAmbientPoint (k := k) m r (a + b) = e.symm (symplecticRootGL m r (a + b)) := rfl
    _ = e.symm (symplecticRootGL m r a * symplecticRootGL m r b) :=
      congrArg _ (symplecticRootGL_add m r a b)
    _ = e.symm (symplecticRootGL m r a) * e.symm (symplecticRootGL m r b) := map_mul _ _ _
    _ = symplecticRootAmbientPoint m r a * symplecticRootAmbientPoint m r b := rfl

@[simp]
public lemma symplecticRootPoint_include (m : ℕ) (r : TypeCRootIndex m) (a : k) :
    (standardSymplecticClosedSubgroup (k := k) m).includePoint
        (symplecticRootPoint m r a) = symplecticRootAmbientPoint m r a := by
  change ((standardSymplecticClosedSubgroup (k := k) m).pointEquiv
    (symplecticRootPoint m r a)).val = _
  rw [symplecticRootPoint,
    (standardSymplecticClosedSubgroup (k := k) m).pointEquiv.apply_symm_apply]

@[simp]
public lemma symplecticRootPoint_zero (m : ℕ) (r : TypeCRootIndex m) :
    symplecticRootPoint (k := k) m r 0 = 1 := by
  apply (standardSymplecticClosedSubgroup (k := k) m).inclusion_injective
  change (standardSymplecticClosedSubgroup (k := k) m).includePoint
      (symplecticRootPoint m r 0) =
    (standardSymplecticClosedSubgroup (k := k) m).includePoint 1
  rw [symplecticRootPoint_include, symplecticRootAmbientPoint_zero]
  exact (standardSymplecticClosedSubgroup (k := k) m).inclusion.map_one.symm

public lemma symplecticRootPoint_add (m : ℕ) (r : TypeCRootIndex m) (a b : k) :
    symplecticRootPoint (k := k) m r (a + b) =
      symplecticRootPoint (k := k) m r a * symplecticRootPoint (k := k) m r b := by
  apply (standardSymplecticClosedSubgroup (k := k) m).inclusion_injective
  change (standardSymplecticClosedSubgroup (k := k) m).includePoint
      (symplecticRootPoint m r (a + b)) =
    (standardSymplecticClosedSubgroup (k := k) m).includePoint
      (symplecticRootPoint m r a * symplecticRootPoint m r b)
  calc
    (standardSymplecticClosedSubgroup (k := k) m).includePoint
        (symplecticRootPoint m r (a + b)) =
        symplecticRootAmbientPoint m r (a + b) := symplecticRootPoint_include m r (a + b)
    _ = symplecticRootAmbientPoint m r a * symplecticRootAmbientPoint m r b :=
      symplecticRootAmbientPoint_add m r a b
    _ = (standardSymplecticClosedSubgroup (k := k) m).includePoint
        (symplecticRootPoint m r a) *
          (standardSymplecticClosedSubgroup (k := k) m).includePoint
            (symplecticRootPoint m r b) := by
      rw [symplecticRootPoint_include, symplecticRootPoint_include]
    _ = (standardSymplecticClosedSubgroup (k := k) m).includePoint
        (symplecticRootPoint m r a * symplecticRootPoint m r b) :=
      ((standardSymplecticClosedSubgroup (k := k) m).inclusion.map_mul _ _).symm

@[simp]
public lemma symplecticRootPoint_scalar (m : ℕ) (r : TypeCRootIndex m) (a : k) :
    (symplecticRootPoint m r a).val (Sum.inr PUnit.unit) = 1 := by
  rw [← (standardSymplecticClosedSubgroup (k := k) m).pointEquiv_val
    (symplecticRootPoint m r a)]
  rw [symplecticRootPoint,
    (standardSymplecticClosedSubgroup (k := k) m).pointEquiv.apply_symm_apply]
  exact symplecticRootAmbientPoint_scalar m r a

@[expose]
public noncomputable def symplecticRootMorphism (m : ℕ) (r : TypeCRootIndex m) :
    AlgebraicGroup.Morphism (KPlus k)
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety where
  toVariety :=
    { toFun := fun x => symplecticRootPoint m r (x.val PUnit.unit)
      regular := by
        rintro (⟨i, j⟩ | PUnit.unit)
        · let e := symplecticStandardIndexEquiv (k := k) m
          let p := e.symm i
          let q := e.symm j
          refine ⟨MvPolynomial.C ((1 : Matrix (symplecticStandardIndex m)
              (symplecticStandardIndex m) k) p q) +
              MvPolynomial.X PUnit.unit *
                MvPolynomial.C ((symplecticRootMatrix (k := k) m r 1 - 1) p q), ?_⟩
          intro x
          rw [← e.apply_symm_apply i, ← e.apply_symm_apply j]
          rw [symplecticRootPoint_val, symplecticRootMatrix_affine]
          simp [evalPolynomial]
          rfl
        · refine ⟨1, ?_⟩
          intro x
          rw [symplecticRootPoint_scalar]
          simp [evalPolynomial] }
  map_one := by
    change symplecticRootPoint m r ((1 : Variety.Point (KPlus k)).val PUnit.unit) = 1
    have hcoord : ((1 : Variety.Point (KPlus k)).val PUnit.unit) = 0 := by
      rw [← kPlusPoint_coordinate (k := k) (1 : Variety.Point (KPlus k))]
      rfl
    rw [hcoord, symplecticRootPoint_zero]
  map_mul := by
    intro x y
    change symplecticRootPoint m r ((x * y).val PUnit.unit) =
      symplecticRootPoint m r (x.val PUnit.unit) * symplecticRootPoint m r (y.val PUnit.unit)
    rw [kPlusPoint_coordinate_mul, symplecticRootPoint_add]

@[simp]
public lemma symplecticRootMorphism_apply (m : ℕ) (r : TypeCRootIndex m)
    (x : Variety.Point (KPlus k)) :
    (symplecticRootMorphism m r).onPoints x =
      symplecticRootPoint m r (x.val PUnit.unit) := by rfl

@[simp]
public lemma symplecticRootMorphism_kPlusPoint (m : ℕ) (r : TypeCRootIndex m) (a : k) :
    (symplecticRootMorphism m r).onPoints (kPlusPoint a) = symplecticRootPoint m r a := by rfl

public lemma symplecticRootMorphism_injective (m : ℕ) (r : TypeCRootIndex m) :
    Function.Injective (symplecticRootMorphism (k := k) m r).onPoints := by
  intro x y hxy
  apply (additiveGroupPointEquiv k).injective
  change x.val PUnit.unit = y.val PUnit.unit
  have hentry := congrArg
    (fun z : Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety =>
      z.val (Sum.inl
        (symplecticStandardIndexEquiv (k := k) m (symplecticRootCoordinate m r).1,
          symplecticStandardIndexEquiv (k := k) m (symplecticRootCoordinate m r).2))) hxy
  simpa only [symplecticRootMorphism_apply, symplecticRootPoint_val,
    symplecticRootMatrix_coordinate] using hentry

public lemma symplecticRootMorphism_coordinate_preimage (m : ℕ) (r : TypeCRootIndex m) :
    ∀ c : (KPlus k).Coordinates,
      ∃ q : Variety.PolynomialFunction
          (standardSymplecticClosedSubgroup (k := k) m).carrierVariety,
        Variety.PolynomialFunction.pullback (symplecticRootMorphism m r).toVariety q =
          Variety.PolynomialFunction.ofPolynomial (KPlus k) (MvPolynomial.X c) := by
  intro c
  let qcoord :
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety.Coordinates :=
    Sum.inl
      (symplecticStandardIndexEquiv (k := k) m (symplecticRootCoordinate m r).1,
        symplecticStandardIndexEquiv (k := k) m (symplecticRootCoordinate m r).2)
  refine ⟨Variety.PolynomialFunction.ofPolynomial
    (standardSymplecticClosedSubgroup (k := k) m).carrierVariety
      (MvPolynomial.X qcoord), ?_⟩
  apply Variety.PolynomialFunction.ext
  intro x
  simp only [Variety.PolynomialFunction.pullback,
    Variety.PolynomialFunction.ofPolynomial,
    Variety.PolynomialFunction.toFun]
  change evalPolynomial ((symplecticRootMorphism m r).toVariety.toFun x).val
      (MvPolynomial.X qcoord) = evalPolynomial x.val (MvPolynomial.X c)
  rw [evalPolynomial_X, evalPolynomial_X]
  change ((symplecticRootMorphism m r).onPoints x).val (Sum.inl
        (symplecticStandardIndexEquiv (k := k) m (symplecticRootCoordinate m r).1,
          symplecticStandardIndexEquiv (k := k) m (symplecticRootCoordinate m r).2)) = x.val c
  rw [symplecticRootMorphism_apply, symplecticRootPoint_val, symplecticRootMatrix_coordinate]

@[expose]
public noncomputable def symplecticRootSubgroup (m : ℕ) (r : TypeCRootIndex m) :
    ClosedSubgroup (standardSymplecticClosedSubgroup (k := k) m).carrierVariety :=
  (symplecticRootMorphism m r).imageClosedSubgroup

public noncomputable def symplecticRootParametrization (m : ℕ) (r : TypeCRootIndex m) :
    @OneParameterParametrization k _
      (symplecticRootSubgroup (k := k) m r).carrierVariety
      (symplecticRootSubgroup (k := k) m r).carrierAlgebraicGroup :=
  Classical.choose ((symplecticRootMorphism m r).iso_imageClosedSubgroup_of_coordinate_preimage
    (symplecticRootMorphism_injective m r)
    (symplecticRootMorphism_coordinate_preimage m r))

public lemma symplecticRootSubgroup_isOneParameter (m : ℕ) (r : TypeCRootIndex m) :
    @IsOneParameterGroup k _
      (symplecticRootSubgroup (k := k) m r).carrierVariety
      (symplecticRootSubgroup (k := k) m r).carrierAlgebraicGroup :=
  ⟨symplecticRootParametrization m r⟩

public lemma symplecticRootParametrization_hom (m : ℕ) (r : TypeCRootIndex m) :
    @AlgebraicGroup.Iso.hom k _ (KPlus k)
        (symplecticRootSubgroup (k := k) m r).carrierVariety
        (inferInstance : AlgebraicGroup (KPlus k))
        (symplecticRootSubgroup (k := k) m r).carrierAlgebraicGroup
        (symplecticRootParametrization (k := k) m r) =
      (symplecticRootMorphism m r).codRestrictClosedSubgroup
        (symplecticRootSubgroup (k := k) m r) (fun y => ⟨y, rfl⟩) :=
  Classical.choose_spec
    ((symplecticRootMorphism m r).iso_imageClosedSubgroup_of_coordinate_preimage
      (symplecticRootMorphism_injective m r)
      (symplecticRootMorphism_coordinate_preimage m r))

public lemma symplecticRootParametrization_include_value
    (m : ℕ) (r : TypeCRootIndex m) (a : k) :
    (symplecticRootSubgroup (k := k) m r).includePoint
        (@OneParameterParametrization.value k _
          (symplecticRootSubgroup (k := k) m r).carrierVariety
          (symplecticRootSubgroup (k := k) m r).carrierAlgebraicGroup
          (symplecticRootParametrization m r) a) =
      symplecticRootPoint m r a := by
  let _ : AlgebraicGroup (symplecticRootSubgroup (k := k) m r).carrierVariety :=
    (symplecticRootSubgroup (k := k) m r).carrierAlgebraicGroup
  change (symplecticRootSubgroup (k := k) m r).inclusion.onPoints
      ((@AlgebraicGroup.Iso.hom k _ (KPlus k)
          (symplecticRootSubgroup (k := k) m r).carrierVariety
          (inferInstance : AlgebraicGroup (KPlus k))
          (symplecticRootSubgroup (k := k) m r).carrierAlgebraicGroup
          (symplecticRootParametrization m r)).onPoints (kPlusPoint a)) = _
  rw [symplecticRootParametrization_hom]
  exact (symplecticRootMorphism m r).codRestrictClosedSubgroup_inclusion_apply
    (symplecticRootSubgroup (k := k) m r) (fun y => ⟨y, rfl⟩) (kPlusPoint a)

/-! The paired diagonal entries and their determinant-one matrix are the
coordinate layer for the standard symplectic torus.  The carrier morphism and
character transport are assembled in the dependent torus module.
-/

@[expose]
public noncomputable def symplecticDiagonalEntries (m : ℕ)
    (x : Variety.Point (dVariety k m)) : symplecticStandardIndex m → kˣ
  | .inl i => dPointEquiv m x i
  | .inr i => (dPointEquiv m x i)⁻¹

omit [IsAlgClosed k] in
public lemma symplecticDiagonalEntries_mul (m : ℕ)
    (x y : Variety.Point (dVariety k m)) :
    symplecticDiagonalEntries (k := k) m (x * y) =
      symplecticDiagonalEntries m x * symplecticDiagonalEntries m y := by
  funext p
  cases p with
  | inl i => simp [symplecticDiagonalEntries, dPointEquiv_mul]
  | inr i => simp [symplecticDiagonalEntries, dPointEquiv_mul, mul_comm]

omit [IsAlgClosed k] in
public lemma symplecticDiagonalEntries_prod (m : ℕ)
    (x : Variety.Point (dVariety k m)) :
    ∏ p : symplecticStandardIndex m, symplecticDiagonalEntries (k := k) m x p = 1 := by
  rw [Fintype.prod_sum_type]
  simp [symplecticDiagonalEntries, Finset.prod_inv_distrib]

@[expose]
public noncomputable def symplecticDiagonalValue (m : ℕ) (z : Fin m → kˣ) :
    symplecticStandardIndex m → k
  | .inl i => z i
  | .inr i => (z i : k)⁻¹

omit [IsAlgClosed k] in
public lemma symplecticDiagonalValue_point (m : ℕ)
    (x : Variety.Point (dVariety k m)) (p : symplecticStandardIndex m) :
    symplecticDiagonalValue (k := k) m (dPointEquiv m x) p =
      (symplecticDiagonalEntries m x p : k) := by
  cases p <;> simp [symplecticDiagonalValue, symplecticDiagonalEntries]

@[expose]
public noncomputable def symplecticDiagonalMatrix (m : ℕ)
    (x : Variety.Point (dVariety k m)) :
    Matrix (symplecticStandardIndex m) (symplecticStandardIndex m) k :=
  Matrix.diagonal (symplecticDiagonalValue m (dPointEquiv m x))

omit [IsAlgClosed k] in
public lemma symplecticDiagonalMatrix_det (m : ℕ)
    (x : Variety.Point (dVariety k m)) :
    (symplecticDiagonalMatrix (k := k) m x).det = 1 := by
  rw [symplecticDiagonalMatrix, Matrix.det_diagonal]
  rw [Fintype.prod_sum_type]
  simp only [symplecticDiagonalValue, Finset.prod_inv_distrib]
  exact mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr fun i _ =>
    Units.ne_zero (dPointEquiv m x i))

omit [IsAlgClosed k] in
public noncomputable def symplecticRootScaleValue (m : ℕ) :
    TypeCRootIndex m → (Fin m → kˣ) → k
  | .inl ⟨⟨⟨i, j⟩, _⟩, s, t⟩, z =>
      if s.1 = 1 then
        if t.1 = 1 then
          ((z i : k)⁻¹) * (z j : k)⁻¹
        else ((z i : k)⁻¹) * z j
      else
        if t.1 = 1 then
          (z i : k) * (z j : k)⁻¹
        else (z i : k) * z j
  | .inr ⟨i, false⟩, z => ((z i : k)⁻¹) * (z i : k)⁻¹
  | .inr ⟨i, true⟩, z => (z i : k) * z i

@[expose]
public noncomputable def symplecticRootScale (m : ℕ) (r : TypeCRootIndex m)
    (x : Variety.Point (dVariety k m)) : k :=
  symplecticRootScaleValue m r (dPointEquiv m x)

omit [IsAlgClosed k] in
public lemma symplecticRootScale_ne_zero (m : ℕ) (r : TypeCRootIndex m)
    (x : Variety.Point (dVariety k m)) :
    symplecticRootScale (k := k) m r x ≠ 0 := by
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩ | ⟨i, b⟩
  · by_cases hs : s.1 = 1 <;> by_cases ht : t.1 = 1 <;>
      simp [symplecticRootScale, symplecticRootScaleValue, hs, ht]
  · cases b <;> simp [symplecticRootScale, symplecticRootScaleValue]

omit [IsAlgClosed k] in
public lemma symplecticRootScale_neg (m : ℕ) (r : TypeCRootIndex m)
    (x : Variety.Point (dVariety k m)) :
    symplecticRootScale (k := k) m (symplecticRootNeg m r) x =
      (symplecticRootScale (k := k) m r x)⁻¹ := by
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩ | ⟨i, b⟩
  · rcases s with ⟨s, rfl | rfl⟩ <;> rcases t with ⟨t, rfl | rfl⟩ <;>
      norm_num [symplecticRootNeg, symplecticRootScale, symplecticRootScaleValue] <;>
      field_simp
  · cases b with
    | false =>
        simp [symplecticRootNeg, symplecticRootScale, symplecticRootScaleValue]
    | true =>
        simp [symplecticRootNeg, symplecticRootScale, symplecticRootScaleValue]

set_option maxRecDepth 16384 in
omit [IsAlgClosed k] in
public lemma symplecticRootMatrix_mul_diagonalValue
    (m : ℕ) (r : TypeCRootIndex m) (a : k) (z : Fin m → kˣ) :
    symplecticRootMatrix (k := k) m r a *
        Matrix.diagonal (symplecticDiagonalValue m z) =
      Matrix.diagonal (symplecticDiagonalValue m z) *
        symplecticRootMatrix (k := k) m r (symplecticRootScaleValue m r z * a) := by
  have hz (i : Fin m) : (z i : k) ≠ 0 := Units.ne_zero (z i)
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩ | ⟨i, b⟩
  · by_cases hs : s.1 = 1 <;> by_cases ht : t.1 = 1 <;>
      ext (p | p) (q | q) <;>
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul] <;>
      simp [symplecticRootMatrix, symplecticRootScaleValue, symplecticDiagonalValue,
        hs, ht, symplecticSingle, Matrix.one_apply, Matrix.single_apply] <;>
      split_ifs
    all_goals
      (try simp only [*]) <;>
        try { field_simp [hz] <;> ring }
  · cases b <;>
      ext (p | p) (q | q) <;>
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul] <;>
      simp [symplecticRootMatrix, symplecticRootScaleValue, symplecticDiagonalValue,
        symplecticSingle, Matrix.one_apply, Matrix.single_apply] <;>
      split_ifs
    all_goals
      (try simp only [*]) <;>
        try { field_simp [hz]; ring }
    all_goals
      rcases ‹_ ∧ _› with ⟨rfl, rfl⟩
      field_simp [hz]

omit [IsAlgClosed k] in
public lemma symplecticRootMatrix_mul_diagonal
    (m : ℕ) (r : TypeCRootIndex m) (a : k)
    (x : Variety.Point (dVariety k m)) :
    symplecticRootMatrix (k := k) m r a * symplecticDiagonalMatrix m x =
      symplecticDiagonalMatrix m x *
        symplecticRootMatrix (k := k) m r (symplecticRootScale m r x * a) := by
  simpa only [symplecticDiagonalMatrix, symplecticRootScale] using
    symplecticRootMatrix_mul_diagonalValue (k := k) m r a (dPointEquiv m x)

@[expose]
public noncomputable def symplecticClosedPointMatrix (m : ℕ)
    (x : Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety) :
    Matrix (symplecticStandardIndex m) (symplecticStandardIndex m) k :=
  symplecticMatrix m (standardSymplecticClosedSubgroupPoints m x).1

@[simp]
public lemma symplecticClosedPointMatrix_entry (m : ℕ)
    (x : Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety)
    (p q : symplecticStandardIndex m) :
    symplecticClosedPointMatrix m x p q =
      x.val (Sum.inl (symplecticStandardIndexEquiv (k := k) m p,
        symplecticStandardIndexEquiv (k := k) m q)) := by
  rw [symplecticClosedPointMatrix]
  rw [← standardSymplecticClosedSubgroup_linear_points m x]
  rw [symplecticMatrix, LinearMap.toMatrix_apply]
  change (Pi.basisFun k (symplecticStandardIndex m)).repr
      ((glPointEquivOf k (symplecticStandardSpace (k := k) m)
        (symplecticStandardBasis (k := k) m)
        ((standardSymplecticClosedSubgroup (k := k) m).inclusion.onPoints x)).1
          ((Pi.basisFun k (symplecticStandardIndex m)) q)) p = _
  rw [Pi.basisFun_apply, ← symplecticStandardBasis_apply (k := k) m q,
    glPointEquivOf_apply_basis, pi_repr_standardSymplecticBasis_symm]
  rfl

@[simp]
public lemma symplecticClosedPointMatrix_rootPoint
    (m : ℕ) (r : TypeCRootIndex m) (a : k) :
    symplecticClosedPointMatrix m (symplecticRootPoint m r a) =
      symplecticRootMatrix m r a := by
  rw [symplecticClosedPointMatrix]
  rw [← standardSymplecticClosedSubgroup_linear_points m (symplecticRootPoint m r a)]
  rw [show (standardSymplecticClosedSubgroup (k := k) m).inclusion.onPoints
      (symplecticRootPoint m r a) = symplecticRootAmbientPoint m r a by
    exact symplecticRootPoint_include m r a]
  exact symplecticRootAmbientPoint_symplecticMatrix m r a

public lemma symplecticClosedPointMatrix_mul (m : ℕ)
    (x y : Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety) :
    symplecticClosedPointMatrix m (x * y) =
      symplecticClosedPointMatrix m x * symplecticClosedPointMatrix m y := by
  simp only [symplecticClosedPointMatrix, map_mul]
  exact LinearMap.toMatrix_mul (Pi.basisFun k (symplecticStandardIndex m)) _ _

public lemma symplecticClosedPointMatrix_injective (m : ℕ) :
    Function.Injective (symplecticClosedPointMatrix (k := k) m) := by
  intro x y hxy
  apply (standardSymplecticClosedSubgroupPoints (k := k) m).injective
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (LinearMap.toMatrix (Pi.basisFun k (symplecticStandardIndex m))
    (Pi.basisFun k (symplecticStandardIndex m))).injective
  exact hxy

public lemma symplecticRootPoint_neg_matrix
    (m : ℕ) (r : TypeCRootIndex m) (a : k) :
    symplecticClosedPointMatrix m (symplecticRootPoint m (symplecticRootNeg m r) a) =
      (symplecticClosedPointMatrix m (symplecticRootPoint m r a)).transpose := by
  rw [symplecticClosedPointMatrix_rootPoint, symplecticClosedPointMatrix_rootPoint,
    symplecticRootMatrix_neg_transpose]

public theorem symplecticRootPoint_diagonal_conjugation
    (m : ℕ) (r : TypeCRootIndex m) (a : k)
    (d : Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety)
    (x : Variety.Point (dVariety k m))
    (hd : symplecticClosedPointMatrix m d = symplecticDiagonalMatrix m x) :
    d⁻¹ * symplecticRootPoint m r a * d =
      symplecticRootPoint m r (symplecticRootScale m r x * a) := by
  have hcomm : symplecticRootPoint m r a * d =
      d * symplecticRootPoint m r (symplecticRootScale m r x * a) := by
    apply symplecticClosedPointMatrix_injective m
    rw [symplecticClosedPointMatrix_mul, symplecticClosedPointMatrix_mul,
      symplecticClosedPointMatrix_rootPoint, symplecticClosedPointMatrix_rootPoint, hd]
    exact symplecticRootMatrix_mul_diagonal m r a x
  calc
    d⁻¹ * symplecticRootPoint m r a * d =
        d⁻¹ * (symplecticRootPoint m r a * d) := by rw [mul_assoc]
    _ = d⁻¹ * (d * symplecticRootPoint m r (symplecticRootScale m r x * a)) :=
      congrArg (d⁻¹ * ·) hcomm
    _ = symplecticRootPoint m r (symplecticRootScale m r x * a) := by simp

public theorem symplecticRootSubgroup_conjugation_mem_of_diagonal
    (m : ℕ) (r : TypeCRootIndex m)
    (d : Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety)
    (z : Variety.Point (dVariety k m))
    (hd : symplecticClosedPointMatrix m d = symplecticDiagonalMatrix m z)
    (x : Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety)
    (hx : x ∈ symplecticRootSubgroup (k := k) m r) :
    d⁻¹ * x * d ∈ symplecticRootSubgroup (k := k) m r := by
  change x ∈ (symplecticRootMorphism m r).image at hx
  rcases hx with ⟨q, rfl⟩
  rw [symplecticRootMorphism_apply,
    symplecticRootPoint_diagonal_conjugation m r (q.val PUnit.unit) d z hd]
  exact ⟨kPlusPoint (symplecticRootScale m r z * q.val PUnit.unit), rfl⟩

public theorem symplecticRootSubgroup_rootWeightEquation_of_diagonal
    (m : ℕ) (r : TypeCRootIndex m)
    (T : ClosedSubgroup
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety)
    (chi : TorusWeight T)
    (z : Variety.Point T.carrierVariety → Variety.Point (dVariety k m))
    (hdiag : ∀ s, symplecticClosedPointMatrix m (T.includePoint s) =
      symplecticDiagonalMatrix m (z s))
    (hchi : ∀ s,
      (@TorusCharacter.pointCharacter k _ T.carrierVariety
        T.carrierAlgebraicGroup chi) s = symplecticRootScale m r (z s)) :
    RootWeightEquation T (symplecticRootSubgroup (k := k) m r) chi := by
  intro y t s
  let _ : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
  let _ : AlgebraicGroup
      (symplecticRootSubgroup (k := k) m r).carrierVariety :=
    (symplecticRootSubgroup (k := k) m r).carrierAlgebraicGroup
  let p := symplecticRootParametrization (k := k) m r
  rcases oneParameterParametrization_eq_rescale p y with ⟨c, hc, _⟩
  rw [show (symplecticRootSubgroup (k := k) m r).includePoint (y.value t) =
      symplecticRootPoint m r (c * t) by
        rw [hc.2, symplecticRootParametrization_include_value]]
  rw [show (symplecticRootSubgroup (k := k) m r).includePoint
        (y.value (chi.pointCharacter s * t)) =
      symplecticRootPoint m r (c * (chi.pointCharacter s * t)) by
        rw [hc.2, symplecticRootParametrization_include_value]]
  rw [symplecticRootPoint_diagonal_conjugation m r (c * t)
    (T.includePoint s) (z s) (hdiag s)]
  congr 1
  rw [hchi]
  ring

/-! The paired diagonal matrices form the standard symplectic torus carrier.
The inverse diagonal coordinates make the carrier map regular; its image is a
closed torus and transports the Laurent characters of `dVariety`. -/

omit [IsAlgClosed k] in
public lemma symplecticDiagonalMatrix_mem (m : ℕ) (z : Fin m → kˣ) :
    Matrix.diagonal (symplecticDiagonalValue (k := k) m z) ∈
      Matrix.symplecticGroup (Fin m) k := by
  have hblocks : Matrix.diagonal (symplecticDiagonalValue (k := k) m z) =
      Matrix.fromBlocks (Matrix.diagonal fun i => (z i : k)) 0 0
        (Matrix.diagonal fun i => ((z i : k)⁻¹)) := by
    ext (i | i) (j | j) <;> by_cases hij : i = j <;>
      simp [symplecticDiagonalValue, hij]
  rw [hblocks, SymplecticGroup.fromBlocks_mem_iff]
  refine ⟨by simp, by simp, ?_⟩
  ext i j
  simp

omit [IsAlgClosed k] in
public lemma symplecticDiagonalMatrix_symplectic (m : ℕ)
    (x : Variety.Point (dVariety k m)) :
    symplecticDiagonalMatrix (k := k) m x ∈
      Matrix.symplecticGroup (Fin m) k :=
  symplecticDiagonalMatrix_mem m (dPointEquiv m x)

omit [IsAlgClosed k] in
public lemma symplecticDiagonalMatrix_one (m : ℕ) :
    symplecticDiagonalMatrix (k := k) m 1 = 1 := by
  rw [symplecticDiagonalMatrix, dPointEquiv_one]
  ext p q
  by_cases hpq : p = q
  · subst q
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply]
    cases p <;> simp [symplecticDiagonalValue]
  · rw [Matrix.diagonal_apply_ne _ hpq, Matrix.one_apply]
    simp [hpq]

@[expose]
public noncomputable def symplecticDiagonalFinMatrix (m : ℕ)
    (x : Variety.Point (dVariety k m)) :
    Matrix (Fin (Module.finrank k (symplecticStandardSpace (k := k) m)))
      (Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) k :=
  Matrix.reindexAlgEquiv k k (symplecticStandardIndexEquiv (k := k) m)
    (symplecticDiagonalMatrix m x)

omit [IsAlgClosed k] in
public lemma symplecticDiagonalFinMatrix_det (m : ℕ)
    (x : Variety.Point (dVariety k m)) :
    (symplecticDiagonalFinMatrix (k := k) m x).det = 1 := by
  rw [symplecticDiagonalFinMatrix, Matrix.coe_reindexAlgEquiv,
    Matrix.det_reindex_self]
  exact SymplecticGroup.det_eq_one (symplecticDiagonalMatrix_symplectic m x)

@[expose]
public noncomputable def symplecticDiagonalGL (m : ℕ)
    (x : Variety.Point (dVariety k m)) :
    GL (Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (symplecticDiagonalFinMatrix m x)
    (by rw [symplecticDiagonalFinMatrix_det]; exact one_ne_zero)

@[expose]
public noncomputable def symplecticDiagonalAmbientPoint (m : ℕ)
    (x : Variety.Point (dVariety k m)) :
    Variety.Point (glVarietyOf k (symplecticStandardSpace (k := k) m)) :=
  (glPointEquiv (Module.finrank k (symplecticStandardSpace (k := k) m))).symm
    (symplecticDiagonalGL m x)

@[simp]
public lemma symplecticDiagonalAmbientPoint_val (m : ℕ)
    (x : Variety.Point (dVariety k m)) (p q : symplecticStandardIndex m) :
    (symplecticDiagonalAmbientPoint m x).val
        (Sum.inl (symplecticStandardIndexEquiv (k := k) m p,
          symplecticStandardIndexEquiv (k := k) m q)) =
      symplecticDiagonalMatrix (k := k) m x p q := by
  simp [symplecticDiagonalAmbientPoint, symplecticDiagonalGL, glPointEquiv,
    symplecticDiagonalFinMatrix, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]

@[simp]
public lemma symplecticDiagonalAmbientPoint_scalar (m : ℕ)
    (x : Variety.Point (dVariety k m)) :
    (symplecticDiagonalAmbientPoint m x).val (Sum.inr PUnit.unit) = 1 := by
  simp [symplecticDiagonalAmbientPoint, symplecticDiagonalGL, glPointEquiv,
    symplecticDiagonalFinMatrix_det]

public lemma symplecticDiagonalAmbientPoint_one (m : ℕ) :
    symplecticDiagonalAmbientPoint (k := k) m 1 = 1 := by
  let e : Variety.Point (glVarietyOf k (symplecticStandardSpace (k := k) m)) ≃*
      GL (Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) k := by
    exact translationGLPointMulEquiv
      (k := k) (Module.finrank k (symplecticStandardSpace (k := k) m))
  have hfin : symplecticDiagonalFinMatrix (k := k) m 1 = 1 := by
    rw [symplecticDiagonalFinMatrix, symplecticDiagonalMatrix_one, map_one]
  have hgl : symplecticDiagonalGL (k := k) m 1 = 1 := by
    apply Units.ext
    exact hfin
  calc
    symplecticDiagonalAmbientPoint (k := k) m 1 =
        e.symm (symplecticDiagonalGL m 1) := rfl
    _ = e.symm 1 := congrArg _ hgl
    _ = 1 := map_one _

public lemma symplecticDiagonalAmbientPoint_symplecticMatrix (m : ℕ)
    (x : Variety.Point (dVariety k m)) :
    symplecticMatrix (k := k) m
        (LinearMap.GeneralLinearGroup.generalLinearEquiv k
          (symplecticStandardSpace (k := k) m)
          (glPointEquivOf k (symplecticStandardSpace (k := k) m)
            (symplecticStandardBasis (k := k) m)
            (symplecticDiagonalAmbientPoint m x))) =
      symplecticDiagonalMatrix (k := k) m x := by
  ext p q
  rw [symplecticMatrix, LinearMap.toMatrix_apply]
  change (Pi.basisFun k (symplecticStandardIndex m)).repr
      ((glPointEquivOf k (symplecticStandardSpace (k := k) m)
        (symplecticStandardBasis (k := k) m)
        (symplecticDiagonalAmbientPoint m x)).1
          ((Pi.basisFun k (symplecticStandardIndex m)) q)) p = _
  rw [Pi.basisFun_apply, ← symplecticStandardBasis_apply (k := k) m q,
    glPointEquivOf_apply_basis, pi_repr_standardSymplecticBasis_symm]
  change (symplecticDiagonalAmbientPoint m x).val
      (Sum.inl (symplecticStandardIndexEquiv (k := k) m p,
        symplecticStandardIndexEquiv (k := k) m q)) = _
  exact symplecticDiagonalAmbientPoint_val m x p q

public lemma symplecticDiagonalAmbientPoint_mem (m : ℕ)
    (x : Variety.Point (dVariety k m)) :
    symplecticDiagonalAmbientPoint (k := k) m x ∈
      (standardSymplecticClosedSubgroup (k := k) m).toSubgroup := by
  rw [standardSymplecticClosedSubgroup_carrier,
    mem_bilinearIsometrySubgroup_iff_symplecticMatrix,
    symplecticDiagonalAmbientPoint_symplecticMatrix]
  exact symplecticDiagonalMatrix_symplectic m x

@[expose]
public noncomputable def symplecticDiagonalPoint (m : ℕ)
    (x : Variety.Point (dVariety k m)) :
    Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety :=
  (standardSymplecticClosedSubgroup (k := k) m).pointEquiv.symm
    ⟨symplecticDiagonalAmbientPoint m x, symplecticDiagonalAmbientPoint_mem m x⟩

@[simp]
public lemma symplecticDiagonalPoint_include (m : ℕ)
    (x : Variety.Point (dVariety k m)) :
    (standardSymplecticClosedSubgroup (k := k) m).includePoint
        (symplecticDiagonalPoint m x) = symplecticDiagonalAmbientPoint m x := by
  change ((standardSymplecticClosedSubgroup (k := k) m).pointEquiv
    (symplecticDiagonalPoint m x)).val = _
  rw [symplecticDiagonalPoint,
    (standardSymplecticClosedSubgroup (k := k) m).pointEquiv.apply_symm_apply]

@[simp]
public lemma symplecticDiagonalPoint_val (m : ℕ)
    (x : Variety.Point (dVariety k m)) (p q : symplecticStandardIndex m) :
    (symplecticDiagonalPoint m x).val
        (Sum.inl (symplecticStandardIndexEquiv (k := k) m p,
          symplecticStandardIndexEquiv (k := k) m q)) =
      symplecticDiagonalMatrix (k := k) m x p q := by
  rw [← (standardSymplecticClosedSubgroup (k := k) m).pointEquiv_val
    (symplecticDiagonalPoint m x), symplecticDiagonalPoint,
    (standardSymplecticClosedSubgroup (k := k) m).pointEquiv.apply_symm_apply]
  exact symplecticDiagonalAmbientPoint_val m x p q

@[simp]
public lemma symplecticDiagonalPoint_scalar (m : ℕ)
    (x : Variety.Point (dVariety k m)) :
    (symplecticDiagonalPoint m x).val (Sum.inr PUnit.unit) = 1 := by
  rw [← (standardSymplecticClosedSubgroup (k := k) m).pointEquiv_val
    (symplecticDiagonalPoint m x), symplecticDiagonalPoint,
    (standardSymplecticClosedSubgroup (k := k) m).pointEquiv.apply_symm_apply]
  exact symplecticDiagonalAmbientPoint_scalar m x

@[simp]
public lemma symplecticClosedPointMatrix_diagonalPoint (m : ℕ)
    (x : Variety.Point (dVariety k m)) :
    symplecticClosedPointMatrix m (symplecticDiagonalPoint m x) =
      symplecticDiagonalMatrix (k := k) m x := by
  rw [symplecticClosedPointMatrix]
  rw [← standardSymplecticClosedSubgroup_linear_points m
    (symplecticDiagonalPoint m x)]
  change symplecticMatrix m
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k
        (symplecticStandardSpace (k := k) m)
        (glPointEquivOf k (symplecticStandardSpace (k := k) m)
          (symplecticStandardBasis (k := k) m)
          ((standardSymplecticClosedSubgroup (k := k) m).includePoint
            (symplecticDiagonalPoint m x)))) = _
  rw [symplecticDiagonalPoint_include]
  exact symplecticDiagonalAmbientPoint_symplecticMatrix m x

@[expose]
public noncomputable def symplecticDiagonalMorphism (m : ℕ) :
    AlgebraicGroup.Morphism (dVariety k m)
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety where
  toVariety :=
    { toFun := symplecticDiagonalPoint m
      regular := by
        rintro (⟨i, j⟩ | PUnit.unit)
        · let e := symplecticStandardIndexEquiv (k := k) m
          by_cases hij : i = j
          · subst j
            cases hpi : e.symm i with
            | inl p =>
              refine ⟨MvPolynomial.X (Sum.inl (ULift.up p)), ?_⟩
              intro x
              rw [evalPolynomial_X]
              have hi : i = e (Sum.inl p) := by
                rw [← hpi]
                exact (e.apply_symm_apply i).symm
              rw [hi, symplecticDiagonalPoint_val,
                symplecticDiagonalMatrix, Matrix.diagonal_apply_eq]
              change dPointEntry m x p = x.val (Sum.inl (ULift.up p))
              rfl
            | inr p =>
              refine ⟨MvPolynomial.X (Sum.inr (ULift.up p)), ?_⟩
              intro x
              rw [evalPolynomial_X]
              have hi : i = e (Sum.inr p) := by
                rw [← hpi]
                exact (e.apply_symm_apply i).symm
              rw [hi, symplecticDiagonalPoint_val,
                symplecticDiagonalMatrix, Matrix.diagonal_apply_eq]
              change (dPointEntry m x p)⁻¹ = x.val (Sum.inr (ULift.up p))
              rw [dPoint_entry_inv]
              rfl
          · refine ⟨0, ?_⟩
            intro x
            have hpq : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
            rw [show i = e (e.symm i) by exact (e.apply_symm_apply i).symm,
              show j = e (e.symm j) by exact (e.apply_symm_apply j).symm]
            rw [symplecticDiagonalPoint_val, symplecticDiagonalMatrix,
              Matrix.diagonal_apply_ne _ hpq]
            simp [evalPolynomial]
        · refine ⟨1, ?_⟩
          intro x
          rw [symplecticDiagonalPoint_scalar]
          simp [evalPolynomial] }
  map_one := by
    apply (standardSymplecticClosedSubgroup (k := k) m).inclusion_injective
    change (standardSymplecticClosedSubgroup (k := k) m).includePoint
        (symplecticDiagonalPoint m 1) =
      (standardSymplecticClosedSubgroup (k := k) m).includePoint 1
    rw [symplecticDiagonalPoint_include, symplecticDiagonalAmbientPoint_one]
    exact (standardSymplecticClosedSubgroup (k := k) m).inclusion.map_one.symm
  map_mul := by
    intro x y
    apply symplecticClosedPointMatrix_injective m
    rw [symplecticClosedPointMatrix_diagonalPoint,
      symplecticClosedPointMatrix_mul,
      symplecticClosedPointMatrix_diagonalPoint,
      symplecticClosedPointMatrix_diagonalPoint]
    rw [symplecticDiagonalMatrix, symplecticDiagonalMatrix,
      symplecticDiagonalMatrix, Matrix.diagonal_mul_diagonal]
    congr 1
    funext p
    rw [symplecticDiagonalValue_point, symplecticDiagonalValue_point,
      symplecticDiagonalValue_point]
    exact congrArg Units.val
      (congrFun (symplecticDiagonalEntries_mul (k := k) m x y) p)

@[simp]
public lemma symplecticDiagonalMorphism_apply (m : ℕ)
    (x : Variety.Point (dVariety k m)) :
    (symplecticDiagonalMorphism (k := k) m).onPoints x = symplecticDiagonalPoint m x := rfl

public lemma symplecticDiagonalMorphism_matrix (m : ℕ)
    (x : Variety.Point (dVariety k m)) :
    symplecticClosedPointMatrix (k := k) m
        ((symplecticDiagonalMorphism (k := k) m).onPoints x) =
      symplecticDiagonalMatrix (k := k) m x := by
  rw [symplecticDiagonalMorphism_apply, symplecticClosedPointMatrix_diagonalPoint]

@[expose]
public noncomputable def symplecticDiagonalTorus (m : ℕ) :
    ClosedSubgroup (standardSymplecticClosedSubgroup (k := k) m).carrierVariety :=
  (symplecticDiagonalMorphism m).imageClosedSubgroup

public lemma symplecticDiagonalTorus_mem_iff (m : ℕ)
    (g : Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety) :
    g ∈ (symplecticDiagonalTorus m).toSubgroup ↔
      ∃ x : Variety.Point (dVariety k m),
        (symplecticDiagonalMorphism m).onPoints x = g := by
  change g ∈ (symplecticDiagonalMorphism m).image ↔ _
  rfl

public lemma symplecticDiagonalTorus_isSubtorus (m : ℕ) :
    IsSubtorus (symplecticDiagonalTorus (k := k) m) :=
  morphism_image_isTorus (symplecticDiagonalMorphism m) (dVariety_isTorus m)

public lemma symplecticDiagonalMorphism_injective (m : ℕ) :
    Function.Injective (symplecticDiagonalMorphism (k := k) m).onPoints := by
  intro x y hxy
  apply (dPointEquiv m).injective
  funext i
  apply Units.ext
  have hm := congrArg
    (fun g : Variety.Point
        (standardSymplecticClosedSubgroup (k := k) m).carrierVariety =>
      g.val (Sum.inl (symplecticStandardIndexEquiv (k := k) m (Sum.inl i),
        symplecticStandardIndexEquiv (k := k) m (Sum.inl i)))) hxy
  simpa [symplecticDiagonalMorphism_apply, symplecticDiagonalPoint_val,
    symplecticDiagonalMatrix, Matrix.diagonal_apply_eq,
    symplecticDiagonalValue, symplecticDiagonalEntries] using hm

public lemma symplecticDiagonalMorphism_coordinate_preimage (m : ℕ) :
    ∀ c : (dVariety k m).Coordinates,
      ∃ q : Variety.PolynomialFunction
          (standardSymplecticClosedSubgroup (k := k) m).carrierVariety,
        Variety.PolynomialFunction.pullback
            (symplecticDiagonalMorphism m).toVariety q =
          Variety.PolynomialFunction.ofPolynomial (dVariety k m)
            (MvPolynomial.X c) := by
  intro c
  cases c with
  | inl i =>
      let c' : (standardSymplecticClosedSubgroup (k := k) m).carrierVariety.Coordinates :=
        Sum.inl (symplecticStandardIndexEquiv (k := k) m (Sum.inl i.down),
          symplecticStandardIndexEquiv (k := k) m (Sum.inl i.down))
      let q : Variety.PolynomialFunction
          (standardSymplecticClosedSubgroup (k := k) m).carrierVariety :=
        Variety.PolynomialFunction.ofPolynomial _
          (MvPolynomial.X c')
      refine ⟨q, ?_⟩
      apply Variety.PolynomialFunction.ext
      intro x
      change q ((symplecticDiagonalMorphism m).onPoints x) =
        Variety.PolynomialFunction.ofPolynomial (dVariety k m)
          (MvPolynomial.X (Sum.inl i)) x
      dsimp only [q, Variety.PolynomialFunction.ofPolynomial,
        Variety.PolynomialFunction.toFun]
      change evalPolynomial _ (MvPolynomial.X c') =
        evalPolynomial _ (MvPolynomial.X (Sum.inl i))
      rw [evalPolynomial_X, evalPolynomial_X]
      dsimp only [c']
      rw [symplecticDiagonalMorphism_apply, symplecticDiagonalPoint_val,
        symplecticDiagonalMatrix, Matrix.diagonal_apply_eq]
      change dPointEntry m x i.down = x.val (Sum.inl i)
      rfl
  | inr i =>
      let c' : (standardSymplecticClosedSubgroup (k := k) m).carrierVariety.Coordinates :=
        Sum.inl (symplecticStandardIndexEquiv (k := k) m (Sum.inr i.down),
          symplecticStandardIndexEquiv (k := k) m (Sum.inr i.down))
      let q : Variety.PolynomialFunction
          (standardSymplecticClosedSubgroup (k := k) m).carrierVariety :=
        Variety.PolynomialFunction.ofPolynomial _
          (MvPolynomial.X c')
      refine ⟨q, ?_⟩
      apply Variety.PolynomialFunction.ext
      intro x
      change q ((symplecticDiagonalMorphism m).onPoints x) =
        Variety.PolynomialFunction.ofPolynomial (dVariety k m)
          (MvPolynomial.X (Sum.inr i)) x
      dsimp only [q, Variety.PolynomialFunction.ofPolynomial,
        Variety.PolynomialFunction.toFun]
      change evalPolynomial _ (MvPolynomial.X c') =
        evalPolynomial _ (MvPolynomial.X (Sum.inr i))
      rw [evalPolynomial_X, evalPolynomial_X]
      dsimp only [c']
      rw [symplecticDiagonalMorphism_apply, symplecticDiagonalPoint_val,
        symplecticDiagonalMatrix, Matrix.diagonal_apply_eq]
      change (dPointEntry m x i.down)⁻¹ = dPointEntryInv m x i.down
      exact dPoint_entry_inv m x i.down

public noncomputable def symplecticDiagonalTorusIso (m : ℕ) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    AlgebraicGroup.Iso (dVariety k m)
      (symplecticDiagonalTorus m).carrierVariety := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  exact Classical.choose
    ((symplecticDiagonalMorphism m).iso_imageClosedSubgroup_of_coordinate_preimage
      (symplecticDiagonalMorphism_injective m)
      (symplecticDiagonalMorphism_coordinate_preimage m))

public lemma symplecticDiagonalTorusIso_hom (m : ℕ) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    (symplecticDiagonalTorusIso (k := k) m).hom =
      (symplecticDiagonalMorphism m).codRestrictClosedSubgroup
        (symplecticDiagonalTorus m) (fun y => ⟨y, rfl⟩) := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  exact Classical.choose_spec
    ((symplecticDiagonalMorphism m).iso_imageClosedSubgroup_of_coordinate_preimage
      (symplecticDiagonalMorphism_injective m)
      (symplecticDiagonalMorphism_coordinate_preimage m))

public lemma symplecticDiagonalTorusIso_inclusion_hom (m : ℕ)
    (x : Variety.Point (dVariety k m)) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    (symplecticDiagonalTorus m).inclusion.onPoints
        ((symplecticDiagonalTorusIso m).hom.onPoints x) =
      (symplecticDiagonalMorphism m).onPoints x := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  rw [symplecticDiagonalTorusIso_hom]
  exact AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply
    (symplecticDiagonalMorphism m) (symplecticDiagonalTorus m)
      (fun y => ⟨y, rfl⟩) x

@[expose]
public noncomputable def symplecticDiagonalTorusPointEquiv (m : ℕ) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    Variety.Point (symplecticDiagonalTorus (k := k) m).carrierVariety ≃*
      Variety.Point (dVariety k m) := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  exact (symplecticDiagonalTorusIso (k := k) m).toMulEquiv.symm

public lemma symplecticDiagonalTorusPointEquiv_symm_inclusion (m : ℕ)
    (x : Variety.Point (dVariety k m)) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    (symplecticDiagonalTorus (k := k) m).inclusion.onPoints
        ((symplecticDiagonalTorusPointEquiv (k := k) m).symm x) =
      (symplecticDiagonalMorphism (k := k) m).onPoints x := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  exact symplecticDiagonalTorusIso_inclusion_hom (k := k) m x

@[expose]
public noncomputable def symplecticDiagonalCharacterTransport (m : ℕ) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    TorusCharacter (dVariety k m) ≃*
      TorusWeight (symplecticDiagonalTorus (k := k) m) := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  let e := symplecticDiagonalTorusIso (k := k) m
  exact
    { toFun := TorusCharacter.pullback e.inv
      invFun := TorusCharacter.pullback e.hom
      left_inv := by
        intro chi
        apply AlgebraicGroup.Morphism.ext
        funext x
        change chi.onPoints (e.inv.onPoints (e.hom.onPoints x)) = chi.onPoints x
        rw [e.hom_inv_id]
      right_inv := by
        intro chi
        apply AlgebraicGroup.Morphism.ext
        funext x
        change chi.onPoints (e.hom.onPoints (e.inv.onPoints x)) = chi.onPoints x
        rw [e.inv_hom_id]
      map_mul' := (TorusCharacter.pullback e.inv).map_mul }

@[expose]
public noncomputable def symplecticDiagonalCharacter (m : ℕ)
    (z : Fin m → ℤ) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    TorusWeight (symplecticDiagonalTorus (k := k) m) := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  exact symplecticDiagonalCharacterTransport (k := k) m
    (dLaurentCharacter (k := k) m z)

public lemma symplecticDiagonalCharacter_apply (m : ℕ) (z : Fin m → ℤ)
    (x : Variety.Point (dVariety k m)) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    dPointEquiv 1
        ((symplecticDiagonalCharacter (k := k) m z).onPoints
          ((symplecticDiagonalTorusIso (k := k) m).hom.onPoints x)) 0 =
      ∏ i, (dPointEquiv m x i) ^ z i := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  change dPointEquiv 1
      ((dLaurentCharacter (k := k) m z).onPoints
        ((symplecticDiagonalTorusIso (k := k) m).inv.onPoints
          ((symplecticDiagonalTorusIso (k := k) m).hom.onPoints x))) 0 = _
  rw [(symplecticDiagonalTorusIso (k := k) m).hom_inv_id,
    dLaurentCharacter_apply]

@[expose]
public noncomputable def symplecticRootExponent (m : ℕ) :
    TypeCRootIndex m → Fin m → ℤ
  | .inl ⟨⟨⟨a, b⟩, _⟩, s, t⟩ =>
      (if s.1 = 1 then (-1 : ℤ) else 1) • Pi.single a 1 +
        (if t.1 = 1 then (-1 : ℤ) else 1) • Pi.single b 1
  | .inr ⟨a, false⟩ => -2 • Pi.single a 1
  | .inr ⟨a, true⟩ => 2 • Pi.single a 1

@[expose]
public noncomputable def symplecticRootWeight (m : ℕ) (r : TypeCRootIndex m) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    TorusWeight (symplecticDiagonalTorus (k := k) m) := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  exact symplecticDiagonalCharacter (k := k) m (symplecticRootExponent m r)

private lemma symplecticRootExponent_cast (m : ℕ) (r : TypeCRootIndex m)
    (i : Fin m) :
    ((symplecticRootExponent m r i : ℤ) : ℝ) =
      -(typeCRootVector m r i) := by
  rcases r with ⟨⟨⟨a, b⟩, hab⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩ | ⟨a, u⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      by_cases hia : i = a <;> by_cases hib : i = b <;>
        norm_num [symplecticRootExponent, typeCRootVector, basisVector,
          Pi.single_apply, hia, hib, add_comm]
  · cases u <;> by_cases hia : i = a <;>
      simp [symplecticRootExponent, typeCRootVector, basisVector, hia]

omit [IsAlgClosed k] in
private lemma prod_zpow_single (m : ℕ) (z : Fin m → kˣ)
    (i : Fin m) (n : ℤ) :
    (∏ j, z j ^ (Pi.single i n : Fin m → ℤ) j) = z i ^ n := by
  calc
    (∏ j, z j ^ (Pi.single i n : Fin m → ℤ) j) =
        z i ^ (Pi.single i n : Fin m → ℤ) i := by
      apply Fintype.prod_eq_single i
      intro j hji
      simp [hji]
    _ = z i ^ n := by simp

omit [IsAlgClosed k] in
private lemma prod_zpow_add (m : ℕ) (z : Fin m → kˣ)
    (a b : Fin m → ℤ) :
    (∏ j, z j ^ (a j + b j)) =
      (∏ j, z j ^ a j) * ∏ j, z j ^ b j := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  exact zpow_add _ _ _

omit [IsAlgClosed k] in
private lemma prod_zpow_smul_single (m : ℕ) (z : Fin m → kˣ)
    (i : Fin m) (n : ℤ) :
    (∏ j, z j ^ (n • Pi.single i 1 : Fin m → ℤ) j) = z i ^ n := by
  rw [show (n • Pi.single i 1 : Fin m → ℤ) = Pi.single i n by
    funext j
    by_cases hji : j = i <;> simp [hji]]
  exact prod_zpow_single m z i n

public lemma symplecticRootWeight_injective (m : ℕ) :
    Function.Injective (symplecticRootWeight (k := k) m) := by
  intro r q hrq
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  have hchar :
      dLaurentCharacter (k := k) m (symplecticRootExponent m r) =
        dLaurentCharacter m (symplecticRootExponent m q) := by
    apply (symplecticDiagonalCharacterTransport (k := k) m).injective
    simpa [symplecticRootWeight, symplecticDiagonalCharacter] using hrq
  have hexp := dLaurentCharacter_injective (k := k) m hchar
  apply typeCRootEmbedding_injective m
  apply Subtype.ext
  funext i
  have hi := congrArg (fun z : ℤ => (z : ℝ)) (congrFun hexp i)
  rw [symplecticRootExponent_cast, symplecticRootExponent_cast] at hi
  exact neg_injective hi

public lemma symplecticRootWeight_apply (m : ℕ) (r : TypeCRootIndex m)
    (x : Variety.Point (dVariety k m)) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    dPointEquiv 1
        ((symplecticRootWeight (k := k) m r).onPoints
          ((symplecticDiagonalTorusIso m).hom.onPoints x)) 0 =
      symplecticRootScale m r x := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  rw [symplecticRootWeight, symplecticDiagonalCharacter_apply]
  rcases r with ⟨⟨⟨i, j⟩, _⟩, s, t⟩ | ⟨i, b⟩
  · simp only [symplecticRootExponent, Pi.add_apply]
    change ((∏ q, (dPointEquiv m x q) ^
      (((if s.1 = 1 then (-1 : ℤ) else 1) • Pi.single i 1) q +
       ((if t.1 = 1 then (-1 : ℤ) else 1) • Pi.single j 1) q) : kˣ) : k) = _
    rw [prod_zpow_add, prod_zpow_smul_single, prod_zpow_smul_single]
    by_cases hs : s.1 = 1 <;> by_cases ht : t.1 = 1 <;>
      simp [symplecticRootScale, symplecticRootScaleValue, hs, ht]
  · cases b
    · simp only [symplecticRootExponent]
      change ((∏ q, (dPointEquiv m x q) ^
          ((-2 : ℤ) • (Pi.single i (1 : ℤ) : Fin m → ℤ)) q : kˣ) : k) =
        symplecticRootScaleValue m (Sum.inr (i, false)) (dPointEquiv m x)
      rw [prod_zpow_smul_single]
      simp [symplecticRootScaleValue, pow_two]
    · simp only [symplecticRootExponent]
      change ((∏ q, (dPointEquiv m x q) ^
          ((2 : ℤ) • (Pi.single i (1 : ℤ) : Fin m → ℤ)) q : kˣ) : k) =
        symplecticRootScaleValue m (Sum.inr (i, true)) (dPointEquiv m x)
      rw [prod_zpow_smul_single]
      simp [symplecticRootScaleValue, pow_two]

public theorem symplecticRootWeight_pointCharacter (m : ℕ)
    (r : TypeCRootIndex m) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    ∀ s : Variety.Point (symplecticDiagonalTorus (k := k) m).carrierVariety,
      (symplecticRootWeight (k := k) m r).pointCharacter s =
        symplecticRootScale (k := k) m r
          (symplecticDiagonalTorusPointEquiv (k := k) m s) := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  intro s
  let x := symplecticDiagonalTorusPointEquiv (k := k) m s
  have hx : (symplecticDiagonalTorusIso (k := k) m).hom.onPoints x = s := by
    change (symplecticDiagonalTorusIso (k := k) m).hom.onPoints
        ((symplecticDiagonalTorusIso (k := k) m).inv.onPoints s) = s
    rw [(symplecticDiagonalTorusIso (k := k) m).inv_hom_id]
  change dPointEquiv 1
      ((symplecticRootWeight (k := k) m r).onPoints s) 0 =
    symplecticRootScale (k := k) m r x
  rw [← hx]
  exact symplecticRootWeight_apply (k := k) m r x

public theorem symplecticRootPoint_diagonal_conjugation_torus (m : ℕ)
    (r : TypeCRootIndex m) (a : k)
    (s : Variety.Point (symplecticDiagonalTorus (k := k) m).carrierVariety) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    (symplecticDiagonalTorus (k := k) m).includePoint s ⁻¹ *
        symplecticRootPoint (k := k) m r a *
          (symplecticDiagonalTorus (k := k) m).includePoint s =
      symplecticRootPoint (k := k) m r
        ((symplecticRootWeight (k := k) m r).pointCharacter s * a) := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  let x := symplecticDiagonalTorusPointEquiv (k := k) m s
  have hx : (symplecticDiagonalTorusIso (k := k) m).hom.onPoints x = s := by
    change (symplecticDiagonalTorusIso (k := k) m).hom.onPoints
        ((symplecticDiagonalTorusIso (k := k) m).inv.onPoints s) = s
    rw [(symplecticDiagonalTorusIso (k := k) m).inv_hom_id]
  have hi := symplecticDiagonalTorusIso_inclusion_hom (k := k) m x
  rw [hx] at hi
  have hdiag : symplecticClosedPointMatrix (k := k) m
      ((symplecticDiagonalTorus (k := k) m).includePoint s) =
      symplecticDiagonalMatrix (k := k) m x := by
    rw [show (symplecticDiagonalTorus (k := k) m).includePoint s =
        (symplecticDiagonalTorus (k := k) m).inclusion.onPoints s by rfl,
      hi, symplecticDiagonalMorphism_matrix]
  calc
    (symplecticDiagonalTorus (k := k) m).includePoint s ⁻¹ *
          symplecticRootPoint (k := k) m r a *
            (symplecticDiagonalTorus (k := k) m).includePoint s =
        symplecticRootPoint (k := k) m r
          (symplecticRootScale (k := k) m r x * a) :=
      symplecticRootPoint_diagonal_conjugation m r a
        ((symplecticDiagonalTorus (k := k) m).includePoint s) x hdiag
    _ = symplecticRootPoint (k := k) m r
          ((symplecticRootWeight (k := k) m r).pointCharacter s * a) := by
      rw [symplecticRootWeight_pointCharacter (k := k) m r s]

public lemma symplecticRootWeight_equation (m : ℕ) (r : TypeCRootIndex m) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    RootWeightEquation (symplecticDiagonalTorus (k := k) m)
      (symplecticRootSubgroup (k := k) m r) (symplecticRootWeight m r) := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  apply symplecticRootSubgroup_rootWeightEquation_of_diagonal
      (m := m) (r := r) (T := symplecticDiagonalTorus m)
      (chi := symplecticRootWeight m r)
      (z := fun s => symplecticDiagonalTorusPointEquiv m s)
  · intro s
    let x := symplecticDiagonalTorusPointEquiv (k := k) m s
    have hx : (symplecticDiagonalTorusIso (k := k) m).hom.onPoints x = s := by
      change (symplecticDiagonalTorusIso (k := k) m).hom.onPoints
          ((symplecticDiagonalTorusIso (k := k) m).inv.onPoints s) = s
      rw [(symplecticDiagonalTorusIso (k := k) m).inv_hom_id]
    rw [show (symplecticDiagonalTorus (k := k) m).includePoint s =
        (symplecticDiagonalTorus m).inclusion.onPoints s by rfl]
    rw [← hx, symplecticDiagonalTorusIso_inclusion_hom,
      symplecticDiagonalMorphism_apply,
      symplecticClosedPointMatrix_diagonalPoint]
    rw [show symplecticDiagonalTorusPointEquiv (k := k) m
          ((symplecticDiagonalTorusIso m).hom.onPoints x) = x by
      change (symplecticDiagonalTorusIso (k := k) m).inv.onPoints
          ((symplecticDiagonalTorusIso m).hom.onPoints x) = x
      rw [(symplecticDiagonalTorusIso (k := k) m).hom_inv_id]]
  · intro s
    let x := symplecticDiagonalTorusPointEquiv (k := k) m s
    have hx : (symplecticDiagonalTorusIso (k := k) m).hom.onPoints x = s := by
      change (symplecticDiagonalTorusIso (k := k) m).hom.onPoints
          ((symplecticDiagonalTorusIso (k := k) m).inv.onPoints s) = s
      rw [(symplecticDiagonalTorusIso (k := k) m).inv_hom_id]
    have h := symplecticRootWeight_apply (k := k) m r x
    rw [hx] at h
    exact h

end Theory.AlgebraicGroup
