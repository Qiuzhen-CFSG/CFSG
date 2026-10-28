module
public import Mathlib.LinearAlgebra.RootSystem.Chain
public import Mathlib.LinearAlgebra.RootSystem.Hom
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Algebra.Group.Units.Equiv

/-!
# Pinned diagram actions on root strings and matrix indices

A root-pairing automorphism transports membership in the root set through its
bijective weight map. Thus it preserves both root-string coefficients, including
linearly dependent pairs. If its root permutation agrees with a permutation of
the chosen base, it also preserves the Cartan matrix.

The sum of these two permutations reindexes Cartan-plus-root matrices over any
semiring, and induces an equivalence on their groups of units. Both constructions
commute with entrywise coefficient maps. These helpers deliberately use only
root-system and matrix imports, independently of the Lie-algebra construction.

The root-string proof generalizes the checked argument in
`TypeE6DiagramRootStrings.lean`. Source: GLS3, §§1.12 and 2.1–2.3; Geck's integral
simple-root construction as formalized in `IntegralGeckConstruction.lean`.
-/

namespace RootPairing.IntegralGeckConstruction
@[expose] public section
set_option linter.unusedSectionVars false
variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  [Fintype ι] [DecidableEq ι] (d : P.Equiv P)

@[simp] theorem diagram_weight_root (r : ι) :
    d.weightMap (P.root r) =
      P.root (d.indexEquiv r) :=
  congrFun d.root_weightMap r

theorem diagram_root_add_iff (r s t : ι) :
    P.root (d.indexEquiv r) =
      P.root (d.indexEquiv s) +
        P.root (d.indexEquiv t) ↔
    P.root r = P.root s + P.root t := by
  rw [← diagram_weight_root d, ← diagram_weight_root d,
    ← diagram_weight_root d, ← map_add]
  exact d.bijective_weightMap.injective.eq_iff

theorem diagram_root_add_nsmul_iff (r s t : ι) (n : ℕ) :
    P.root (d.indexEquiv r) =
      P.root (d.indexEquiv s) + n • P.root (d.indexEquiv t) ↔
    P.root r = P.root s + n • P.root t := by
  rw [← diagram_weight_root d, ← diagram_weight_root d,
    ← diagram_weight_root d, ← map_nsmul, ← map_add]
  exact d.bijective_weightMap.injective.eq_iff

theorem diagram_root_sub_iff (r s t : ι) :
    P.root (d.indexEquiv r) =
      P.root (d.indexEquiv s) -
        P.root (d.indexEquiv t) ↔
    P.root r = P.root s - P.root t := by
  rw [← diagram_weight_root d, ← diagram_weight_root d,
    ← diagram_weight_root d, ← map_sub]
  exact d.bijective_weightMap.injective.eq_iff

@[simp] theorem diagram_neg (r : ι) :
    let _ := P.indexNeg
    d.indexEquiv (-r) = -d.indexEquiv r := by
  let _ := P.indexNeg
  apply P.root.injective
  rw [← diagram_weight_root d]
  change d.weightMap
      (P.root (P.reflectionPerm r r)) =
    P.root (P.reflectionPerm
      (d.indexEquiv r) (d.indexEquiv r))
  rw [P.root_reflectionPerm, P.reflection_apply_self,
    map_neg, diagram_weight_root d, P.root_reflectionPerm,
    P.reflection_apply_self]

private theorem diagram_linearIndependent (r s : ι) :
    LinearIndependent R ![P.root (d.indexEquiv r),
      P.root (d.indexEquiv s)] ↔
    LinearIndependent R ![P.root r, P.root s] := by
  have h := d.weightMap.linearIndependent_iff
    (LinearMap.ker_eq_bot.mpr d.bijective_weightMap.injective)
      (v := ![P.root r, P.root s])
  have heq : d.weightMap ∘
      ![P.root r, P.root s] =
      ![P.root (d.indexEquiv r),
        P.root (d.indexEquiv s)] := by
    funext i
    fin_cases i <;> exact diagram_weight_root d _
  rwa [heq] at h

private theorem diagram_mem_range (x : M) :
    d.weightMap x ∈ Set.range P.root ↔
      x ∈ Set.range P.root := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨d.indexEquiv.symm r, ?_⟩
    apply d.bijective_weightMap.injective
    rw [diagram_weight_root d, Equiv.apply_symm_apply]
    exact hr
  · rintro ⟨r, rfl⟩
    exact ⟨d.indexEquiv r, (diagram_weight_root d r).symm⟩

@[simp] theorem diagram_chainBotCoeff (r s : ι) :
    P.chainBotCoeff (d.indexEquiv r)
      (d.indexEquiv s) = P.chainBotCoeff r s := by
  by_cases h : LinearIndependent R ![P.root r, P.root s]
  · rw [P.chainBotCoeff_eq_sSup h,
      P.chainBotCoeff_eq_sSup ((diagram_linearIndependent d r s).mpr h)]
    congr 1
    ext n
    simpa only [Set.mem_ofPred_eq, map_sub, map_nsmul, diagram_weight_root d]
      using diagram_mem_range d (P.root s - n • P.root r)
  · rw [P.chainBotCoeff_of_not_linearIndependent h,
      P.chainBotCoeff_of_not_linearIndependent
        (fun h' => h ((diagram_linearIndependent d r s).mp h'))]

@[simp] theorem diagram_chainTopCoeff (r s : ι) :
    P.chainTopCoeff (d.indexEquiv r)
      (d.indexEquiv s) = P.chainTopCoeff r s := by
  by_cases h : LinearIndependent R ![P.root r, P.root s]
  · rw [P.chainTopCoeff_eq_sSup h,
      P.chainTopCoeff_eq_sSup ((diagram_linearIndependent d r s).mpr h)]
    congr 1
    ext n
    simpa only [Set.mem_ofPred_eq, map_add, map_nsmul, diagram_weight_root d]
      using diagram_mem_range d (P.root s + n • P.root r)
  · rw [P.chainTopCoeff_of_not_linearIndependent h,
      P.chainTopCoeff_of_not_linearIndependent
        (fun h' => h ((diagram_linearIndependent d r s).mp h'))]

variable {b : P.Base} (db : b.support ≃ b.support)
  (hd : ∀ i : b.support, d.indexEquiv i = (db i : ι))

include hd in
/-- A pinned pairing equivalence preserves the Cartan matrix. -/
theorem diagram_cartanMatrix (i j : b.support) :
    b.cartanMatrix (db i) (db j) = b.cartanMatrix i j := by
  by_cases h : i = j
  · subst j
    simp
  · rw [b.cartanMatrix_eq_neg_chainTopCoeff (fun h' => h (db.injective h')),
      b.cartanMatrix_eq_neg_chainTopCoeff h, ← hd i, ← hd j,
      diagram_chainTopCoeff d]

/-- Permutation of the Cartan coordinates and root coordinates of the Geck lattice. -/
def diagramIndexEquiv : b.support ⊕ ι ≃ b.support ⊕ ι :=
  Equiv.sumCongr db d.indexEquiv

@[simp] theorem diagramIndexEquiv_inl (i : b.support) :
    diagramIndexEquiv d db (Sum.inl i) = Sum.inl (db i) := rfl

@[simp] theorem diagramIndexEquiv_inr (i : ι) :
    diagramIndexEquiv d db (Sum.inr i) = Sum.inr (d.indexEquiv i) := rfl

/-- Simultaneous row and column reindexing over any coefficient semiring. -/
noncomputable def diagramMatrixEquiv (S : Type*) [Semiring S] :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) S ≃+*
      Matrix (b.support ⊕ ι) (b.support ⊕ ι) S :=
  Matrix.reindexRingEquiv S (diagramIndexEquiv d db)

@[simp] theorem diagramMatrixEquiv_apply (S : Type*) [Semiring S]
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) S) (j k : b.support ⊕ ι) :
    diagramMatrixEquiv d db S A (diagramIndexEquiv d db j)
      (diagramIndexEquiv d db k) = A j k := by
  simp [diagramMatrixEquiv, Matrix.reindex_apply]

/-- Check equivariance in the original coordinates, avoiding inverse indices. -/
theorem diagramMatrixEquiv_eq_iff (S : Type*) [Semiring S]
    (A B : Matrix (b.support ⊕ ι) (b.support ⊕ ι) S) :
    diagramMatrixEquiv d db S A = B ↔
      ∀ j k, A j k = B (diagramIndexEquiv d db j) (diagramIndexEquiv d db k) := by
  constructor
  · intro h j k
    rw [← h, diagramMatrixEquiv_apply]
  · intro h
    ext j k
    obtain ⟨j, rfl⟩ := (diagramIndexEquiv d db).surjective j
    obtain ⟨k, rfl⟩ := (diagramIndexEquiv d db).surjective k
    rw [diagramMatrixEquiv_apply, h]

/-- Reindexing is natural for entrywise coefficient maps, including scalar extension. -/
theorem diagramMatrixEquiv_map {S T : Type*} [Semiring S] [Semiring T]
    (f : S → T) (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) S) :
    diagramMatrixEquiv d db T (A.map f) = (diagramMatrixEquiv d db S A).map f := rfl

/-- The induced equivalence of groups of invertible matrices. -/
noncomputable def diagramUnitsEquiv (S : Type*) [Semiring S] :
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) S)ˣ ≃*
      (Matrix (b.support ⊕ ι) (b.support ⊕ ι) S)ˣ :=
  Units.mapEquiv (diagramMatrixEquiv d db S).toMulEquiv

@[simp] theorem diagramUnitsEquiv_val (S : Type*) [Semiring S]
    (A : (Matrix (b.support ⊕ ι) (b.support ⊕ ι) S)ˣ) :
    (diagramUnitsEquiv d db S A).val = diagramMatrixEquiv d db S A.val := rfl

/-- Coefficient homomorphisms commute with diagram reindexing on units. -/
theorem diagramUnitsEquiv_map {S T : Type*} [Semiring S] [Semiring T]
    (f : S →+* T) (A : (Matrix (b.support ⊕ ι) (b.support ⊕ ι) S)ˣ) :
    diagramUnitsEquiv d db T (Units.map f.mapMatrix.toMonoidHom A) =
      Units.map f.mapMatrix.toMonoidHom (diagramUnitsEquiv d db S A) := by
  apply Units.ext
  rfl

end
end RootPairing.IntegralGeckConstruction
