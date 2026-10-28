module

public import Theory.AlgebraicGroup.RootSystems.SymplecticTangentWeightSupport
public import Theory.AlgebraicGroup.RootSubgroups.NormalizerMembership

/-!
# Exhaustiveness of the standard symplectic torus roots

For the paired diagonal torus in the standard symplectic carrier, this module
proves that its torus-root characters are exactly the explicit type-C weights
`symplecticRootWeight m r`.  Together with the injectivity theorem exported by
`SymplecticRootSubgroups`, the range theorem below is the root-indexing
interface used by the symplectic root-data assembly.

The reverse inclusion takes an invariant one-parameter subgroup to its nonzero
identity tangent and applies the coordinate support theorem from
`SymplecticTangentWeightSupport`.  To exclude the trivial character directly,
we prove that the centralizer of the paired diagonal torus is the torus itself:
distinct Laurent entry characters force a centralizing matrix to be diagonal,
and the symplectic equation pairs its two diagonal blocks by inverse entries.
The forward inclusion uses the explicit root curves and their diagonal
conjugation formula.  Thus the proof is a direct calculation in the standard
matrix model, following the usual construction of the type-C roots, and does
not invoke a general root-classification theorem.
-/

open Set

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

open StandardRootSystem

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

private noncomputable def symplecticDiagonalEntryExponent (m : ℕ) :
    symplecticStandardIndex m → Fin m → ℤ
  | Sum.inl i => Pi.single i 1
  | Sum.inr i => Pi.single i (-1)

private lemma symplecticDiagonalEntryExponent_injective (m : ℕ) :
    Function.Injective (symplecticDiagonalEntryExponent m) := by
  classical
  intro p q hpq
  cases p with
  | inl i =>
      cases q with
      | inl j =>
          congr 1
          by_contra hij
          have h := congrFun hpq i
          simp [symplecticDiagonalEntryExponent, hij] at h
      | inr j =>
          have h := congrFun hpq i
          by_cases hij : i = j <;>
            simp [symplecticDiagonalEntryExponent, hij] at h
  | inr i =>
      cases q with
      | inl j =>
          have h := congrFun hpq i
          by_cases hij : i = j <;>
            simp [symplecticDiagonalEntryExponent, hij] at h
      | inr j =>
          congr 1
          by_contra hij
          have h := congrFun hpq i
          simp [symplecticDiagonalEntryExponent, hij] at h

omit [IsAlgClosed k] in
private lemma symplecticDiagonalEntryExponent_apply (m : ℕ)
    (x : Variety.Point (dVariety k m)) (p : symplecticStandardIndex m) :
    dPointEquiv 1
        ((dLaurentCharacter m (symplecticDiagonalEntryExponent m p)).onPoints x) 0 =
      symplecticDiagonalEntries m x p := by
  classical
  cases p with
  | inl i =>
      rw [dLaurentCharacter_apply]
      simp [symplecticDiagonalEntryExponent, symplecticDiagonalEntries,
        Pi.single_apply]
  | inr i =>
      rw [dLaurentCharacter_apply]
      simp [symplecticDiagonalEntryExponent, symplecticDiagonalEntries,
        Pi.single_apply]

private lemma symplecticDiagonalEntries_separate (m : ℕ)
    {p q : symplecticStandardIndex m} (hpq : p ≠ q) :
    ∃ x : Variety.Point (dVariety k m),
      symplecticDiagonalEntries m x p ≠ symplecticDiagonalEntries m x q := by
  classical
  by_contra hnone
  push Not at hnone
  have hchars :
      dLaurentCharacter (k := k) m (symplecticDiagonalEntryExponent m p) =
        dLaurentCharacter m (symplecticDiagonalEntryExponent m q) := by
    apply AlgebraicGroup.Morphism.ext
    funext x
    apply (dPointEquiv 1).injective
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact (symplecticDiagonalEntryExponent_apply m x p).trans
      ((hnone x).trans (symplecticDiagonalEntryExponent_apply m x q).symm)
  have hexp := dLaurentCharacter_injective (k := k) m hchars
  exact hpq (symplecticDiagonalEntryExponent_injective m hexp)

omit [IsAlgClosed k] in
private lemma diagonal_symplectic_pair_mul_eq_one (m : ℕ)
    (M : Matrix (symplecticStandardIndex m) (symplecticStandardIndex m) k)
    (hdiag : ∀ p q, p ≠ q → M p q = 0)
    (hM : M ∈ Matrix.symplecticGroup (Fin m) k) (i : Fin m) :
    M (Sum.inl i) (Sum.inl i) * M (Sum.inr i) (Sum.inr i) = 1 := by
  have hMdiag : M = Matrix.diagonal (fun p => M p p) := by
    ext p q
    by_cases hpq : p = q
    · subst q
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hpq, hdiag p q hpq]
  have h := congrFun (congrFun (SymplecticGroup.mem_iff.mp hM) (Sum.inl i)) (Sum.inr i)
  rw [hMdiag] at h
  simp [Matrix.mul_apply, Matrix.J, Matrix.diagonal_apply] at h
  exact h

private lemma symplecticClosedPointMatrix_mem (m : ℕ)
    (g : Variety.Point
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety) :
    symplecticClosedPointMatrix m g ∈ Matrix.symplecticGroup (Fin m) k := by
  change symplecticMatrix m (standardSymplecticClosedSubgroupPoints m g).1 ∈
    Matrix.symplecticGroup (Fin m) k
  exact (mem_bilinearIsometrySubgroup_iff_symplecticMatrix m _).mp
    (standardSymplecticClosedSubgroupPoints m g).property

private lemma symplecticDiagonalTorus_mem_iff_diagonal (m : ℕ)
    (g : Variety.Point
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety) :
    g ∈ (symplecticDiagonalTorus (k := k) m).toSubgroup ↔
      ∀ p q, p ≠ q → symplecticClosedPointMatrix m g p q = 0 := by
  constructor
  · rintro ⟨x, rfl⟩ p q hpq
    rw [symplecticDiagonalMorphism_matrix, symplecticDiagonalMatrix,
      Matrix.diagonal_apply_ne _ hpq]
  · intro hdiag
    let M := symplecticClosedPointMatrix (k := k) m g
    have hpair (i : Fin m) :
        M (Sum.inl i) (Sum.inl i) * M (Sum.inr i) (Sum.inr i) = 1 :=
      diagonal_symplectic_pair_mul_eq_one m M hdiag
        (symplecticClosedPointMatrix_mem m g) i
    let z : Fin m → kˣ := fun i =>
      { val := M (Sum.inl i) (Sum.inl i)
        inv := M (Sum.inr i) (Sum.inr i)
        val_inv := hpair i
        inv_val := by rw [mul_comm, hpair i] }
    let x : Variety.Point (dVariety k m) := (dPointEquiv m).symm z
    apply (symplecticDiagonalTorus_mem_iff m g).mpr
    refine ⟨x, symplecticClosedPointMatrix_injective m ?_⟩
    rw [symplecticDiagonalMorphism_matrix]
    symm
    change M = symplecticDiagonalMatrix m x
    rw [symplecticDiagonalMatrix]
    ext p q
    by_cases hpq : p = q
    · subst q
      rw [Matrix.diagonal_apply_eq]
      cases p with
      | inl i =>
          rw [show dPointEquiv m x = z by
            exact (dPointEquiv m).apply_symm_apply z]
          rfl
      | inr i =>
          rw [show dPointEquiv m x = z by
            exact (dPointEquiv m).apply_symm_apply z]
          change M (Sum.inr i) (Sum.inr i) =
            (M (Sum.inl i) (Sum.inl i))⁻¹
          exact eq_inv_of_mul_eq_one_right (hpair i)
    · rw [Matrix.diagonal_apply_ne _ hpq]
      exact hdiag p q hpq

/-- A standard symplectic matrix centralizing every paired diagonal matrix is
itself paired diagonal. -/
public theorem symplecticDiagonalTorus_centralizer_eq (m : ℕ) :
    (symplecticDiagonalTorus (k := k) m).centralizer.toSubgroup =
      (symplecticDiagonalTorus (k := k) m).toSubgroup := by
  ext g
  constructor
  · intro hg
    apply (symplecticDiagonalTorus_mem_iff_diagonal m g).mpr
    intro p q hpq
    obtain ⟨x, hx⟩ := symplecticDiagonalEntries_separate (k := k) m hpq
    have htx : (symplecticDiagonalMorphism m).onPoints x ∈
        (symplecticDiagonalTorus m).toSubgroup := ⟨x, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hg _ htx
    have hmatrix := congrArg (symplecticClosedPointMatrix m) hcomm
    rw [symplecticClosedPointMatrix_mul, symplecticClosedPointMatrix_mul,
      symplecticDiagonalMorphism_matrix] at hmatrix
    have hentry := congrFun (congrFun hmatrix p) q
    rw [symplecticDiagonalMatrix, Matrix.diagonal_mul,
      Matrix.mul_diagonal] at hentry
    have hx' :
        (symplecticDiagonalEntries m x p : k) ≠
          (symplecticDiagonalEntries m x q : k) := by
      exact_mod_cast hx
    rw [symplecticDiagonalValue_point, symplecticDiagonalValue_point] at hentry
    have hfactor :
        ((symplecticDiagonalEntries m x p : k) -
            (symplecticDiagonalEntries m x q : k)) *
          symplecticClosedPointMatrix m g p q = 0 := by
      rw [sub_mul, mul_comm (symplecticDiagonalEntries m x q : k)]
      exact sub_eq_zero.mpr hentry
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hx')
  · intro hg
    change g ∈ Subgroup.centralizer
      ((symplecticDiagonalTorus (k := k) m).toSubgroup :
        Set (Variety.Point
          (standardSymplecticClosedSubgroup (k := k) m).carrierVariety))
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    let T := symplecticDiagonalTorus (k := k) m
    letI := T.carrierAlgebraicGroup
    let gt : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨g, hg⟩
    let tt : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨t, ht⟩
    have hcomm := symplecticDiagonalTorus_isSubtorus (k := k) m |>.isMulCommutative
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

/-- Every explicit symplectic root subgroup is normalized by the standard
paired diagonal torus. -/
public lemma symplecticRootSubgroup_invariant (m : ℕ)
    (r : TypeCRootIndex m) :
    IsClosedSubgroupInvariant (symplecticDiagonalTorus (k := k) m)
      (symplecticRootSubgroup (k := k) m r) := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  intro t ht x hx
  let s : Variety.Point (symplecticDiagonalTorus (k := k) m).carrierVariety :=
    (symplecticDiagonalTorus (k := k) m).pointEquiv.symm ⟨t, ht⟩
  have hs : (symplecticDiagonalTorus (k := k) m).includePoint s = t := by
    exact congrArg Subtype.val
      ((symplecticDiagonalTorus (k := k) m).pointEquiv.apply_symm_apply ⟨t, ht⟩)
  let z := symplecticDiagonalTorusPointEquiv (k := k) m s
  have hz : (symplecticDiagonalTorusIso (k := k) m).hom.onPoints z = s := by
    change (symplecticDiagonalTorusIso (k := k) m).hom.onPoints
        ((symplecticDiagonalTorusIso (k := k) m).inv.onPoints s) = s
    rw [(symplecticDiagonalTorusIso (k := k) m).inv_hom_id]
  have hi := symplecticDiagonalTorusIso_inclusion_hom (k := k) m z
  rw [hz] at hi
  have hdiag : symplecticClosedPointMatrix (k := k) m
      ((symplecticDiagonalTorus (k := k) m).includePoint s) =
      symplecticDiagonalMatrix (k := k) m z := by
    rw [show (symplecticDiagonalTorus (k := k) m).includePoint s =
        (symplecticDiagonalTorus (k := k) m).inclusion.onPoints s by rfl,
      hi, symplecticDiagonalMorphism_matrix]
  rw [← hs]
  exact symplecticRootSubgroup_conjugation_mem_of_diagonal
    (k := k) m r ((symplecticDiagonalTorus (k := k) m).includePoint s)
      z hdiag x hx

@[simp]
public theorem symplecticRootWeight_mem_torusRootSet
    (m : ℕ) (r : TypeCRootIndex m) :
    symplecticRootWeight (k := k) m r ∈
      TorusRootSet (symplecticDiagonalTorus (k := k) m) := by
  refine ⟨symplecticRootSubgroup (k := k) m r,
    ⟨symplecticRootSubgroup_invariant (k := k) m r,
      symplecticRootSubgroup_isOneParameter (k := k) m r⟩,
    symplecticRootWeight_equation (k := k) m r⟩

/-- The explicit type-C weights are precisely the torus-root characters of the
standard paired diagonal torus. -/
public theorem symplecticRootWeight_range (m : ℕ) :
    Set.range (symplecticRootWeight (k := k) m) =
      TorusRootSet (symplecticDiagonalTorus (k := k) m) := by
  apply Set.Subset.antisymm
  · rintro chi ⟨r, rfl⟩
    exact symplecticRootWeight_mem_torusRootSet m r
  · intro chi hchi
    rcases hchi with ⟨X, hX, hEq⟩
    letI := X.carrierAlgebraicGroup
    have hchine : chi ≠ 1 :=
      hX.rootWeight_ne_one_of_centralizer_eq
        (symplecticDiagonalTorus_isSubtorus (k := k) m)
        (symplecticDiagonalTorus_centralizer_eq (k := k) m) chi hEq
    let x : OneParameterParametrization X.carrierVariety := Classical.choice hX.2
    obtain ⟨r, hr⟩ := symplecticTangentWeight_eq_rootWeight m hchine
      (oneParameterTangent_isWeightVector
        (symplecticDiagonalTorus (k := k) m) X x hEq)
    exact ⟨r, hr.symm⟩

end Theory.AlgebraicGroup
