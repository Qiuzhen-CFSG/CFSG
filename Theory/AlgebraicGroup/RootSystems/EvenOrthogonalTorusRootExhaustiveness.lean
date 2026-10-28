module

public import Theory.AlgebraicGroup.RootSystems.EvenOrthogonalTangentWeightSupport
public import Theory.AlgebraicGroup.RootSubgroups.NormalizerMembership

/-!
# Exhaustiveness of the split even-orthogonal torus roots

For hyperbolic rank `n >= 4`, this module proves that the diagonal torus in
split `Omega_{2n}` is self-centralizing and hence maximal.  The centralizer
calculation uses the natural hyperbolic basis: its `2n` diagonal characters
are the distinct Laurent monomials `e_i` and `-e_i`, so a commuting matrix is
diagonal.  Preservation of the hyperbolic quadratic form then pairs its two
diagonal entries at each index as mutual inverses.

The explicit type-D one-parameter subgroups are invariant under this torus,
and `evenOrthogonalRootWeight_equation` supplies their characters.  Combined
with the characteristic-free identity-tangent weight classification, this
identifies the range of `evenOrthogonalRootWeight` with the full
`TorusRootSet`.  These direct calculations are the standard split type-D root
construction underlying GLS, Part I, Chapter A, Sections 1.9--1.10; no
classification of type-D versions is used.
-/

open Set

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

open StandardRootSystem

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

private abbrev evenOrthogonalStandardIndex (n : Nat) := Sum (Fin n) (Fin n)

private noncomputable def evenOrthogonalNaturalBasis (n : Nat) :
    Module.Basis (evenOrthogonalStandardIndex n) k (HyperbolicSpace k n) :=
  (Pi.basisFun k (Fin n)).prod (Pi.basisFun k (Fin n))

private noncomputable def evenOrthogonalDiagonalEntryExponent (n : Nat) :
    evenOrthogonalStandardIndex n → Fin n → ℤ
  | Sum.inl i => Pi.single i 1
  | Sum.inr i => Pi.single i (-1)

private lemma evenOrthogonalDiagonalEntryExponent_injective (n : Nat) :
    Function.Injective (evenOrthogonalDiagonalEntryExponent n) := by
  classical
  intro p q hpq
  cases p with
  | inl i =>
      cases q with
      | inl j =>
          congr 1
          by_contra hij
          have h := congrFun hpq i
          simp [evenOrthogonalDiagonalEntryExponent, hij] at h
      | inr j =>
          have h := congrFun hpq i
          by_cases hij : i = j <;>
            simp [evenOrthogonalDiagonalEntryExponent, hij] at h
  | inr i =>
      cases q with
      | inl j =>
          have h := congrFun hpq i
          by_cases hij : i = j <;>
            simp [evenOrthogonalDiagonalEntryExponent, hij] at h
      | inr j =>
          congr 1
          by_contra hij
          have h := congrFun hpq i
          simp [evenOrthogonalDiagonalEntryExponent, hij] at h

private noncomputable def evenOrthogonalDiagonalEntry (n : Nat)
    (x : Variety.Point (dVariety k n)) : evenOrthogonalStandardIndex n → kˣ
  | Sum.inl i => dPointEquiv n x i
  | Sum.inr i => (dPointEquiv n x i)⁻¹

private def hyperbolicDiagonalScalar (n : Nat) (d : Fin n → kˣ) :
    evenOrthogonalStandardIndex n → k
  | Sum.inl i => d i
  | Sum.inr i => ↑((d i)⁻¹)

omit [IsAlgClosed k] in
private lemma evenOrthogonalDiagonalEntryExponent_apply (n : Nat)
    (x : Variety.Point (dVariety k n)) (p : evenOrthogonalStandardIndex n) :
    dPointEquiv 1
        ((dLaurentCharacter n (evenOrthogonalDiagonalEntryExponent n p)).onPoints x) 0 =
      evenOrthogonalDiagonalEntry n x p := by
  classical
  cases p with
  | inl i =>
      rw [dLaurentCharacter_apply]
      simp [evenOrthogonalDiagonalEntryExponent, evenOrthogonalDiagonalEntry,
        Pi.single_apply]
  | inr i =>
      rw [dLaurentCharacter_apply]
      simp [evenOrthogonalDiagonalEntryExponent, evenOrthogonalDiagonalEntry,
        Pi.single_apply]

private lemma evenOrthogonalDiagonalEntries_separate (n : Nat)
    {p q : evenOrthogonalStandardIndex n} (hpq : p ≠ q) :
    ∃ x : Variety.Point (dVariety k n),
      evenOrthogonalDiagonalEntry n x p ≠ evenOrthogonalDiagonalEntry n x q := by
  classical
  by_contra hnone
  push Not at hnone
  have hchars :
      dLaurentCharacter (k := k) n (evenOrthogonalDiagonalEntryExponent n p) =
        dLaurentCharacter n (evenOrthogonalDiagonalEntryExponent n q) := by
    apply AlgebraicGroup.Morphism.ext
    funext x
    apply (dPointEquiv 1).injective
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact (evenOrthogonalDiagonalEntryExponent_apply n x p).trans
      ((hnone x).trans (evenOrthogonalDiagonalEntryExponent_apply n x q).symm)
  have hexp := dLaurentCharacter_injective (k := k) n hchars
  exact hpq (evenOrthogonalDiagonalEntryExponent_injective n hexp)

omit [IsAlgClosed k] in
private lemma hyperbolicDiagonalPoint_toMatrix (n : Nat) (d : Fin n → kˣ) :
    LinearMap.toMatrix (evenOrthogonalNaturalBasis (k := k) n)
        (evenOrthogonalNaturalBasis (k := k) n)
        (hyperbolicDiagonalPoint n d).1.toLinearMap =
      Matrix.diagonal (hyperbolicDiagonalScalar n d) := by
  classical
  ext p q
  cases p <;> cases q <;>
    simp [LinearMap.toMatrix_apply, evenOrthogonalNaturalBasis,
      hyperbolicDiagonalPoint, hyperbolicDiagonalIsometry,
      hyperbolicDiagonalLinearEquiv, hyperbolicDiagonalScalar,
      Matrix.diagonal_apply, Pi.single_apply]

private noncomputable def evenOrthogonalPointLinear (n : Nat) (hn : 4 ≤ n)
    (g : Variety.Point
      (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
        (standardHyperbolicSplit n)).carrierVariety) :
    HyperbolicSpace k n ≃ₗ[k] HyperbolicSpace k n :=
  (evenSpinActionImageClosedSubgroupPoints
    (hyperbolicForm (k := k) n) (standardHyperbolicSplit n) (by simpa using hn) g).1.1

private noncomputable def evenOrthogonalPointMatrix (n : Nat) (hn : 4 ≤ n)
    (g : Variety.Point
      (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
        (standardHyperbolicSplit n)).carrierVariety) :
    Matrix (evenOrthogonalStandardIndex n) (evenOrthogonalStandardIndex n) k :=
  LinearMap.toMatrix (evenOrthogonalNaturalBasis (k := k) n)
    (evenOrthogonalNaturalBasis (k := k) n) (evenOrthogonalPointLinear n hn g).toLinearMap

private lemma evenOrthogonalPointMatrix_injective (n : Nat) (hn : 4 ≤ n) :
    Function.Injective (evenOrthogonalPointMatrix (k := k) n hn) := by
  intro g h hgh
  have hlinear : (evenOrthogonalPointLinear n hn g).toLinearMap =
      (evenOrthogonalPointLinear n hn h).toLinearMap :=
    (LinearMap.toMatrix
      (evenOrthogonalNaturalBasis (k := k) n)
      (evenOrthogonalNaturalBasis (k := k) n)).injective hgh
  have hequiv : evenOrthogonalPointLinear n hn g =
      evenOrthogonalPointLinear n hn h :=
    LinearEquiv.toLinearMap_injective hlinear
  apply (evenSpinActionImageClosedSubgroupPoints
    (hyperbolicForm (k := k) n) (standardHyperbolicSplit n)
      (by simpa using hn)).injective
  exact Subtype.ext (Subtype.ext hequiv)

private lemma evenOrthogonalPointMatrix_mul (n : Nat) (hn : 4 ≤ n)
    (g h : Variety.Point
      (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
        (standardHyperbolicSplit n)).carrierVariety) :
    evenOrthogonalPointMatrix n hn (g * h) =
      evenOrthogonalPointMatrix n hn g * evenOrthogonalPointMatrix n hn h := by
  rw [evenOrthogonalPointMatrix, evenOrthogonalPointMatrix,
    evenOrthogonalPointMatrix, evenOrthogonalPointLinear,
    evenOrthogonalPointLinear, evenOrthogonalPointLinear, map_mul]
  exact LinearMap.toMatrix_comp _ _ _ _ _

private lemma evenOrthogonalDiagonalMorphism_matrix (n : Nat) (hn : 4 ≤ n)
    (x : Variety.Point (dVariety k n)) :
    evenOrthogonalPointMatrix n hn ((evenOrthogonalDiagonalMorphism n hn).onPoints x) =
      Matrix.diagonal (fun p => (evenOrthogonalDiagonalEntry n x p : k)) := by
  have hpoint := evenSpinActionImageClosedSubgroup_linear_points
    (hyperbolicForm (k := k) n) (standardHyperbolicSplit n)
      (by simpa using hn) ((evenOrthogonalDiagonalMorphism n hn).onPoints x)
  have hdiag := evenOrthogonalDiagonalMorphism_linear_points (k := k) n hn x
  have heq : evenOrthogonalPointLinear n hn
        ((evenOrthogonalDiagonalMorphism n hn).onPoints x) =
      (hyperbolicDiagonalPoint n (dPointEquiv n x)).1 := hpoint.symm.trans hdiag
  rw [evenOrthogonalPointMatrix, heq, hyperbolicDiagonalPoint_toMatrix]
  congr 1
  funext p
  cases p <;> rfl

private lemma evenOrthogonalPointLinear_preserves_hyperbolicForm
    (n : Nat) (hn : 4 ≤ n)
    (g : Variety.Point
      (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
        (standardHyperbolicSplit n)).carrierVariety)
    (v : HyperbolicSpace k n) :
    hyperbolicForm n (evenOrthogonalPointLinear n hn g v) =
      hyperbolicForm n v :=
  (mem_quadraticIsometrySubgroup _ _).mp
    (evenSpinActionImageClosedSubgroupPoints
      (hyperbolicForm (k := k) n) (standardHyperbolicSplit n)
        (by simpa using hn) g).1.2 v

private lemma evenOrthogonalPointLinear_apply_basis (n : Nat) (hn : 4 ≤ n)
    (g : Variety.Point
      (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
        (standardHyperbolicSplit n)).carrierVariety)
    (p : evenOrthogonalStandardIndex n) :
    evenOrthogonalPointLinear n hn g (evenOrthogonalNaturalBasis n p) =
      ∑ q, evenOrthogonalPointMatrix n hn g q p •
        evenOrthogonalNaturalBasis n q := by
  have h := Matrix.toLin_self
    (evenOrthogonalNaturalBasis (k := k) n)
    (evenOrthogonalNaturalBasis (k := k) n)
    (evenOrthogonalPointMatrix n hn g) p
  rw [evenOrthogonalPointMatrix, Matrix.toLin_toMatrix] at h
  exact h

private lemma diagonal_evenOrthogonal_pair_mul_eq_one (n : Nat) (hn : 4 ≤ n)
    (g : Variety.Point
      (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
        (standardHyperbolicSplit n)).carrierVariety)
    (hdiag : ∀ p q, p ≠ q → evenOrthogonalPointMatrix n hn g p q = 0)
    (i : Fin n) :
    evenOrthogonalPointMatrix n hn g (Sum.inl i) (Sum.inl i) *
        evenOrthogonalPointMatrix n hn g (Sum.inr i) (Sum.inr i) = 1 := by
  classical
  let b := evenOrthogonalNaturalBasis (k := k) n
  let M := evenOrthogonalPointMatrix n hn g
  have hMdiag : M = Matrix.diagonal (fun p => M p p) := by
    ext p q
    by_cases hpq : p = q
    · subst q
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hpq]
      change evenOrthogonalPointMatrix n hn g p q = 0
      exact hdiag p q hpq
  have hu := evenOrthogonalPointLinear_apply_basis (k := k) n hn g (Sum.inl i)
  have hl := evenOrthogonalPointLinear_apply_basis (k := k) n hn g (Sum.inr i)
  rw [show evenOrthogonalPointMatrix n hn g = M by rfl, hMdiag] at hu hl
  simp only [Matrix.diagonal_apply] at hu hl
  simp only [M] at hu hl
  have hpres := evenOrthogonalPointLinear_preserves_hyperbolicForm
    (k := k) n hn g (b (Sum.inl i) + b (Sum.inr i))
  rw [map_add, hu, hl] at hpres
  simpa [b, evenOrthogonalNaturalBasis, Pi.basisFun_apply,
    hyperbolicForm_apply, Pi.single_apply] using hpres

private lemma evenOrthogonalDiagonalTorus_mem_iff_diagonal
    (n : Nat) (hn : 4 ≤ n)
    (g : Variety.Point
      (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
        (standardHyperbolicSplit n)).carrierVariety) :
    g ∈ (evenOrthogonalDiagonalTorus (k := k) n hn).toSubgroup ↔
      ∀ p q, p ≠ q → evenOrthogonalPointMatrix n hn g p q = 0 := by
  constructor
  · rintro ⟨x, rfl⟩ p q hpq
    rw [evenOrthogonalDiagonalMorphism_matrix,
      Matrix.diagonal_apply_ne _ hpq]
  · intro hdiag
    let M := evenOrthogonalPointMatrix (k := k) n hn g
    have hpair (i : Fin n) :
        M (Sum.inl i) (Sum.inl i) * M (Sum.inr i) (Sum.inr i) = 1 :=
      diagonal_evenOrthogonal_pair_mul_eq_one n hn g hdiag i
    let d : Fin n → kˣ := fun i =>
      { val := M (Sum.inl i) (Sum.inl i)
        inv := M (Sum.inr i) (Sum.inr i)
        val_inv := hpair i
        inv_val := by rw [mul_comm, hpair i] }
    let x : Variety.Point (dVariety k n) := (dPointEquiv n).symm d
    refine ⟨x, evenOrthogonalPointMatrix_injective n hn ?_⟩
    rw [evenOrthogonalDiagonalMorphism_matrix]
    ext p q
    by_cases hpq : p = q
    · subst q
      rw [Matrix.diagonal_apply_eq]
      cases p with
      | inl i =>
          change M (Sum.inl i) (Sum.inl i) =
            (evenOrthogonalDiagonalEntry n x (Sum.inl i) : k)
          rw [evenOrthogonalDiagonalEntry]
          rw [show dPointEquiv n x = d by exact (dPointEquiv n).apply_symm_apply d]
      | inr i =>
          change M (Sum.inr i) (Sum.inr i) =
            (evenOrthogonalDiagonalEntry n x (Sum.inr i) : k)
          rw [evenOrthogonalDiagonalEntry]
          rw [show dPointEquiv n x = d by exact (dPointEquiv n).apply_symm_apply d]
          rfl
    · rw [Matrix.diagonal_apply_ne _ hpq]
      exact (hdiag p q hpq).symm

public theorem evenOrthogonalDiagonalTorus_centralizer_eq
    (n : Nat) (hn : 4 ≤ n) :
    (evenOrthogonalDiagonalTorus (k := k) n hn).centralizer.toSubgroup =
      (evenOrthogonalDiagonalTorus (k := k) n hn).toSubgroup := by
  ext g
  constructor
  · intro hg
    apply (evenOrthogonalDiagonalTorus_mem_iff_diagonal n hn g).mpr
    intro p q hpq
    obtain ⟨x, hx⟩ := evenOrthogonalDiagonalEntries_separate (k := k) n hpq
    have htx : (evenOrthogonalDiagonalMorphism n hn).onPoints x ∈
        (evenOrthogonalDiagonalTorus n hn).toSubgroup := ⟨x, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hg _ htx
    have hmatrix := congrArg (evenOrthogonalPointMatrix n hn) hcomm
    rw [evenOrthogonalPointMatrix_mul, evenOrthogonalPointMatrix_mul,
      evenOrthogonalDiagonalMorphism_matrix] at hmatrix
    have hentry := congrFun (congrFun hmatrix p) q
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
    have hx' : (evenOrthogonalDiagonalEntry n x p : k) ≠
        (evenOrthogonalDiagonalEntry n x q : k) := by
      exact_mod_cast hx
    have hfactor :
        ((evenOrthogonalDiagonalEntry n x p : k) -
            (evenOrthogonalDiagonalEntry n x q : k)) *
          evenOrthogonalPointMatrix n hn g p q = 0 := by
      rw [sub_mul, mul_comm (evenOrthogonalDiagonalEntry n x q : k)]
      exact sub_eq_zero.mpr hentry
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hx')
  · intro hg
    change g ∈ Subgroup.centralizer
      ((evenOrthogonalDiagonalTorus (k := k) n hn).toSubgroup :
        Set (Variety.Point
          (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
            (standardHyperbolicSplit n)).carrierVariety))
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    let T := evenOrthogonalDiagonalTorus (k := k) n hn
    letI := T.carrierAlgebraicGroup
    let gt : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨g, hg⟩
    let tt : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨t, ht⟩
    have hcomm := evenOrthogonalDiagonalTorus_isSubtorus (k := k) n hn
      |>.isMulCommutative
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

public theorem evenOrthogonalDiagonalTorus_isMaximalTorus
    (n : Nat) (hn : 4 ≤ n) :
    IsMaximalTorus (evenOrthogonalDiagonalTorus (k := k) n hn) := by
  refine ⟨evenOrthogonalDiagonalTorus_isSubtorus n hn, ?_⟩
  intro S hS hTS
  apply SetLike.coe_injective
  apply Set.Subset.antisymm
  · intro g hg
    have hgcentral : g ∈ Subgroup.centralizer
        ((evenOrthogonalDiagonalTorus (k := k) n hn).toSubgroup :
          Set (Variety.Point
            (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
              (standardHyperbolicSplit n)).carrierVariety)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      letI := S.carrierAlgebraicGroup
      let gs : Variety.Point S.carrierVariety := S.pointEquiv.symm ⟨g, hg⟩
      let ts : Variety.Point S.carrierVariety := S.pointEquiv.symm ⟨t, hTS ht⟩
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
          (evenOrthogonalDiagonalTorus (k := k) n hn) := hgcentral
    change g ∈ (evenOrthogonalDiagonalTorus (k := k) n hn).centralizer.toSubgroup
      at hgclosed
    rw [evenOrthogonalDiagonalTorus_centralizer_eq (k := k) n hn] at hgclosed
    exact hgclosed
  · exact hTS

public lemma evenOrthogonalRootSubgroup_invariant
    (n : Nat) (hn : 4 ≤ n) (r : TypeDRootIndex n) :
    IsClosedSubgroupInvariant (evenOrthogonalDiagonalTorus (k := k) n hn)
      (evenOrthogonalRootSubgroup (k := k) n hn r) := by
  let T := evenOrthogonalDiagonalTorus (k := k) n hn
  let X := evenOrthogonalRootSubgroup (k := k) n hn r
  letI := T.carrierAlgebraicGroup
  letI := X.carrierAlgebraicGroup
  intro t ht x hx
  let s : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨t, ht⟩
  let xX : Variety.Point X.carrierVariety := X.pointEquiv.symm ⟨x, hx⟩
  let p : OneParameterParametrization X.carrierVariety :=
    evenOrthogonalRootParametrization n hn r
  let q : Variety.Point (KPlus k) := p.inv.onPoints xX
  let a : k := Multiplicative.toAdd (additiveGroupPointEquiv k q)
  have hqa : kPlusPoint a = q := by
    apply (additiveGroupPointEquiv k).injective
    exact Multiplicative.ofAdd.apply_symm_apply (additiveGroupPointEquiv k q)
  have hxa : X.includePoint (p.value a) = x := by
    change (X.pointEquiv (p.hom.onPoints (kPlusPoint a))).val = x
    rw [hqa, p.inv_hom_id]
    exact congrArg Subtype.val (X.pointEquiv.apply_symm_apply ⟨x, hx⟩)
  have hs : T.includePoint s = t := by
    exact congrArg Subtype.val (T.pointEquiv.apply_symm_apply ⟨t, ht⟩)
  have heq := evenOrthogonalRootWeight_equation (k := k) n hn r p a s
  rw [hs, hxa] at heq
  rw [heq]
  exact (X.pointEquiv (p.value
    ((evenOrthogonalRootWeight n hn r).pointCharacter s * a))).property

@[simp]
public theorem evenOrthogonalRootWeight_mem_torusRootSet
    (n : Nat) (hn : 4 ≤ n) (r : TypeDRootIndex n) :
    evenOrthogonalRootWeight (k := k) n hn r ∈
      TorusRootSet (evenOrthogonalDiagonalTorus (k := k) n hn) := by
  refine ⟨evenOrthogonalRootSubgroup (k := k) n hn r,
    ⟨evenOrthogonalRootSubgroup_invariant (k := k) n hn r,
      evenOrthogonalRootSubgroup_isOneParameter (k := k) n hn r⟩,
    evenOrthogonalRootWeight_equation (k := k) n hn r⟩

/-- The explicit type-D weights are precisely the torus-root characters of the
standard even-orthogonal diagonal torus. -/
public theorem evenOrthogonalRootWeight_range (n : Nat) (hn : 4 ≤ n) :
    Set.range (evenOrthogonalRootWeight (k := k) n hn) =
      TorusRootSet (evenOrthogonalDiagonalTorus (k := k) n hn) := by
  apply Set.Subset.antisymm
  · rintro chi ⟨r, rfl⟩
    exact evenOrthogonalRootWeight_mem_torusRootSet n hn r
  · intro chi hchi
    rcases hchi with ⟨X, hX, hEq⟩
    letI := X.carrierAlgebraicGroup
    have hchine : chi ≠ 1 :=
      hX.rootWeight_ne_one_of_centralizer_eq
        (evenOrthogonalDiagonalTorus_isSubtorus (k := k) n hn)
        (evenOrthogonalDiagonalTorus_centralizer_eq (k := k) n hn) chi hEq
    let x : OneParameterParametrization X.carrierVariety := Classical.choice hX.2
    obtain ⟨r, hr⟩ := evenOrthogonalTangentWeight_eq_rootWeight n hn hchine
      (oneParameterTangent_isWeightVector
        (evenOrthogonalDiagonalTorus (k := k) n hn) X x hEq)
    exact ⟨r, hr.symm⟩

end Theory.AlgebraicGroup
