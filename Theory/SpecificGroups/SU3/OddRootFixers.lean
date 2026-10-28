module

public import Theory.SpecificGroups.SU3.OddRootFixers.FixedBlock
public import Theory.SpecificGroups.SU3.OddRootFixers.FieldElimination
public import Theory.SpecificGroups.SU3.OddRootFixers.TriangularConjugacy
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# From a marked diagonal unitary actor to its fixed PSL₂ subgroup

The graph-fixed block supplies an actual PSL₂(2ⁿ). Its center containment and
pointwise fixation are transported back through the specified automorphism.
Both SU₃ and its actual projective image are treated, retaining the special
scalar kernel and the two field cardinalities.

The exports with suffix `of_diagonal_form` are conditional reductions. The
`of_odd_root` exports below discharge their matrix normal-form premises by
combining the field-elimination and triangular-conjugacy modules. The
equivalence transport is also used by the arbitrary-cover adapter, with the
literal mapped Sylow center.

Source: GLS4, Chapter 4, Lemma 3.6(c,d), as used in Chapter 2, Lemma 13.2.
-/

public section
open Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddRootFixers
open BorelTorus

/-- Pull back an actual fixed subgroup, its equivalence and its marked containment. -/
theorem marked_fixed_subgroup_of_equiv
    {G H L : Type*} [Group G] [Group H] [Group L]
    (e : G ≃* H) (a : MulAut G) (R : Subgroup G)
    (I : Subgroup H) (eI : I ≃* L) (hR : R.map e.toMonoidHom ≤ I)
    (hfix : ∀ x ∈ I, MulAut.congr e a x = x) :
    ∃ K : Subgroup G, Nonempty (K ≃* L) ∧ R ≤ K ∧ ∀ x ∈ K, a x = x := by
  let K := I.map e.symm.toMonoidHom
  refine ⟨K, ⟨(I.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.trans eI⟩,
    ?_, ?_⟩
  · intro x hx
    exact ⟨e x, hR ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
  · rintro x ⟨y, hy, rfl⟩
    apply e.injective
    change e (a (e.symm y)) = e (e.symm y)
    rw [e.apply_symm_apply]
    exact hfix y hy

/-- Transport a marked Sylow-center conclusion across an actual group equivalence. -/
theorem sylow_fixed_subgroup_of_equiv
    {G H L : Type*} [Group G] [Finite G] [Group H] [Group L]
    (e : G ≃* H) (P : Sylow 2 G) (a : MulAut G)
    (h : ∃ I : Subgroup H, Nonempty (I ≃* L) ∧
      (center (P.mapSurjective (f := e.toMonoidHom) e.surjective)).map
        (P.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup H).subtype ≤ I ∧
      ∀ x ∈ I, MulAut.congr e a x = x) :
    ∃ I : Subgroup G, Nonempty (I ≃* L) ∧
      (center P).map (P : Subgroup G).subtype ≤ I ∧ ∀ x ∈ I, a x = x := by
  obtain ⟨I, ⟨eI⟩, hI, hfix⟩ := h
  apply marked_fixed_subgroup_of_equiv e a _ I eI _ hfix
  rw [map_embeddedCenter _ e.toMonoidHom e.injective]
  exact hI

/-- Transport pointwise fixation of the mapped Sylow center. -/
theorem fixes_sylow_center_congr
    {G H : Type*} [Group G] [Finite G] [Group H]
    (e : G ≃* H) (P : Sylow 2 G) (a : MulAut G)
    (hfix : ∀ x ∈ (center P).map (P : Subgroup G).subtype, a x = x) :
    ∀ x ∈ (center (P.mapSurjective (f := e.toMonoidHom) e.surjective)).map
      (P.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup H).subtype,
      MulAut.congr e a x = x := by
  change ∀ x ∈ (center ((P : Subgroup G).map e.toMonoidHom)).map
      ((P : Subgroup G).map e.toMonoidHom).subtype, _
  rw [← map_embeddedCenter _ e.toMonoidHom e.injective]
  rintro x ⟨y, hy, rfl⟩
  change e (a (e.symm (e y))) = e y
  rw [e.symm_apply_apply, hfix y hy]

variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)

include hcard in
private theorem binary_charTwo : CharP E 2 := by
  let := Fintype.ofFinite E
  apply charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
  simpa [Nat.card_eq_fintype_card, pow_mul] using hcard

include hn hcard hfixed in
/-- A diagonal matrix normal form supplies the marked PSL₂ inside SU₃ itself.
Existence of this form from odd order is not assumed implicitly. -/
theorem special_fixed_linear_of_diagonal_form
    (P : Sylow 2 J.specialSubgroup) (a : MulAut J.specialSubgroup)
    (hform : HasSpecialRootForm J hJ (IsRootDiagonal J) P a) :
    ∃ I : Subgroup J.specialSubgroup, Nonempty (I ≃* PSL2BinaryMatrixGroup n) ∧
      (center P).map (P : Subgroup J.specialSubgroup).subtype ≤ I ∧
      ∀ x ∈ I, a x = x := by
  let : CharP E 2 := binary_charTwo hcard
  obtain ⟨e, d, hd, hP, ha⟩ := hform
  apply marked_fixed_subgroup_of_equiv e a _ (specialGraphAut J hJ).fixedSubgroup
    (specialFixedEquivBinary J hJ hfixed) _ (diagonal_fixes_special J hJ d hd _ ha)
  rw [map_embeddedCenter _ e.toMonoidHom e.injective, hP]
  exact special_root_center_le_fixed J hJ hn hcard hfixed

include hn hcard hfixed in
/-- The same construction in the literal projective special unitary image. -/
theorem projective_fixed_linear_of_diagonal_form
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hform : HasProjectiveRootForm J hJ (IsRootDiagonal J) P a) :
    ∃ I : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      Nonempty (I ≃* PSL2BinaryMatrixGroup n) ∧
      (center P).map (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype ≤ I ∧
      ∀ x ∈ I, a x = x := by
  let : CharP E 2 := binary_charTwo hcard
  obtain ⟨e, d, hd, hP, ha⟩ := hform
  apply marked_fixed_subgroup_of_equiv e a _ (projectiveGraphAut J hJ).fixedSubgroup
    (projectiveFixedEquivBinary J hJ hfixed) _ ?_
  · rw [map_embeddedCenter _ e.toMonoidHom e.injective, hP]
    exact projective_root_center_le_fixed J hJ hn hcard hfixed
  · rw [ha]
    exact diagonal_fixes_projective J hJ d hd

include hJ hn hcard hfixed in
/-- Every odd-order projective unitary root fixer fixes a marked binary block. -/
theorem projective_fixed_linear_of_odd_root
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : Odd (orderOf a))
    (hfix : ∀ x ∈ (center P).map
      (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype, a x = x) :
    ∃ I : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      Nonempty (I ≃* PSL2BinaryMatrixGroup n) ∧
      (center P).map (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype ≤ I ∧
      ∀ x ∈ I, a x = x := by
  exact projective_fixed_linear_of_diagonal_form J hJ hn hcard hfixed P a
    (projective_diagonal_form_of_triangular J hJ hcard hfixed P a ha
      (projective_triangular_form J hJ hn hcard hfixed P a ha hfix))

include hJ hn hcard hfixed in
/-- Every odd-order special-unitary root fixer fixes a marked binary block. -/
theorem special_fixed_linear_of_odd_root
    (P : Sylow 2 J.specialSubgroup) (a : MulAut J.specialSubgroup)
    (ha : Odd (orderOf a))
    (hfix : ∀ x ∈ (center P).map (P : Subgroup J.specialSubgroup).subtype, a x = x) :
    ∃ I : Subgroup J.specialSubgroup, Nonempty (I ≃* PSL2BinaryMatrixGroup n) ∧
      (center P).map (P : Subgroup J.specialSubgroup).subtype ≤ I ∧
      ∀ x ∈ I, a x = x := by
  exact special_fixed_linear_of_diagonal_form J hJ hn hcard hfixed P a
    (special_diagonal_form_of_triangular J hJ hcard hfixed P a ha
      (special_triangular_form J hJ hn hcard hfixed P a ha hfix))

end BenderSuzuki.MatrixGroups.HermitianForm.OddRootFixers
