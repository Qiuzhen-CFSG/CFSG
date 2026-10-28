module

public import Theory.SpecificGroups.SU3.SylowPointwiseInner
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.DiagonalActors
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.GroupAction.SylowPointwiseInnerTransport

/-!
# Full Sylow pointwise innerness in binary PSU₃

Pointwise fixation of the root detects the field parameter. A unitary root
fixer is triangular, and the first root coordinate forces its three diagonal
entries to agree. In its root-times-diagonal factorization the diagonal factor
is consequently scalar. Thus the actor is conjugation by a root element.
This includes diagonal actors of odd order and the Hermitian field actor;
there is no hypothesis on the order of the automorphism.

Sylow conjugacy and an actual Hermitian basis change give arbitrary Sylows
and arbitrary nondegenerate forms, retaining the conjugating element in the
specified Sylow subgroup. Simplicity is inherited from the component caller.

Sources: Huppert II.10.12; GLS3, Theorem 2.5.12 and §2.7; the characteristic-two
Sylow-centralizer assertion in Aschbacher–Smith, B.1.13, printed pp.73–74.
-/

public section

open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.SylowPointwiseInner
open OddPrimeSylow.NormalizedOuter.Coverage BorelTorus.SemilinearActors
variable {E : Type*} [Field E] [Finite E] [CharP E 2]

omit [Finite E] [CharP E 2] in
private theorem commute_of_projective (A X : GL (Fin 3) E)
    (hX : X.val.trace = 1)
    (h : ProjGenLinGroup.mk (A * X * A⁻¹) = ProjGenLinGroup.mk X) :
    A.val * X.val = X.val * A.val := by
  obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  have ht := congrArg (fun B : GL (Fin 3) E => B.val.trace) hc
  have hm : ((A * X * A⁻¹) * GeneralLinearGroup.scalar (Fin 3) c).val =
      (c : E) • (A.val * X.val * (A⁻¹).val) := by
    ext i j
    simp [GeneralLinearGroup.coe_scalar, Matrix.mul_diagonal, mul_comm]
  rw [hm, trace_smul, trace_units_conj, hX, smul_eq_mul, mul_one] at ht
  have hc1 : c = 1 := Units.ext ht
  rw [hc1, map_one, mul_one] at hc
  exact congrArg Units.val (mul_inv_eq_iff_eq_mul.mp hc)

/-- A unitary root fixer has the same projective class as a root matrix. -/
theorem unitary_fixing_root_eq_root_conj
    (J : HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (u : J.unitarySubgroup)
    (hfix : ∀ z : hermitianUnipotentCoord J,
      J.unitaryConj u (root J hJ z) = root J hJ z) :
    ∃ z : hermitianUnipotentCoord J,
      J.unitaryConj u = MulAut.conj (root J hJ z) := by
  have hinter : ∀ t : hermitianUnipotentCoord J,
      ∃ z : hermitianUnipotentCoord J,
        ProjGenLinGroup.mk (u.val * hermitianUnipotentGL J z) =
          ProjGenLinGroup.mk (hermitianUnipotentGL J t * u.val) := by
    intro t
    refine ⟨t, ?_⟩
    have he := congrArg Subtype.val (hfix t)
    simp only [unitaryConj_apply_val, root, hermitianUnipotentPSU_val] at he
    simpa only [map_mul] using mul_inv_eq_iff_eq_mul.mp he
  obtain ⟨h10, h20, h21⟩ := unitary_upper_of_root_intertwining J hJ hcard hfixed u hinter
  have hmat (z : hermitianUnipotentCoord J) :
      u.val.val * (hermitianUnipotentGL J z).val =
        (hermitianUnipotentGL J z).val * u.val.val := by
    apply commute_of_projective u.val (hermitianUnipotentGL J z)
    · simp [hermitianUnipotentGL, hermitianUnipotentMatrix, Matrix.trace,
        Fin.sum_univ_three, CharTwo.add_self_eq_zero]
    · simpa only [map_mul, map_inv, unitaryConj_apply_val, root,
        hermitianUnipotentPSU_val] using congrArg Subtype.val (hfix z)
  obtain ⟨z1, hz1⟩ := EvenSemilinear.coord_first_surjective J hcard hfixed 1
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 1) (hmat z1)
  have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 1 2) (hmat z1)
  simp [hermitianUnipotentMatrix, Matrix.mul_apply, Fin.sum_univ_three,
    h10, h21, hz1, CharTwo.neg_eq] at h01 h12
  have hd01 : u.val.val 0 0 = u.val.val 1 1 := by linear_combination h01
  have hd12 : u.val.val 1 1 = u.val.val 2 2 := by linear_combination h12
  obtain ⟨z, d, hf, hd, _⟩ := upper_unitary_factorization J hJ u h10 h20 h21
  have hdiag (i : Fin 3) : u.val.val i i = d.val.val i i := by
    have hi := congrArg (fun A : GL (Fin 3) E => A.val i i) hf
    fin_cases i <;>
      simpa [hermitianUnipotentMatrix, Matrix.mul_apply, Fin.sum_univ_three, hd] using hi
  have hdeq : ∀ i : Fin 3, d.val.val i i = d.val.val 0 0 := by
    intro i
    rw [← hdiag i, ← hdiag 0]
    fin_cases i
    · rfl
    · exact hd01.symm
    · exact (hd01.trans hd12).symm
  have hd0 : d.val.val 0 0 ≠ 0 := by
    intro h
    have hz : d.val.val = 0 := by
      ext i j
      by_cases hij : i = j
      · subst j
        simpa using (hdeq i).trans h
      · simpa using hd i j hij
    have hdet := d.val.det_ne_zero
    simp [hz] at hdet
  have hscalar : d.val = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (d.val.val 0 0) hd0) := by
    apply Units.ext
    ext i j
    by_cases hij : i = j
    · subst j
      simpa [GeneralLinearGroup.coe_scalar] using hdeq i
    · simp [GeneralLinearGroup.coe_scalar, hd i j hij, hij]
  have hdproj : ProjGenLinGroup.mk d.val = 1 := by
    rw [hscalar]
    exact ProjGenLinGroup.mk_eq_one.mpr
      (GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨_, rfl⟩)
  have hu : ProjGenLinGroup.mk u.val = ProjGenLinGroup.mk (hermitianUnipotentGL J z) := by
    rw [hf, map_mul, hdproj, mul_one]
  refine ⟨z, ?_⟩
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  simp only [unitaryConj_apply_val, MulAut.conj_apply, Subgroup.coe_mul,
    Subgroup.coe_inv, root, hermitianUnipotentPSU_val, hu]

/-- Every root fixer is conjugation by an element of the root group. -/
theorem fixing_root_eq_root_conj
    (J : HermitianForm 3 E)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hfix : ∀ z : hermitianUnipotentCoord J,
      a (root J hJ z) = root J hJ z) :
    ∃ z : hermitianUnipotentCoord J, a = MulAut.conj (root J hJ z) := by
  obtain ⟨σ, hσ⟩ := EvenSemilinear.semilinear_coverage J hJ hn hcard hconj a
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  have he := semilinear_fixing_root_field_eq_one J hJ hcard hfixed a σ hσ hfix
  rw [he] at hσ
  obtain ⟨u, rfl⟩ := (HasUnitarySemilinearForm.one_iff J).mp hσ
  exact unitary_fixing_root_eq_root_conj J hJ hcard hfixed u hfix

/-- The full pointwise fixer of any Sylow on the standard form is Sylow-inner. -/
theorem fixing_sylow_eq_mem_conj_standard
    (J : HermitianForm 3 E)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hfix : ∀ x ∈ S, a x = x) : ∃ x ∈ S, a = MulAut.conj x := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  let P := EvenTwoRank.rootSylow J hJ (by omega) hcard hfixed
  apply MulAut.fixing_inner_sylow P S _ a hfix
  intro b hb
  obtain ⟨z, hz⟩ := fixing_root_eq_root_conj J hJ hn hcard hconj b
    (fun z => hb (root J hJ z) ⟨z, rfl⟩)
  exact ⟨root J hJ z, ⟨z, rfl⟩, hz⟩

omit [CharP E 2] in
/-- Arbitrary Hermitian forms and arbitrary automorphism orders are allowed. -/
theorem fixing_sylow_eq_mem_conj
    (J : HermitianForm 3 E)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hfix : ∀ x ∈ S, a x = x) : ∃ x ∈ S, a = MulAut.conj x := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
    (by simpa only [Nat.card_eq_fintype_card, pow_mul] using hcard)
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  obtain ⟨e⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2 ^ n) hcard hfixed
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup
      (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J)) := e.symm.isSimpleGroup
  apply MulAut.fixing_sylow_inner_of_equiv e _ S a hfix
  exact fixing_sylow_eq_mem_conj_standard _ rfl hn hcard hconj

end BenderSuzuki.MatrixGroups.HermitianForm.SylowPointwiseInner
