module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourOrbits
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourPlacement

/-!
# The two plane-core orbits in the projective unitary-four amalgam

SL₂ congruence takes every nonzero Hermitian parameter to diag(1, det X).
The literal special-unitary torus diag(1,s,s⁻¹,1), with s in the fixed
field, scales the second diagonal parameter by s². Fixed-field Frobenius
therefore fuses all nonzero determinant fibers. Projectivization and the
actual two-core parametrization give two representatives in the native
plane core, with every conjugator in the full plane parabolic.

The final transport theorem uses an actual endpoint equivalence and its
intrinsic two-core map. It is applied to the original prepared residual in
the Chapter6 companion. Nonfusion in the ambient G uses Thompson control
separately; no full-normalizer realization is assumed here.

Source: Aschbacher–Smith F.4.27(3), F.4.30 and F.4.35, printed
pp.288–292 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Matrix BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.UnitarySource.FourOrbits
open GreenBook.LieModels.UnitaryFour
open Representation.OrthogonalFourMinus Representation.OrthogonalFourMinus.FiniteModel
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical
open Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourOrbits
variable (m : ℕ) (hm : 1 ≤ m) [NeZero m]

private def element (X : Space m) : ProjectiveGroup m hm :=
  ((L2TwoCoreEquiv m hm (Multiplicative.ofAdd X)).val : ProjectiveGroup m hm)

private theorem element_eq (X : Space m) : element m hm X =
    projection m hm (unipotentSU (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)
      ((planeHermitianEquiv m).symm X)) := rfl

private theorem element_injective : Function.Injective (element m hm) := by
  intro X Y h
  apply Multiplicative.ofAdd.injective
  apply (L2TwoCoreEquiv m hm).injective
  exact Subtype.ext (Subtype.ext h)

private theorem element_zero : element m hm 0 = 1 := by
  change (((L2TwoCoreEquiv m hm) 1).val : ProjectiveGroup m hm) = 1
  rw [map_one]
  rfl

private theorem element_conj (g : L2 m hm) (X : Space m) :
    (g : ProjectiveGroup m hm) * element m hm X * (g : ProjectiveGroup m hm)⁻¹ =
      element m hm (action m (L2QuotientEquivSL2 m hm (QuotientGroup.mk g)) X) :=
  congrArg (fun x : pCore 2 (L2 m hm) => (x.val : ProjectiveGroup m hm))
    (L2TwoCoreEquiv_conj m hm g (Multiplicative.ofAdd X))

private theorem element_normalize (X : Space m) (hX : X ≠ 0) :
    ∃ g ∈ planeParabolic m hm,
      g * element m hm X * g⁻¹ = element m hm (representative m (form m X)) := by
  obtain ⟨A,hA⟩ := normalize m X hX
  let g := L2Levi m hm ((planeSL2Equiv m).symm A)
  refine ⟨g,(L2_le_planeParabolic m hm) g.property,?_⟩
  rw [element_conj,L2QuotientEquivSL2_mk]
  change element m hm (action m (planeSL2Equiv m
    (L2Restriction m hm (L2Levi m hm ((planeSL2Equiv m).symm A)))) X) = _
  rw [L2Restriction_levi,MulEquiv.apply_symm_apply,hA]

private def torus (s : FixedBy.subfield (MatrixField m) (fieldConj m)) (hs : s ≠ 0) :
    planeParabolicMatrix m hm := by
  let a : MatrixField m := s
  have ha : a ≠ 0 := fun he => hs (Subtype.ext he)
  have hsa : fieldConj m a = a := s.property
  let d : Fin 4 → MatrixField m := ![1,a,a⁻¹,1]
  have hd : (Matrix.diagonal d).det = 1 := by
    rw [Matrix.det_diagonal]
    simp [d,Fin.prod_univ_succ,ha]
  let g : MatrixGroup m hm :=
    ⟨GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal d) (by rw [hd]; exact one_ne_zero),
      by
        change (UnitaryFourFlag.form (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)).conjTranspose
          (Matrix.diagonal d) * gram (MatrixField m) * Matrix.diagonal d = gram (MatrixField m)
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [UnitaryFourFlag.form,gram,HermitianForm.conjTranspose,Matrix.mul_apply,
            Fin.sum_univ_succ,d,ha,hsa],
      Units.ext hd⟩
  exact ⟨g,(mem_planeParabolicSU _ _ g).mpr ⟨rfl,rfl,rfl,rfl⟩⟩

private theorem representative_torus (c : fixedField m) (hc : c ≠ 0) :
    ∃ g ∈ planeParabolic m hm,
      g * element m hm (representative m c) * g⁻¹ = element m hm (representative m 1) := by
  obtain ⟨s,hs⟩ := (frobeniusEquiv (fixedField m) 2).surjective c⁻¹
  have hs2 : s^2 = c⁻¹ := hs
  have hs0 : s ≠ 0 := by
    intro he
    exact (inv_ne_zero hc) (by simpa [he] using hs2.symm)
  let s' : FixedBy.subfield (MatrixField m) (fieldConj m) :=
    ⟨(planeFieldEquiv m).symm s,by
      change fieldConj m ((planeFieldEquiv m).symm (s : Field m)) = (planeFieldEquiv m).symm (s : Field m)
      rw [←planeFieldEquiv_symm_conj]
      exact congrArg (planeFieldEquiv m).symm s.property⟩
  have hs' : s' ≠ 0 := by
    intro he
    apply hs0
    apply Subtype.ext
    apply (planeFieldEquiv m).symm.injective
    exact (congrArg Subtype.val he).trans (map_zero _).symm
  let g := torus m hm s' hs'
  refine ⟨projection m hm g.val,⟨g.val,g.property,rfl⟩,?_⟩
  let u : MatrixGroup m hm := unipotentSU (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)
    ((planeHermitianEquiv m).symm (representative m c))
  let v : MatrixGroup m hm := unipotentSU (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)
    ((planeHermitianEquiv m).symm (representative m 1))
  have hmatrix : g.val * u * g.val⁻¹ = v := by
    apply (mul_inv_eq_iff_eq_mul).mpr
    apply Subtype.ext
    apply Units.ext
    have he : (s' : MatrixField m)^2 * (planeFieldEquiv m).symm (c : Field m) = 1 := by
      have he : (s : Field m)^2 * (c : Field m) = 1 :=
        congrArg Subtype.val (by rw [hs2,inv_mul_cancel₀ hc] : s^2*c = 1)
      simpa only [map_mul,map_pow,map_one] using congrArg (planeFieldEquiv m).symm he
    have hg : g.val.val.val = Matrix.diagonal ![1,(s' : MatrixField m),(s' : MatrixField m)⁻¹,1] := rfl
    change g.val.val.val *
        (unipotentSU (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)
          ((planeHermitianEquiv m).symm (representative m c))).val.val =
      (unipotentSU (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)
          ((planeHermitianEquiv m).symm (representative m 1))).val.val * g.val.val.val
    rw [hg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unipotentSU,unipotentMatrix,planeHermitianEquiv,representative,
        coordinates_symm_val,Matrix.diagonal_mul,Matrix.mul_diagonal]
    change (s' : MatrixField m) * (planeFieldEquiv m).symm (c : Field m) = (s' : MatrixField m)⁻¹
    apply (mul_right_cancel₀ (show (s' : MatrixField m) ≠ 0 from Subtype.coe_ne_coe.mpr hs'))
    rw [inv_mul_cancel₀ (show (s' : MatrixField m) ≠ 0 from Subtype.coe_ne_coe.mpr hs')]
    rw [mul_right_comm]
    exact (pow_two (s' : MatrixField m) ▸ he)
  simpa only [map_mul,map_inv,element_eq] using congrArg (projection m hm) hmatrix

/-- Every nonidentity native plane-core element is plane-conjugate to one of two fixed elements. -/
theorem planeCore_two_orbits :
    ∃ z ∈ FourPlacement.planeCore m hm, ∃ t ∈ FourPlacement.planeCore m hm,
      z ≠ 1 ∧ t ≠ 1 ∧ ∀ x ∈ FourPlacement.planeCore m hm, x ≠ 1 →
        ∃ g ∈ planeParabolic m hm, g*x*g⁻¹ = z ∨ g*x*g⁻¹ = t := by
  let z := element m hm (representative m 0)
  let t := element m hm (representative m 1)
  have hmem (c : fixedField m) : element m hm (representative m c) ∈ FourPlacement.planeCore m hm :=
    ⟨(L2TwoCoreEquiv m hm (Multiplicative.ofAdd (representative m c))).val,
      (L2TwoCoreEquiv m hm (Multiplicative.ofAdd (representative m c))).property,rfl⟩
  have hne (c : fixedField m) : element m hm (representative m c) ≠ 1 := by
    intro he
    exact representative_ne_zero m c ((element_injective m hm) (he.trans (element_zero m hm).symm))
  refine ⟨z,hmem 0,t,hmem 1,hne 0,hne 1,?_⟩
  rintro x ⟨a,ha,rfl⟩ hx
  change (a : ProjectiveGroup m hm) ≠ 1 at hx
  change ∃ g ∈ planeParabolic m hm,
    g*(a : ProjectiveGroup m hm)*g⁻¹ = z ∨ g*(a : ProjectiveGroup m hm)*g⁻¹ = t
  obtain ⟨X,hX⟩ := (L2TwoCoreEquiv m hm).surjective ⟨a,ha⟩
  have hxe : (a : ProjectiveGroup m hm) = element m hm X.toAdd :=
    (congrArg (fun v : pCore 2 (L2 m hm) => (v.val : ProjectiveGroup m hm)) hX).symm
  have hX0 : X.toAdd ≠ 0 := by
    intro he
    rw [hxe,he,element_zero] at hx
    exact hx rfl
  obtain ⟨g,hg,hgX⟩ := element_normalize m hm X.toAdd hX0
  by_cases hc : form m X.toAdd = 0
  · refine ⟨g,hg,Or.inl ?_⟩
    rw [hxe,hgX,hc]
  · obtain ⟨k,hk,hkc⟩ := representative_torus m hm (form m X.toAdd) hc
    refine ⟨k*g,(planeParabolic m hm).mul_mem hk hg,Or.inr ?_⟩
    rw [hxe]
    calc
      (k*g)*element m hm X.toAdd*(k*g)⁻¹ = k*(g*element m hm X.toAdd*g⁻¹)*k⁻¹ := by group
      _ = t := by rw [hgX,hkc]

/-- An actual plane endpoint equivalence transports the two native orbits,
including the exact intrinsic two-core and ambient subgroup embedding. -/
theorem planeCore_two_orbits_transport
    {G : Type*} [Group G] (P : Subgroup G) (e : P ≃* planeParabolic m hm) :
    ∃ z ∈ P.pCoreIn 2, ∃ t ∈ P.pCoreIn 2,
      z ≠ 1 ∧ t ≠ 1 ∧ ∀ x ∈ P.pCoreIn 2, x ≠ 1 →
        ∃ g ∈ P, g*x*g⁻¹ = z ∨ g*x*g⁻¹ = t := by
  have hmem (x : P) : e x ∈ pCore 2 (planeParabolic m hm) ↔ x ∈ pCore 2 P := by
    rw [←pCore_map_iso 2 e]
    exact mem_map_iff_mem e.injective
  obtain ⟨z,hz,t,ht,hz1,ht1,hcov⟩ := planeCore_two_orbits m hm
  rw [FourPlacement.planeCore_eq_twoCore] at hz ht
  obtain ⟨z,hz,rfl⟩ := hz
  obtain ⟨t,ht,rfl⟩ := ht
  have hz' : e.symm z ∈ pCore 2 P := (hmem _).mp (by rwa [e.apply_symm_apply])
  have ht' : e.symm t ∈ pCore 2 P := (hmem _).mp (by rwa [e.apply_symm_apply])
  refine ⟨(e.symm z : G),⟨e.symm z,hz',rfl⟩,
    (e.symm t : G),⟨e.symm t,ht',rfl⟩,?_,?_,?_⟩
  · intro he
    have hh : z = 1 := e.symm.injective ((Subtype.ext he).trans e.symm.map_one.symm)
    exact hz1 (congrArg Subtype.val hh)
  · intro he
    have hh : t = 1 := e.symm.injective ((Subtype.ext he).trans e.symm.map_one.symm)
    exact ht1 (congrArg Subtype.val hh)
  · rintro x ⟨x,hx,rfl⟩ hx1
    have hnative : (e x : ProjectiveGroup m hm) ∈ FourPlacement.planeCore m hm := by
      rw [FourPlacement.planeCore_eq_twoCore]
      exact ⟨e x,(hmem x).mpr hx,rfl⟩
    have hne : (e x : ProjectiveGroup m hm) ≠ 1 := by
      intro he
      have hh : x = 1 := e.injective ((Subtype.ext he).trans e.map_one.symm)
      exact hx1 (congrArg P.subtype hh)
    obtain ⟨g,hg,hgzt⟩ := hcov (e x) hnative hne
    let k : P := e.symm ⟨g,hg⟩
    have transport (y : planeParabolic m hm)
        (he : g*(e x : ProjectiveGroup m hm)*g⁻¹ = y) :
        (k : G)*(x : G)*(k : G)⁻¹ = (e.symm y : G) := by
      change ((k*x*k⁻¹ : P) : G) = (e.symm y : G)
      apply congrArg (fun v : P => (v : G))
      apply e.injective
      simp only [map_mul,map_inv,k,e.apply_symm_apply]
      exact Subtype.ext he
    refine ⟨k,k.property,?_⟩
    rcases hgzt with hz | ht
    · exact Or.inl (transport z hz)
    · exact Or.inr (transport t ht)

end CFSG.Quasithin.ChapterF.UnitarySource.FourOrbits
