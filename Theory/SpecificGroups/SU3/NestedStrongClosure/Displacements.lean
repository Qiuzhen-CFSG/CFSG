module

public import Theory.SpecificGroups.SU3.ExtensionBorel.Actors
public import Theory.SpecificGroups.SU3.BinaryRootFrattini
public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.Residual
public import Theory.SpecificGroups.SU3.EvenSemilinear.Coordinates

/-!
# Field detection from central root displacements

An automorphism preserving the binary unitary root group and having square-one
displacements fixes its entire first-coordinate quotient. Triangularity of a
semilinear representative and the (0,1) matrix entry then give a scalar multiple
of the field automorphism equal to the identity. Evaluating at one removes the
scalar. Trace one removes the projective scalar ambiguity before this entry
calculation. The actor need not itself square to one.

Source: the root matrices in Huppert II.10.12 and GLS3 Section 2.7; the nested
strong-closure argument for Aschbacher (1975), Lemma 3.4.
-/

public section
open Matrix Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.NestedStrongClosure
open BorelTorus BorelTorus.SemilinearActors ExtensionBorel
variable {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)

private theorem root_intertwine (u : GL (Fin 3) E)
    (z w : hermitianUnipotentCoord J) (σ : E ≃+* E)
    (h : ProjGenLinGroup.mk u * ProjGenLinGroup.map σ.toRingHom
      (ProjGenLinGroup.mk (hermitianUnipotentGL J z)) * (ProjGenLinGroup.mk u)⁻¹ =
      ProjGenLinGroup.mk (hermitianUnipotentGL J w)) :
    u.val * (hermitianUnipotentGL J (rootFieldEquiv J σ z)).val =
      (hermitianUnipotentGL J w).val * u.val := by
  rw [ProjGenLinGroup.map_mk, field_map_root, ← map_inv, ← map_mul, ← map_mul] at h
  obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  have ht := congrArg (fun B : GL (Fin 3) E => B.val.trace) hc
  have htrace (v : hermitianUnipotentCoord J) : (hermitianUnipotentGL J v).val.trace = 1 := by
    simp [hermitianUnipotentGL, hermitianUnipotentMatrix, Matrix.trace,
      Fin.sum_univ_three, CharTwo.add_self_eq_zero]
  have hm : ((u * hermitianUnipotentGL J (rootFieldEquiv J σ z) * u⁻¹) *
      GeneralLinearGroup.scalar (Fin 3) c).val =
      (c : E) • (u.val * (hermitianUnipotentGL J (rootFieldEquiv J σ z)).val * (u⁻¹).val) := by
    ext i j
    simp [GeneralLinearGroup.coe_scalar, Matrix.mul_diagonal, mul_comm]
  rw [hm, trace_smul, trace_units_conj, htrace, htrace, smul_eq_mul, mul_one] at ht
  have hc1 : c = 1 := Units.ext ht
  rw [hc1, map_one, mul_one] at hc
  exact congrArg Units.val (mul_inv_eq_iff_eq_mul.mp hc)

/-- Square-one displacements on the full root group force the field parameter
of an arbitrary semilinear actor to be trivial. No bound on its order is used. -/
theorem field_eq_one_of_root_square_displacements
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {q : ℕ}
    (hcard : Nat.card E = q^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (σ : E ≃+* E)
    (hsem : J.HasUnitarySemilinearForm a σ)
    (hstable : (projectiveRoot J hJ).map a.toMonoidHom = projectiveRoot J hJ)
    (hdisp : ∀ x ∈ projectiveRoot J hJ, (a x * x⁻¹)^2 = 1) : σ = 1 := by
  obtain ⟨u, hu⟩ := hsem
  obtain ⟨h10, h20, h21⟩ := projective_semilinear_upper J hJ hcard hfixed a σ u hu hstable
  have hfirst (z : hermitianUnipotentCoord J) :
      u.val.val 0 0 * σ z.val.1 = z.val.1 * u.val.val 1 1 := by
    have hz : a (hermitianUnipotentPSU J hJ z) ∈ projectiveRoot J hJ := by
      rw [← hstable]
      exact mem_map_of_mem _ ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := hz
    have hsq : (w*z⁻¹)^2 = 1 := by
      apply EvenInner.root_injective J hJ
      rw [map_pow, map_mul, map_inv, map_one, hw]
      exact hdisp _ ⟨z, rfl⟩
    have hzero := (BinaryRootFrattini.square_one_iff J _).mp hsq
    have he : w.val.1 = z.val.1 := by
      change w.val.1 + -z.val.1 = 0 at hzero
      exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hzero)
    have hmat := root_intertwine J u.val z w σ (by
      have hh := hu (hermitianUnipotentPSU J hJ z)
      rw [← hw] at hh
      exact hh.symm)
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 1) hmat
    simp [hermitianUnipotentMatrix, rootFieldEquiv_val,
      Matrix.mul_apply, Fin.sum_univ_three, h21, he] at hh
    linear_combination hh
  have hentry (x : E) : u.val.val 0 0 * σ x = x * u.val.val 1 1 := by
    obtain ⟨z, hz⟩ := EvenSemilinear.coord_first_surjective J hcard hfixed x
    simpa only [hz] using hfirst z
  have hdiag : u.val.val 0 0 = u.val.val 1 1 := by simpa using hentry 1
  have h00 : u.val.val 0 0 ≠ 0 := by
    intro hz
    have hd := u.val.det_ne_zero
    simp [Matrix.det_fin_three, h10, h20, h21, hz] at hd
  apply RingEquiv.ext
  intro x
  change σ x = x
  apply mul_left_cancel₀ h00
  simpa only [← hdiag, mul_comm] using hentry x

end BenderSuzuki.MatrixGroups.HermitianForm.NestedStrongClosure
