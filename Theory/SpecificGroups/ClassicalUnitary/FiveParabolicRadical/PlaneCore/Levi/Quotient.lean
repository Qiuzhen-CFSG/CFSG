module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Levi.Kernel
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Levi.Scalars

/-!
# The full projective plane-parabolic Levi quotient

Restriction to the marked plane descends from SU to the projective parabolic
with values in GL₂ modulo its scalar fifth roots. Its kernel is precisely the
constructed unipotent subgroup: factorization in SU reduces this assertion to
the exact scalar kernel of the Levi section. The resulting quotient isomorphism
and its faithful section describe the full projective Levi decomposition.

Source: the unitary parabolic calculation underlying Aschbacher--Smith,
*The Classification of Quasithin Groups*, F.1.12(7), printed pp.263--264.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.PlaneCore
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

omit [CharP F 2] in
theorem planeRestriction_of_scalar (g : specialStabilizer J (plane F)) (a : Fˣ)
    (h : g.val.val = GeneralLinearGroup.scalar (Fin 5) a) :
    planeRestriction J g = GeneralLinearGroup.scalar (Fin 2) a := by
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [planeRestriction_mulVec]
  have he (v : plane F) : planeLinearAction J g v = a.val • v := by
    apply Subtype.ext
    change g.val.val.val *ᵥ v.val = a.val • v.val
    rw [h]
    exact Matrix.diagonal_const_mulVec _ _
  rw [he, map_smul, LinearEquiv.apply_symm_apply]
  exact (Matrix.diagonal_const_mulVec _ _).symm

omit [CharP F 2] in
theorem project_kernel_le_planeScalar_kernel :
    ((project J).subgroupMap (specialStabilizer J (plane F))).ker ≤
      ((QuotientGroup.mk' (planeScalarRoots (F := F))).comp (planeRestriction J)).ker := by
  intro g hg
  have hp : project J g.val = 1 := congrArg Subtype.val hg
  have hs : ProjGenLinGroup.mk g.val.val = 1 := congrArg Subtype.val hp
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hs
  obtain ⟨a, ha⟩ := hs
  have hd := ((J.mem_specialSubgroup_iff g.val.val).mp g.val.property).2
  rw [← ha, GeneralLinearGroup.det_scalar] at hd
  have hr : a ∈ rootsOfUnity 5 F := (mem_rootsOfUnity 5 a).mpr (by simpa using hd)
  change QuotientGroup.mk (planeRestriction J g) = (1 : GL (Fin 2) F ⧸ planeScalarRoots)
  apply (QuotientGroup.eq_one_iff _).mpr
  rw [planeRestriction_of_scalar J g a ha.symm]
  exact ⟨⟨a, hr⟩, rfl⟩

/-- Restriction on the projective parabolic retains exactly the scalar ambiguity. -/
noncomputable def planeProjectiveRestriction :
    planeParabolic J →* (GL (Fin 2) F ⧸ planeScalarRoots (F := F)) :=
  ((project J).subgroupMap (specialStabilizer J (plane F))).liftOfSurjective
    ((project J).subgroupMap_surjective (specialStabilizer J (plane F)))
    ⟨(QuotientGroup.mk' (planeScalarRoots (F := F))).comp (planeRestriction J),
      project_kernel_le_planeScalar_kernel J⟩

omit [CharP F 2] in
theorem planeProjectiveRestriction_project (g : specialStabilizer J (plane F)) :
    planeProjectiveRestriction J
        ((project J).subgroupMap (specialStabilizer J (plane F)) g) =
      QuotientGroup.mk (planeRestriction J g) := by
  apply MonoidHom.liftOfRightInverse_comp_apply

@[simp] theorem planeProjectiveRestriction_unipotent (hJ : J.form = 1) (u : Parameters J) :
    planeProjectiveRestriction J (Parameters.toParabolic hJ u) = 1 := by
  change planeProjectiveRestriction J
    ((project J).subgroupMap (specialStabilizer J (plane F))
      (Parameters.toStabilizer hJ u)) = 1
  rw [planeProjectiveRestriction_project]
  have hu : planeRestriction J (Parameters.toStabilizer hJ u) = 1 :=
    parameters_le_ker_restriction J hJ ⟨u, rfl⟩
  rw [hu]
  rfl

@[simp] theorem planeProjectiveRestriction_levi (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) (A : GL (Fin 2) F) :
    planeProjectiveRestriction J (planeLeviParabolic J c hc hJ A) =
      QuotientGroup.mk A := by
  change planeProjectiveRestriction J
    ((project J).subgroupMap (specialStabilizer J (plane F))
      (planeLeviStabilizer J c hc hJ A)) = _
  rw [planeProjectiveRestriction_project, planeRestriction_section]

theorem planeProjectiveRestriction_surjective (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) : Function.Surjective (planeProjectiveRestriction J) := by
  intro q
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective (planeScalarRoots (F := F)) q
  exact ⟨planeLeviParabolic J c hc hJ A, planeProjectiveRestriction_levi J c hc hJ A⟩

/-- The full kernel, not merely a subgroup of pointwise plane fixers. -/
theorem planeProjectiveRestriction_ker (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) (hconj : ∀ x, J.conj x = x ^ 4) :
    (planeProjectiveRestriction J).ker = projectiveUnipotent J hJ := by
  ext g
  constructor
  · intro hg
    obtain ⟨u, A, rfl⟩ := planeParabolic_factorization J c hc hJ g
    have hA : QuotientGroup.mk A = (1 : GL (Fin 2) F ⧸ planeScalarRoots) := by
      simpa only [MonoidHom.mem_ker, map_mul, planeProjectiveRestriction_unipotent,
        planeProjectiveRestriction_levi, one_mul] using hg
    have hL : planeLeviParabolic J c hc hJ A = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [planeLeviParabolic_ker J c hc hJ hconj]
      exact (QuotientGroup.eq_one_iff _).mp hA
    exact ⟨u, by rw [hL, mul_one]⟩
  · rintro ⟨u, rfl⟩
    exact planeProjectiveRestriction_unipotent J hJ u

instance projectiveUnipotentNormal (hJ : J.form = 1) :
    (projectiveUnipotent J hJ).Normal := projectiveUnipotent_normal J hJ

/-- The quotient of the whole projective parabolic by its unipotents. -/
noncomputable def planeParabolicQuotientEquiv (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) (hconj : ∀ x, J.conj x = x ^ 4) :
    (planeParabolic J ⧸ projectiveUnipotent J hJ) ≃*
      (GL (Fin 2) F ⧸ planeScalarRoots (F := F)) :=
  (QuotientGroup.quotientMulEquivOfEq
    (planeProjectiveRestriction_ker J c hc hJ hconj).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (planeProjectiveRestriction J)
        (planeProjectiveRestriction_surjective J c hc hJ))

/-- The full projective Levi section, now with its precise scalar quotient as domain. -/
noncomputable def planeProjectiveLevi (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) (hconj : ∀ x, J.conj x = x ^ 4) :
    (GL (Fin 2) F ⧸ planeScalarRoots (F := F)) →* planeParabolic J :=
  QuotientGroup.lift _ (planeLeviParabolic J c hc hJ) (by
    intro A hA
    apply MonoidHom.mem_ker.mp
    rwa [planeLeviParabolic_ker J c hc hJ hconj])

@[simp] theorem planeProjectiveLevi_mk (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) (hconj : ∀ x, J.conj x = x ^ 4) (A : GL (Fin 2) F) :
    planeProjectiveLevi J c hc hJ hconj (QuotientGroup.mk A) =
      planeLeviParabolic J c hc hJ A := rfl

@[simp] theorem planeProjectiveRestriction_section (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) (hconj : ∀ x, J.conj x = x ^ 4)
    (q : GL (Fin 2) F ⧸ planeScalarRoots (F := F)) :
    planeProjectiveRestriction J (planeProjectiveLevi J c hc hJ hconj q) = q := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective (planeScalarRoots (F := F)) q
  exact planeProjectiveRestriction_levi J c hc hJ A

theorem planeProjectiveLevi_injective (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) (hconj : ∀ x, J.conj x = x ^ 4) :
    Function.Injective (planeProjectiveLevi J c hc hJ hconj) :=
  Function.LeftInverse.injective (planeProjectiveRestriction_section J c hc hJ hconj)

end Theory.SpecificGroups.UnitaryFive.PlaneCore
