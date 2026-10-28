module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.Field

/-!
# Projective interpretation of normalized unitary coordinates

Every nonzero vector has a unique representative with first nonzero entry one.
This identifies normalized isotropic vectors, including zero, with the actual
isotropic projective lines over GF(4) and an additional singleton. The field
isomorphism transports the rank-one formula to the specified unitary matrix
`I + v vᴴ`. A nonzero scalar coordinate identity therefore proves the precise
permutation action, including both singleton cases.

Application: the ATLAS Fi22 fixed-point labeling, GLS3 Table 5.3t,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

@[expose] public section
open Theory.SpecificGroups
open scoped LinearAlgebra.Projectivization
namespace Sporadic.Fischer.Fi22.TransvectionComparison.Labeling

theorem liftVector_injective : Function.Injective liftVector := by
  intro v w h
  funext k
  exact fieldEquiv.injective (congrFun h k)

@[simp] theorem liftVector_zero : liftVector 0 = 0 := by
  ext k
  exact map_zero fieldEquiv

@[simp] theorem liftVector_eq_zero (v : Fin 6 → Four) : liftVector v = 0 ↔ v = 0 := by
  rw [← liftVector_zero]
  exact liftVector_injective.eq_iff

theorem liftVector_smul (c : Four) (v : Fin 6 → Four) :
    liftVector (c • v) = fieldEquiv c • liftVector v := by
  ext k
  exact map_mul fieldEquiv c (v k)

theorem normalized_smul_eq (v w : Fin 6 → Four) (hv : Normalized v)
    (hw : Normalized w) (c : Four) (hc : c ≠ 0) (h : c • w = v) : v = w := by
  rcases hv with rfl | ⟨i, hi, hbefore⟩
  · exact (smul_eq_zero.mp h).resolve_left hc |>.symm
  rcases hw with rfl | ⟨j, hj, hbefore'⟩
  · simpa only [smul_zero] using h.symm
  have hij : i = j := by
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have := congrFun h i
      simp [Pi.smul_apply, smul_eq_mul, hbefore' i hlt, hi] at this
    · exact heq
    · have := congrFun h j
      simp [Pi.smul_apply, smul_eq_mul, hbefore j hgt, hj, hc] at this
  subst j
  have hc1 : c = 1 := by
    simpa only [Pi.smul_apply, smul_eq_mul, hj, hi, mul_one] using congrFun h i
  simpa only [hc1, one_smul] using h.symm

theorem exists_normalized (v : Fin 6 → Four) (hv : v ≠ 0) :
    ∃ c : Four, c ≠ 0 ∧ Normalized (c • v) := by
  let s : Finset (Fin 6) := Finset.univ.filter (fun i => v i ≠ 0)
  have hs : s.Nonempty := by
    by_contra hn
    apply hv
    funext i
    by_contra hi
    exact hn ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let i := s.min' hs
  have hi : v i ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
  refine ⟨(v i)⁻¹, inv_ne_zero hi, Or.inr ⟨i, ?_, ?_⟩⟩
  · exact inv_mul_cancel₀ hi
  · intro j hj
    have hz : v j = 0 := by
      by_contra hn
      have hij := Finset.min'_le s j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
      exact not_lt_of_ge hij hj
    simp only [Pi.smul_apply, hz, smul_zero]

/-- Normalized isotropic vectors, with zero retained as a singleton. -/
abbrev NormalPoint := {v : Fin 6 → Four // norm v = 0 ∧ Normalized v}

noncomputable def toPoint (v : NormalPoint) : U6Two.PointWithSingleton :=
  if hv : v.val = 0 then none
  else some (U6Two.mkIsotropicPoint (liftVector v.val)
    (mt (liftVector_eq_zero _).mp hv) (by rw [lift_norm, v.property.1, map_zero]))

theorem toPoint_zero (v : NormalPoint) (hv : v.val = 0) : toPoint v = none := by
  simp only [toPoint, dif_pos hv]

theorem toPoint_nonzero (v : NormalPoint) (hv : v.val ≠ 0) :
    toPoint v = some (U6Two.mkIsotropicPoint (liftVector v.val)
      (mt (liftVector_eq_zero _).mp hv) (by rw [lift_norm, v.property.1, map_zero])) := by
  simp only [toPoint, dif_neg hv]

theorem toPoint_injective : Function.Injective toPoint := by
  intro v w h
  by_cases hv : v.val = 0
  · by_cases hw : w.val = 0
    · exact Subtype.ext (hv.trans hw.symm)
    · rw [toPoint_zero v hv, toPoint_nonzero w hw] at h
      contradiction
  · by_cases hw : w.val = 0
    · rw [toPoint_zero w hw, toPoint_nonzero v hv] at h
      contradiction
    · rw [toPoint_nonzero v hv, toPoint_nonzero w hw] at h
      have hp := congrArg Subtype.val (Option.some.inj h)
      obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mp hp
      have hcv : fieldEquiv.symm c • w.val = v.val := by
        funext k
        apply fieldEquiv.injective
        simpa only [Pi.smul_apply, smul_eq_mul, map_mul,
          fieldEquiv.apply_symm_apply, liftVector] using congrFun hc k
      have hc0 : fieldEquiv.symm c ≠ 0 := by
        intro hz
        rw [hz, zero_smul] at hcv
        exact hv hcv.symm
      exact Subtype.ext (normalized_smul_eq v.val w.val v.property.2 w.property.2 _ hc0 hcv)

theorem toPoint_surjective : Function.Surjective toPoint := by
  intro p
  cases p with
  | none => exact ⟨⟨0, by simp [norm], Or.inl rfl⟩, toPoint_zero _ rfl⟩
  | some p =>
    let w : Fin 6 → Four := fun k => fieldEquiv.symm (p.val.rep k)
    have hw : liftVector w = p.val.rep := by ext k; exact fieldEquiv.apply_symm_apply _
    have hw0 : w ≠ 0 := by
      intro h
      exact p.val.rep_nonzero (by rw [← hw, h, liftVector_zero])
    obtain ⟨c, hc, hcn⟩ := exists_normalized w hw0
    have hn : norm (c • w) = 0 := by
      apply fieldEquiv.injective
      rw [map_zero, ← lift_norm, liftVector_smul, U6Two.hermitianNorm_smul, hw]
      rw [p.property, mul_zero]
    let v : NormalPoint := ⟨c • w, hn, hcn⟩
    have hv : v.val ≠ 0 := smul_ne_zero hc hw0
    refine ⟨v, (toPoint_nonzero v hv).trans ?_⟩
    congr 1
    apply Subtype.ext
    change Projectivization.mk _ (liftVector (c • w)) _ = p.val
    rw [← Projectivization.mk_rep p.val]
    apply (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr
    exact ⟨fieldEquiv c, by rw [liftVector_smul, hw]⟩

/-- The genuine projective interpretation of all normalized isotropic vectors. -/
noncomputable def normalPointEquiv : NormalPoint ≃ U6Two.PointWithSingleton :=
  Equiv.ofBijective toPoint ⟨toPoint_injective, toPoint_surjective⟩

/-- A nonzero scalar identity of coordinates certifies the literal projective
transvection, also when either point is the adjoined singleton. -/
theorem toPoint_transvection (v w z : NormalPoint) (c : Four) (hc : c ≠ 0)
    (h : c • z.val = transvection v.val w.val) :
    toPoint z = pointTransvection (toPoint v) (toPoint w) := by
  by_cases hv : v.val = 0
  · have hwz : w.val = z.val := normalized_smul_eq w.val z.val w.property.2
      z.property.2 c hc (by simpa [transvection, hv] using h)
    have hzw : z = w := Subtype.ext hwz.symm
    rw [hzw, toPoint_zero v hv, pointTransvection_none]
    rfl
  by_cases hw : w.val = 0
  · have hz : z.val = 0 := by
      have hcz : c • z.val = 0 := by simpa [transvection, hw] using h
      exact (smul_eq_zero.mp hcz).resolve_left hc
    rw [toPoint_zero z hz, toPoint_zero w hw, toPoint_nonzero v hv,
      pointTransvection_some]
    rfl
  have hw0 : liftVector w.val ≠ 0 := mt (liftVector_eq_zero _).mp hw
  have hvi : U6Two.hermitianNorm (liftVector v.val) = 0 := by
    rw [lift_norm, v.property.1, map_zero]
  have hlinear : (U6Two.unitaryTransvection (liftVector v.val) hvi).val •
      liftVector w.val = fieldEquiv c • liftVector z.val := by
    rw [U6Two.unitaryTransvection_smul, ← lift_transvection, ← h, liftVector_smul]
  have hz : z.val ≠ 0 := by
    intro hz
    rw [hz, liftVector_zero, smul_zero] at hlinear
    exact ((smul_ne_zero_iff_ne (U6Two.unitaryTransvection (liftVector v.val) hvi).val).mpr
      hw0) hlinear
  rw [toPoint_nonzero z hz, toPoint_nonzero v hv, toPoint_nonzero w hw,
    pointTransvection_some, U6Two.transvectionPermutation,
    U6Two.isotropicActionWithSingleton_some, U6Two.isotropicTransvection_mk,
    U6Two.isotropicAction_project_mk]
  apply congrArg some
  apply Subtype.ext
  symm
  apply (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr
  exact ⟨fieldEquiv c, hlinear.symm⟩

end Sporadic.Fischer.Fi22.TransvectionComparison.Labeling
