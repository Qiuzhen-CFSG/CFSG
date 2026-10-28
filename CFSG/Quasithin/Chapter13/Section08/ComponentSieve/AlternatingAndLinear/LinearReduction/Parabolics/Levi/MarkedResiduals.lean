module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi.FiveSpaces
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# Cubic witnesses in the marked endpoint two-residuals

On the two coordinates of a node, the product of opposite transvections
has cube one. It belongs to the actual single-node parabolic and hence to
its two-residual O². The first endpoint moves a vector of the marked
two-space; the last endpoint moves a coset in the marked two-dimensional
quotient. Under the quotient maps of FiveSpaces these give nonidentity S₃
coordinates. Consequently neither residual image is contained in the
corresponding PSL₃(2) factor.

Source: Aschbacher–Smith 13.8.25, combined manuscript of 1 March 2004,
printed p.960 (PDF p.977). These are explicit witnesses in the given
subgroups, not abstract copies of a rank-one group.
-/

public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.SmallParabolicLevi BinaryLinear.FiveFlagGeometry.SylowOvergroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

private noncomputable def basisTransvection (b : FiveBasis) (r s : Fin 5) (hrs : r ≠ s) : LinearGroup 5 :=
  transvection (b r) (b.coord s) (by simp [Module.Basis.coord_apply, hrs.symm])

private theorem basisTransvection_maps (b : FiveBasis) (r s : Fin 5) (hrs : r ≠ s)
    (k : Fin 4) (h : r.val ≤ k.val ∨ k.val < s.val) :
    ∀ v ∈ flagSpace b k, basisTransvection b r s hrs v ∈ flagSpace b k := by
  have hle : flagSpace b k ≤ (flagSpace b k).comap
      (basisTransvection b r s hrs).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    change b j + (b.coord s) (b j) • b r ∈ flagSpace b k
    by_cases hjs : j = s
    · subst j
      have hr : r.val ≤ k.val := h.resolve_right (fun hh => Nat.not_lt_of_ge hj hh)
      apply Submodule.add_mem _ ((basis_mem_flagSpace_iff b k s).mpr hj)
      exact Submodule.smul_mem _ _ ((basis_mem_flagSpace_iff b k r).mpr hr)
    · simpa [Module.Basis.coord_apply, Ne.symm hjs] using
        (basis_mem_flagSpace_iff b k j).mpr hj
  exact fun v hv => hle hv

/-- A cubic element acting on precisely the two coordinates of a marked node. -/
noncomputable def fiveNodeRotation (b : FiveBasis) (i : Fin 4) : LinearGroup 5 :=
  basisTransvection b i.castSucc i.succ (by intro h; have := congrArg Fin.val h; simp at this) *
  basisTransvection b i.succ i.castSucc (by intro h; have := congrArg Fin.val h; simp at this)

theorem fiveNodeRotation_mem (b : FiveBasis) (i : Fin 4) :
    fiveNodeRotation b i ∈ fiveParabolic b {i} := by
  apply (fiveParabolic b {i}).mul_mem
  · apply (mem_flagStabilizer_iff_maps b {i}ᶜ _).mpr
    intro k hk
    apply basisTransvection_maps
    change k ≠ i at hk
    have hne : k.val ≠ i.val := fun h => hk (Fin.ext h)
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  · apply (mem_flagStabilizer_iff_maps b {i}ᶜ _).mpr
    intro k hk
    apply basisTransvection_maps
    change k ≠ i at hk
    have hne : k.val ≠ i.val := fun h => hk (Fin.ext h)
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega

private theorem binary_add_self (v : Space 5) : v + v = 0 := by
  calc
    v + v = ((1 : ZMod 2) + 1) • v := by rw [add_smul, one_smul]
    _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul]

theorem fiveNodeRotation_apply_left (b : FiveBasis) (i : Fin 4) :
    fiveNodeRotation b i (b i.castSucc) = b i.succ := by
  have hne : i.castSucc ≠ i.succ := by intro h; have := congrArg Fin.val h; simp at this
  change (b i.castSucc + (b.coord i.castSucc) (b i.castSucc) • b i.succ) +
    (b.coord i.succ) (b i.castSucc + (b.coord i.castSucc) (b i.castSucc) • b i.succ) •
      b i.castSucc = _
  simp only [map_add, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply, ite_true, one_smul, hne, ite_false, zero_add]
  rw [add_right_comm, binary_add_self, zero_add]

theorem fiveNodeRotation_apply_right (b : FiveBasis) (i : Fin 4) :
    fiveNodeRotation b i (b i.succ) = b i.succ + b i.castSucc := by
  have hne : i.castSucc ≠ i.succ := by intro h; have := congrArg Fin.val h; simp at this
  simp [fiveNodeRotation, basisTransvection, transvection, LinearEquiv.mul_apply,
    Module.Basis.coord_apply, hne]

theorem fiveNodeRotation_apply_other (b : FiveBasis) (i : Fin 4) (j : Fin 5)
    (hj : j ≠ i.castSucc) (hj' : j ≠ i.succ) : fiveNodeRotation b i (b j) = b j := by
  simp [fiveNodeRotation, basisTransvection, transvection, LinearEquiv.mul_apply,
    Module.Basis.coord_apply, Ne.symm hj, Ne.symm hj']

theorem fiveNodeRotation_cube (b : FiveBasis) (i : Fin 4) :
    fiveNodeRotation b i ^ 3 = 1 := by
  apply LinearEquiv.toLinearMap_injective
  apply b.ext
  intro j
  change (fiveNodeRotation b i) ((fiveNodeRotation b i) ((fiveNodeRotation b i) (b j))) = b j
  by_cases hj : j = i.castSucc
  · subst j
    rw [fiveNodeRotation_apply_left, fiveNodeRotation_apply_right, map_add,
      fiveNodeRotation_apply_right, fiveNodeRotation_apply_left, add_right_comm,
      binary_add_self, zero_add]
  · by_cases hj' : j = i.succ
    · subst j
      rw [fiveNodeRotation_apply_right, map_add, fiveNodeRotation_apply_right,
        fiveNodeRotation_apply_left, add_right_comm, binary_add_self, zero_add,
        fiveNodeRotation_apply_left]
    · rw [fiveNodeRotation_apply_other b i j hj hj',
        fiveNodeRotation_apply_other b i j hj hj', fiveNodeRotation_apply_other b i j hj hj']

/-- The cubic element belongs to O² of the actual single-node parabolic. -/
theorem fiveNodeRotation_mem_residual (b : FiveBasis) (i : Fin 4) :
    fiveNodeRotation b i ∈ fiveNodeResidual b i := by
  let g : fiveParabolic b {i} := ⟨fiveNodeRotation b i, fiveNodeRotation_mem b i⟩
  have hg : g ^ 3 = 1 := Subtype.ext (fiveNodeRotation_cube b i)
  apply Subgroup.mem_map.mpr
  refine ⟨g, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
  exact (by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hg)



/-- The first endpoint residual has a nonidentity S₃ coordinate in the 2+3 overgroup. -/
theorem exists_first_residual_nontrivial_twoSpace_image (b : FiveBasis) :
    ∃ g : flagStabilizer b {1}, g.val ∈ fiveNodeResidual b 0 ∧
      (fiveTwoSpaceQuotientEquiv b (QuotientGroup.mk' _ g)).1 ≠ 1 := by
  have hP : fiveParabolic b {0} ≤ flagStabilizer b {1} :=
    flagStabilizer_antitone b (by simp)
  let g : flagStabilizer b {1} := ⟨fiveNodeRotation b 0, hP (fiveNodeRotation_mem b 0)⟩
  refine ⟨g, fiveNodeRotation_mem_residual b 0, ?_⟩
  rw [fiveTwoSpaceQuotientEquiv_fst_mk, ne_eq, linearTwoEquivSymmetricThree.map_eq_one_iff,
    (linearGroupCongr (fiveCutCoordinates b 1)).map_eq_one_iff]
  intro hact
  let w : flagSpace b 1 := ⟨b 0, (basis_mem_flagSpace_iff b 1 0).mpr (by decide)⟩
  have hf := congrArg Subtype.val (LinearEquiv.congr_fun hact w)
  change fiveNodeRotation b 0 (b 0) = b 0 at hf
  have hr : fiveNodeRotation b 0 (b 0) = b 1 := by
    simpa using fiveNodeRotation_apply_left b 0
  rw [hr] at hf
  exact (by decide : (1 : Fin 5) ≠ 0) (b.injective hf)

/-- The last endpoint residual has a nonidentity S₃ coordinate in the 3+2 overgroup. -/
theorem exists_last_residual_nontrivial_threeSpace_image (b : FiveBasis) :
    ∃ g : flagStabilizer b {2}, g.val ∈ fiveNodeResidual b 3 ∧
      (fiveThreeSpaceQuotientEquiv b (QuotientGroup.mk' _ g)).2 ≠ 1 := by
  have hP : fiveParabolic b {3} ≤ flagStabilizer b {2} :=
    flagStabilizer_antitone b (by simp)
  let g : flagStabilizer b {2} := ⟨fiveNodeRotation b 3, hP (fiveNodeRotation_mem b 3)⟩
  refine ⟨g, fiveNodeRotation_mem_residual b 3, ?_⟩
  rw [fiveThreeSpaceQuotientEquiv_snd_mk, ne_eq, linearTwoEquivSymmetricThree.map_eq_one_iff,
    (linearGroupCongr (fiveQuotientCoordinates b 2)).map_eq_one_iff]
  intro hact
  have hf := LinearEquiv.congr_fun hact ((flagSpace b 2).mkQ (b 4))
  change (flagSpace b 2).mkQ (fiveNodeRotation b 3 (b 4)) = (flagSpace b 2).mkQ (b 4) at hf
  have hr : fiveNodeRotation b 3 (b 4) = b 4 + b 3 := by
    simpa using fiveNodeRotation_apply_right b 3
  rw [hr] at hf
  have hm := (Submodule.Quotient.eq (flagSpace b 2)).mp hf
  simp only [add_sub_cancel_left] at hm
  have := (basis_mem_flagSpace_iff b 2 3).mp hm
  norm_num at this

/-- The first residual's image is not contained in the marked PSL₃(2) factor. -/
theorem first_residual_image_not_le_projective_factor (b : FiveBasis) :
    ¬ ((fiveNodeResidual b 0).subgroupOf (flagStabilizer b {1})).map
      ((fiveTwoSpaceQuotientEquiv b).toMonoidHom.comp (QuotientGroup.mk' _)) ≤
        (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod ⊤ := by
  intro h
  obtain ⟨g, hg, hn⟩ := exists_first_residual_nontrivial_twoSpace_image b
  exact hn (h (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)).1

/-- The last residual's image is not contained in the marked PSL₃(2) factor. -/
theorem last_residual_image_not_le_projective_factor (b : FiveBasis) :
    ¬ ((fiveNodeResidual b 3).subgroupOf (flagStabilizer b {2})).map
      ((fiveThreeSpaceQuotientEquiv b).toMonoidHom.comp (QuotientGroup.mk' _)) ≤
        (⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))).prod ⊥ := by
  intro h
  obtain ⟨g, hg, hn⟩ := exists_last_residual_nontrivial_threeSpace_image b
  exact hn (h (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)).2

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

end
