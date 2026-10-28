module

public import Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics.CoreCentralizer.Radical

/-!
# Reducing unitary parabolic two-core centralizers to matrices

The concrete flag kernel is a normal two-subgroup of the actual projective
parabolic. An element centralizing its projective image has a special unitary
representative centralizing the original flag kernel. If the matrix calculation
shows this representative is a scalar plus a shear from `V/Wᗮ` into `W`, its
projective square is one. Thus the radical centralizer is itself a normal
two-subgroup, which proves the desired intrinsic two-core centralizer bound.

The scalar-shear calculation is still an explicit premise. This module proves
the radical and projective reductions, not the complete source theorem.
The two remaining cases are `Wᗮ = W` and `Wᗮ ≠ W`; their final assembly belongs
in `CoreCentralizer` after their matrix calculations have been proved.

Source: GLS3 2.6.5(e), `refs/KGroup/GLS3/chapter2.tex`, as used for
Aschbacher--Smith B.1.13, printed p.74 (PDF p.85) of `refs/quasithin.pdf`.
-/

public section

open Matrix BenderSuzuki.MatrixGroups Subgroup

namespace Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics.CoreCentralizer
variable {F : Type*} [Field F] {d : ℕ} (J : HermitianForm d F)

/-- A scalar plus a flag shear has projective square one in characteristic
two. This uses total isotropy and does not require the scalar matrix itself
to have determinant one. -/
theorem projectParabolic_sq_eq_one_of_scalarShear [CharP F 2]
    (W : Submodule F (Fin d → F)) (hi : TotallyIsotropic J W)
    (g : specialStabilizer J W) (hg : ScalarShear J W g) :
    projectParabolic J W g ^ 2 = 1 := by
  obtain ⟨c, hc0, hc1⟩ := hg
  have hv (v : Fin d → F) :
      stabilizerAction J W g (stabilizerAction J W g v) = ((c : F) ^ 2) • v := by
    have ht := hc0 _ ((le_perpendicular_iff J W).mpr hi (hc1 v))
    rw [map_sub, map_smul] at ht
    have he := sub_eq_iff_eq_add.mp ht
    rw [smul_sub, sub_add_eq_add_sub, ← add_smul, CharTwo.add_self_eq_zero,
      zero_smul, zero_sub, smul_smul, ← neg_smul, CharTwo.neg_eq] at he
    simpa only [pow_two] using he
  have hs : g.val.val ^ 2 = GeneralLinearGroup.scalar (Fin d) (c ^ 2) := by
    apply Units.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    rw [pow_two, Units.val_mul]
    change ((g.val.val : Matrix (Fin d) (Fin d) F) *
      (g.val.val : Matrix (Fin d) (Fin d) F)) *ᵥ v =
      (Matrix.diagonal (fun _ : Fin d => ((c ^ 2 : Fˣ) : F))) *ᵥ v
    rw [← mulVec_mulVec, diagonal_const_mulVec]
    exact hv v
  apply Subtype.ext
  apply Subtype.ext
  change ProjGenLinGroup.mk g.val.val ^ 2 = 1
  rw [← map_pow, hs, ProjGenLinGroup.mk_scalar]

/-- The actual matrix centralizer calculation makes the intrinsic projective
radical centralizer a two-group. The matrix calculation remains explicit. -/
theorem radicalCentralizer_isTwoGroup_of_scalarShear [CharP F 2]
    (W : Submodule F (Fin d → F)) (hW : W ≠ ⊥) (hi : TotallyIsotropic J W)
    (hcalc : ∀ g : specialStabilizer J W,
      g ∈ centralizer (specialRadical J W : Set (specialStabilizer J W)) → ScalarShear J W g) :
    IsPGroup 2 (centralizer (projectiveRadical J W : Set (parabolic J W))) := by
  intro x
  obtain ⟨g, hg⟩ := projectParabolic_surjective J W x.val
  have hc := centralizes_specialRadical_of_project J W hW g (hg.symm ▸ x.property)
  refine ⟨1, ?_⟩
  apply Subtype.ext
  change x.val ^ 2 = 1
  rw [← hg]
  exact projectParabolic_sq_eq_one_of_scalarShear J W hi g (hcalc g hc)

/-- Conditional final reduction for the intrinsic parabolic two-core.
The radical and its centralizer are normal two-subgroups, so the centralizer
of the two-core lies in that two-core. The remaining source obligation is
the scalar-shear calculation for all special unitary radical centralizers. -/
theorem centralizer_twoCore_le_of_scalarShear [CharP F 2] [NeZero d] [Finite F]
    (W : Submodule F (Fin d → F)) (hW : W ≠ ⊥) (hi : TotallyIsotropic J W)
    (hcalc : ∀ g : specialStabilizer J W,
      g ∈ centralizer (specialRadical J W : Set (specialStabilizer J W)) → ScalarShear J W g) :
    centralizer (pCore 2 (parabolic J W) : Set (parabolic J W)) ≤ pCore 2 (parabolic J W) := by
  have hc : centralizer (projectiveRadical J W : Set (parabolic J W)) ≤
      pCore 2 (parabolic J W) :=
    le_sSup ⟨inferInstance, radicalCentralizer_isTwoGroup_of_scalarShear J W hW hi hcalc⟩
  exact (Subgroup.centralizer_le (projectiveRadical_le_twoCore J W)).trans hc

end Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics.CoreCentralizer
