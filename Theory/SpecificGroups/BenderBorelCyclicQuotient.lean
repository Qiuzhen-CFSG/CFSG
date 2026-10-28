module

public import BenderSuzuki.Converse.PSL2
public import Theory.SpecificGroups.Suzuki.StandardSubgroups
public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import Theory.GroupTheory.CyclicCoreQuotient

/-!
# The three Bender Borels modulo their two-cores

In each concrete Borel, the root group is a normal two-subgroup and the
torus is cyclic. Hence the quotient by the two-core is cyclic. For PSU₃
the Hermitian coordinate group has exponent at most four in characteristic
two, and the literal torus/root commutation formula proves normality.
The torus is the image of the matrix-field units; no replacement of the
quadratic matrix field by the Hermitian fixed field occurs.

Source: the PSL₂ matrix formulas, Huppert--Blackburn XI.3.1--3 (Suzuki),
and Huppert II.10.12 (PSU₃). These supply the Borel calculation in
Aschbacher--Smith, E.2.2(2a) and 4.4.13, pp.215--216 and 623--624.
-/

@[expose] public section
open Subgroup

namespace Theory.SpecificGroups.BenderBorel
open BenderSuzuki.Converse BenderSuzuki.MatrixGroups BenderSuzuki.External

/-- The standard projective unitary Borel, with the actual root and torus maps. -/
abbrev unitaryBorel {F : Type*} [Field F] (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :=
  (hermitianUnipotentPSU J hJ).range ⊔ (hermitianTorusPSU J hJ).range


theorem psl2_borel_cyclic_quotient {F : Type*} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hcard : Nat.card F = 2 ^ f) :
    IsCyclic (PBorel F ⧸ pCore 2 (PBorel F)) := by
  have hp : IsPGroup 2 (PUnip F) := IsPGroup.of_card (by rw [PUnip_card, hcard])
  let : IsCyclic (PTorus F) := by
    change IsCyclic ((Torus F).map (pi F))
    rw [Torus_eq_range, MonoidHom.map_range]
    exact isCyclic_of_surjective _ ((pi F).comp (torHom F)).rangeRestrict_surjective
  exact cyclic_quotient_pCore_of_borel (PUnip F) (PTorus F) (PBorel F) hp
    PUnip_sup_PTorus PUnip_normal_in_PBorel

theorem suzuki_borel_cyclic_quotient (m : ℕ) (hm : 0 < m) :
    IsCyclic (SuzukiBorelSubgroup m ⧸ pCore 2 (SuzukiBorelSubgroup m)) := by
  let := suzukiSplitTorus_isCyclic m hm
  exact cyclic_quotient_pCore_of_borel (SuzukiRootSubgroup m) (SuzukiSplitTorus m)
    (SuzukiBorelSubgroup m) (suzukiRootSubgroup_isPGroup m hm)
    (suzukiBorelSubgroup_eq_sup m).symm (suzukiRootSubgroup_normal_in_borel m)

theorem hermitian_root_isPGroup {F : Type*} [Field F] [CharP F 2]
    (J : HermitianForm 3 F) : IsPGroup 2 (hermitianUnipotentCoord J) := by
  intro z
  refine ⟨2, ?_⟩
  have htwo : (2 : F) = 0 := by simpa using CharP.cast_eq_zero F 2
  have hdouble (x : F) : x + x = 0 := by linear_combination x * htwo
  change z ^ 4 = 1
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two, pow_two]
  apply Subtype.ext
  apply Prod.ext
  · change (z.val.1 + z.val.1) + (z.val.1 + z.val.1) = 0
    exact hdouble _
  · change (z.val.2 + z.val.2 - z.val.1 * J.conj z.val.1) +
        (z.val.2 + z.val.2 - z.val.1 * J.conj z.val.1) -
        (z.val.1 + z.val.1) * J.conj (z.val.1 + z.val.1) = 0
    rw [hdouble, hdouble, zero_mul, sub_zero]

theorem hermitian_root_normal {F : Type*} [Field F]
    (J : HermitianForm 3 F) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    ((hermitianUnipotentPSU J hJ).range.subgroupOf (unitaryBorel J hJ)).Normal := by
  let r := hermitianUnipotentPSU J hJ
  let t := hermitianTorusPSU J hJ
  have hconj (k : Fˣ) (z : hermitianUnipotentCoord J) :
      t k * r z * (t k)⁻¹ = r (hermitianTorusAction J k z) := by
    rw [hermitianTorusPSU_mul_unipotent, mul_inv_cancel_right]
  apply normal_subgroupOf_of_le_normalizer
  apply sup_le le_normalizer
  rintro _ ⟨k, rfl⟩
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨z, rfl⟩
    rw [hconj]
    exact ⟨_, rfl⟩
  · rintro ⟨z, hz⟩
    refine ⟨hermitianTorusAction J k⁻¹ z, ?_⟩
    rw [← hconj, map_inv, hz]
    dsimp only [t]
    group

theorem unitary_borel_cyclic_quotient {F : Type*} [Field F] [Finite F] [CharP F 2]
    (J : HermitianForm 3 F) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    IsCyclic (unitaryBorel J hJ ⧸ pCore 2 (unitaryBorel J hJ)) := by
  let r := hermitianUnipotentPSU J hJ
  let t := hermitianTorusPSU J hJ
  let : IsCyclic t.range := isCyclic_of_surjective t.rangeRestrict t.rangeRestrict_surjective
  exact cyclic_quotient_pCore_of_borel r.range t.range (unitaryBorel J hJ)
    ((hermitian_root_isPGroup J).of_surjective r.rangeRestrict r.rangeRestrict_surjective)
    rfl (hermitian_root_normal J hJ)

end Theory.SpecificGroups.BenderBorel
