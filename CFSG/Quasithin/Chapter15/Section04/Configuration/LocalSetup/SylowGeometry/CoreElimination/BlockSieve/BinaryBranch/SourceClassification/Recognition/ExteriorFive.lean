module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Coordinates
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Setup
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.Representation.CubicFixedSpace
public import Theory.Representation.Quotient
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.BinaryBranch.SourceClassification
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.NativeSections
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Duality.Core

/-!
# Excluding exterior-five sections of the actual binary source actor

The radical of the standard natural two-plane in SL₅(2) fixes only its
exterior line in Λ²(F₂⁵). A cubic in the two-plane fixes that line, yielding
an outside-Sylow fixer. Complementary-wedge duality gives the cube case;
the proved ten-dimensional irreducible classification covers every section
in the exterior-five source row. The actual moved-section quotient then
lifts the cubic fixer to the original source module through both extensions.
The source seed centralizer excludes that fixer.

Source: Aschbacher--Smith, B.4.2(11), B.5.1 and 15.4.20, printed pp.86,
99 and 1164; I.1.6(7) supplies the ten-dimensional exterior recognition.
-/

public section

open Subgroup
open scoped IsMulCommutative
open Representation Representation.SL5TenDimensional Representation.SL5ExteriorSquare
open BinaryLinear.OuterCyclic

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.BinaryBranch.SourceClassification.Recognition.ExteriorFive
/-- The literal binary special linear group used by exterior recognition. -/
abbrev ModelGroup := Representation.SL5TenDimensional.Group
private noncomputable def R : Subgroup ModelGroup := (BinaryLinear.radical (naturalFlag 2)).comap
  (slEquivLinear 5).toMonoidHom
private def c : ModelGroup := elementary 0 1 * elementary 1 0
private theorem c_pow : c ^ 3 = 1 := by decide +kernel
private theorem c_ne : c ≠ 1 := by decide +kernel
private theorem R_two : IsPGroup 2 R :=
  (BinaryLinear.radical_two (naturalFlag 2)).comap_of_injective _ (slEquivLinear 5).injective

private theorem elementary_mem_R (i j : Fin 5) (hi : i.val < 2) (hj : 2 ≤ j.val) :
    elementary i j ∈ R := by
  have hij : i ≠ j := by intro he; subst j; omega
  constructor
  · intro v hv
    change ((elementary i j).val.mulVec v) = v
    simp only [elementary, dif_pos hij, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
    rw [hv j hj]
    simp
  · intro v k hk
    change (((elementary i j).val.mulVec v) - v) k = 0
    simp only [elementary, dif_pos hij, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec, add_sub_cancel_left]
    have hki : k ≠ i := by intro he; subst k; omega
    simp [hki]

private theorem fixed_coordinates (v : V)
    (hv : v ∈ BinaryOffender.fixedSpace (exteriorAction 2) R) :
    ∀ i : Fin 10, i ≠ 0 → coordinates v i = 0 := by
  have hh (i j : Fin 5) (hi : i.val < 2) (hj : 2 ≤ j.val) :
      (actionMatrix (elementary i j)).mulVec (coordinates v) = coordinates v := by
    rw [← coordinates_action]
    exact congrArg coordinates (hv ⟨elementary i j, elementary_mem_R i j hi hj⟩)
  have ha := hh 0 2 (by decide) (by decide)
  have hb := hh 0 3 (by decide) (by decide)
  have hc := hh 0 4 (by decide) (by decide)
  have hd := hh 1 2 (by decide) (by decide)
  have he := hh 1 3 (by decide) (by decide)
  have hf := hh 1 4 (by decide) (by decide)
  intro i hi
  fin_cases i
  · exact (hi rfl).elim
  · simpa [actionMatrix, elementary, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pair, Matrix.single_apply,
      Matrix.one_apply] using congrFun hd 0
  · simpa [actionMatrix, elementary, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pair, Matrix.single_apply,
      Matrix.one_apply] using congrFun he 0
  · simpa [actionMatrix, elementary, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pair, Matrix.single_apply,
      Matrix.one_apply] using congrFun hf 0
  · simpa [actionMatrix, elementary, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pair, Matrix.single_apply,
      Matrix.one_apply] using congrFun ha 0
  · simpa [actionMatrix, elementary, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pair, Matrix.single_apply,
      Matrix.one_apply] using congrFun hb 0
  · simpa [actionMatrix, elementary, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pair, Matrix.single_apply,
      Matrix.one_apply] using congrFun hc 0
  · simpa [actionMatrix, elementary, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pair, Matrix.single_apply,
      Matrix.one_apply] using congrFun ha 2
  · simpa [actionMatrix, elementary, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pair, Matrix.single_apply,
      Matrix.one_apply] using congrFun ha 3
  · simpa [actionMatrix, elementary, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pair, Matrix.single_apply,
      Matrix.one_apply] using congrFun hb 3

private theorem c_fixes (v : V)
    (hv : v ∈ BinaryOffender.fixedSpace (exteriorAction 2) R) : exteriorAction 2 c v = v := by
  apply coordinates.injective
  rw [coordinates_action]
  have hv' := fixed_coordinates v hv
  ext i
  fin_cases i <;>
    simp [actionMatrix, c, elementary, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pair, Matrix.single_apply,
      Matrix.one_apply, -coordinates_apply, hv', show (1 : ZMod 2) + 1 = 0 by decide]


/-- The exterior square has an outside-Sylow cubic fixing every Sylow-fixed vector. -/
theorem square_enlargement (S : Sylow 2 ModelGroup) :
    ∃ d : ModelGroup, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ BinaryOffender.fixedSpace (exteriorAction 2) (S : Subgroup ModelGroup),
        exteriorAction 2 d v = v :=
  BinaryOffender.sylow_fixedSpace_enlargement_of_cubic (exteriorAction 2) R R_two
    c c_pow c_ne c_fixes S

/-- Complementary wedges transport the same cubic witness to the exterior cube. -/
theorem cube_enlargement (S : Sylow 2 ModelGroup) :
    ∃ d : ModelGroup, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ BinaryOffender.fixedSpace (exteriorAction 3) (S : Subgroup ModelGroup),
        exteriorAction 3 d v = v := by
  apply Representation.BinarySylowFixedSpace.sylow_fixedSpace_enlargement_equivariant
    (exteriorAction 3) (exteriorAction 2) (S : Subgroup ModelGroup)
    SL5ExteriorSquare.Duality.graph SL5ExteriorSquare.Duality.hodge
    SL5ExteriorSquare.Duality.hodge_action
  exact square_enlargement (S.mapSurjective (f := SL5ExteriorSquare.Duality.graph.toMonoidHom)
    SL5ExteriorSquare.Duality.graph.surjective)

/-- Every irreducible ten-dimensional SL₅(2) module has the same fixed-space obstruction. -/
theorem ten_dimensional_enlargement
    {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) [IsIrreducible ρ]
    (e : A ≃* ModelGroup) (hdim : Module.finrank (ZMod 2) W = 10) (T : Sylow 2 A) :
    ∃ d : A, d ∉ T ∧ d ^ 3 = 1 ∧
      ∀ v ∈ BinaryOffender.fixedSpace ρ (T : Subgroup A), ρ d v = v := by
  let σ := ρ.comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective ρ).mpr
      inferInstance
  rcases SL5TenDimensional.Classification.identification_of_finrank_ten σ hdim with he | he
  · obtain ⟨f⟩ := he
    apply Representation.BinarySylowFixedSpace.sylow_fixedSpace_enlargement_equivariant
      ρ (exteriorAction 2) (T : Subgroup A) e f.toLinearEquiv
    · intro g v
      have hf := LinearMap.congr_fun (f.isIntertwining' (e g)) v
      change f.toLinearEquiv (ρ (e.symm (e g)) v) =
        exteriorAction 2 (e g) (f.toLinearEquiv v) at hf
      simpa only [e.symm_apply_apply] using hf
    · exact square_enlargement (T.mapSurjective (f := e.toMonoidHom) e.surjective)
  · obtain ⟨f⟩ := he
    apply Representation.BinarySylowFixedSpace.sylow_fixedSpace_enlargement_equivariant
      ρ (exteriorAction 3) (T : Subgroup A) e f.toLinearEquiv
    · intro g v
      have hf := LinearMap.congr_fun (f.isIntertwining' (e g)) v
      change f.toLinearEquiv (ρ (e.symm (e g)) v) =
        exteriorAction 3 (e g) (f.toLinearEquiv v) at hf
      simpa only [e.symm_apply_apply] using hf
    · exact cube_enlargement (T.mapSurjective (f := e.toMonoidHom) e.surjective)

open TwoFactors.FFBranch TwoFactors.FFBranch.ClassificationComparison
open TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

/-- The literal exterior-five moved section supplies a fixer on the original
module, without requiring either extension to split or the component to be whole. -/
theorem movedSection_enlargement
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} {L : Subgroup D}
    (s : MovedSection ρ L) (hirr : IsIrreducible (s.action.comp L.subtype))
    (e : L ≃* ModelGroup)
    (hdim : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 10)
    (S : Sylow 2 D) :
    ∃ d : D, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ BinaryOffender.fixedSpace ρ (S : Subgroup D), ρ d v = v := by
  let : IsIrreducible (s.action.comp L.subtype) := hirr
  let T : Sylow 2 L := Classical.choice inferInstance
  exact NativeSections.movedSection_enlargement s T
    (ten_dimensional_enlargement (s.action.comp L.subtype) e hdim T) S

/-- The source seed centralizer excludes the exterior-five row for the
actual offender actor and its actual moved-section quotient. -/
theorem sourceAction_not_exteriorFive
    {D : Type*} [Group D] [Finite D] {d : Source.Geometry D} {i j : Bool}
    {H U K : Subgroup D} (h : Input d i j H U K) :
    let := h.module_properties.1
    ∀ {L : Subgroup (sourceGroup h)} (s : MovedSection (V := Additive (moduleClosure (d.Z.subgroupOf H))) (sourceAction h) L),
      IsIrreducible (s.action.comp L.subtype) →
      (L ≃* ModelGroup) →
      Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 10 → False := by
  let := h.module_properties.1
  dsimp only
  intro L s hirr e hdim
  obtain ⟨S, hS⟩ := exists_offenderSylow h.placed.sylow (d.Z.subgroupOf H)
    h.seed_inputs.2.2.1
  obtain ⟨x, hx, _, hfix⟩ := movedSection_enlargement s hirr e hdim S
  change ∀ v ∈ BinaryOffender.fixedSpace
      (offenderAction h.placed.sylow (d.Z.subgroupOf H) h.seed_inputs.2.2.1)
        (S : Subgroup _),
      offenderAction h.placed.sylow (d.Z.subgroupOf H) h.seed_inputs.2.2.1 x v = v at hfix
  exact offenderAction_no_fixedSpace_enlargement h.placed.sylow (d.Z.subgroupOf H)
    h.seed_inputs.2.2.1 (S : Subgroup _) hS x hx hfix

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.BinaryBranch.SourceClassification.Recognition.ExteriorFive
