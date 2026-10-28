module
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SolvableOvergroups
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCores
public import Theory.SpecificGroups.SymplecticFour.ParabolicCubicClosure
public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.FirstCohomologyDuality
public import Theory.Representation.SylowFixedCubicObstruction

/-!
# The Sylow fixed-space cubic obstruction in natural SL₃(4)

The upper unitriangular determinant-one group is a full Sylow two-subgroup.
Its fixed space is the first field line, fixed pointwise by the point local
subgroup. That subgroup maps onto SL₂(4) through its two-core, so its cubic
closure is nonsolvable. Sylow conjugacy supplies the same obstruction for
an arbitrary supplied Sylow, while solvable overgroups lie in its Borel.

Source: Aschbacher–Smith13.7.6(5), printed p.939.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Matrix
open scoped MatrixGroups
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.LinearThree
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [CharP F 2] [Algebra (ZMod 2) F] in
/-- The literal upper unitriangular Sylow in SL₃ over the four-element field. -/
noncomputable def fourUnipotentSLSylow (hF : Nat.card F = 4) : Sylow 2 SL(3,F) := by
  have hp : IsPGroup 2 (unipotentSL F) := IsPGroup.of_card (n := 6) (by
    rw [card_unipotentSL,hF]; norm_num)
  apply hp.toSylow
  have hc := (unipotentSL F).card_mul_index
  rw [card_unipotentSL,DefiningSylow.card_specialLinear,hF] at hc
  have hi : (unipotentSL F).index = 945 := by omega
  rw [hi]
  decide

omit [Algebra (ZMod 2) F] in
/-- Solvable overgroups of a full Sylow in SL₃(4) normalize it. -/
theorem four_solvable_sylow_overgroup_normalizes (hF : Nat.card F = 4)
    (S : Sylow 2 SL(3,F)) (J : Subgroup SL(3,F)) (hj : Group.IsSolvable J)
    (hSJ : (S : Subgroup SL(3,F)) ≤ J) : J ≤ normalizer (S : Set SL(3,F)) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(3,F) S (fourUnipotentSLSylow hF)
  let e := MulAut.conj g
  have hS : (S : Subgroup SL(3,F)).map e.toMonoidHom = unipotentSL F := by
    change ((g • S : Sylow 2 SL(3,F)) : Subgroup SL(3,F)) = _
    rw [hg]
    rfl
  let := hj
  let : Group.IsSolvable (J.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective J)
  have hn := (SolvableOvergroups.solvable_le_borelSL F (by omega)
    (J.map e.toMonoidHom) (hS ▸ map_mono hSJ)).trans
      (borelSL_le_normalizer_unipotentSL F)
  rw [←hS,←map_equiv_normalizer_eq (S : Subgroup SL(3,F)) e] at hn
  exact (map_le_map_iff_of_injective e.injective).mp hn

omit [Algebra (ZMod 2) F] in
/-- The point local cubic closure has nonsolvable SL₂ quotient. -/
theorem pointLocalSL_cubic_not_solvable (hF : 2 < Nat.card F) :
    ¬ Group.IsSolvable (closure {x : pointLocalSL F | orderOf x = 3}) := by
  intro hs
  let e := pointLocalSLCoreQuotientEquiv F
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (pointLocalSL F)))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hsModel := solvable_cubic_closure_of_two_kernel f hf hk hs
  rw [Theory.SpecificGroups.SymplecticFour.sl2_cubic_closure_eq_top hF] at hsModel
  let := hsModel
  let : Group.IsSolvable SL(2,F) := Group.isSolvable_of_surjective
    (f := (⊤ : Subgroup SL(2,F)).subtype) topEquiv.surjective
  let := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_perfect hF
  let := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple hF
  exact Group.IsPerfect.not_isSolvable SL(2,F) inferInstance

omit [Finite F] [CharP F 2] in
/-- The point local subgroup fixes every unipotent-fixed natural vector. -/
theorem pointLocalSL_fixes_unipotent_fixed_space
    (a : SL(3,F)) (ha : a ∈ pointLocalSL F) (v : Fin 3 → F)
    (hv : v ∈ fixedSpace (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3))
      (unipotentSL F)) :
    restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3) a v = v := by
  have hfix (x : U F) : (matrix F x).mulVec v = v :=
    hv ⟨specialLinear F x,(specialLinear_range F).le ⟨x,rfl⟩⟩
  have h₁ := congrFun (hfix ⟨1,0,0⟩) 0
  have h₂ := congrFun (hfix ⟨0,1,0⟩) 1
  simp [matrix, mulVec, dotProduct, Fin.sum_univ_three] at h₁ h₂
  obtain ⟨h00,h10,h20⟩ := (mem_pointLocalSL_iff F a).mp ha
  change a.val.mulVec v = v
  ext i
  fin_cases i <;> simp [mulVec,dotProduct,Fin.sum_univ_three,h₁,h₂,h00,h10,h20]

/-- Every supplied Sylow has a nonsolvable cubic subgroup in its natural fixed-space fixer. -/
theorem four_sylow_fixed_cubic_not_solvable (hF : Nat.card F = 4)
    (S : Sylow 2 SL(3,F)) :
    ¬ Group.IsSolvable (closure {a : subspaceKernel
      (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3))
      (fixedSpace (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3))
        (S : Subgroup SL(3,F))) ⊤ | orderOf a = 3}) := by
  apply Representation.cubic_sylow_fixer_not_solvable_of_standard
    (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3))
    (fourUnipotentSLSylow hF) (pointLocalSL F)
  · exact pointLocalSL_fixes_unipotent_fixed_space
  · exact pointLocalSL_cubic_not_solvable (by omega)
end Matrix.PSL3.LinearThree
