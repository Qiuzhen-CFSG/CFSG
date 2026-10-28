module
public import Theory.SpecificGroups.SymplecticFour.ParabolicCubicClosure
public import Theory.SpecificGroups.SymplecticFour.Sylow.ThreeResidualPlacement
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Theory.Representation.SymplecticNatural
public import Theory.Representation.FirstCohomologyDuality
public import Theory.Representation.SylowFixedCubicObstruction

/-!
# Cubic obstruction in the Sylow fixed-space fixer of Sp₄(4)

The point local subgroup fixes the full standard Sylow fixed line and
surjects onto SL₂ with two-group kernel. Its cubic closure is nonsolvable.
Sylow conjugacy transfers this obstruction to every Sylow of the natural
binary action. A solvable Sylow overgroup normalizes that Sylow by the
intrinsic parabolic placement theorem.

Source: Aschbacher–Smith13.7.6(5), printed p.939.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Matrix
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Algebra (ZMod 2) F] in
/-- Cubics in the point local subgroup have a nonsolvable SL₂ quotient. -/
theorem pointLocal_cubic_not_solvable (hF : 2 < Nat.card F) :
    ¬ Group.IsSolvable (closure {x : pointLocal (F := F) | orderOf x = 3}) := by
  intro hs
  have hsModel := solvable_cubic_closure_of_two_kernel pointQuotient pointQuotient_surjective
    (IsElementaryAbelian.isPGroup 2 (pointRadical (F := F))) hs
  rw [sl2_cubic_closure_eq_top hF] at hsModel
  let := hsModel
  let : Group.IsSolvable (SpecialLinearGroup (Fin 2) F) :=
    Group.isSolvable_of_surjective (f := (⊤ : Subgroup (SpecialLinearGroup (Fin 2) F)).subtype)
      topEquiv.surjective
  let := NaturalExtension.model_perfect hF
  let := NaturalExtension.model_simple hF
  exact Group.IsPerfect.not_isSolvable (SpecialLinearGroup (Fin 2) F) inferInstance

omit [Algebra (ZMod 2) F] in
/-- Every solvable Sylow overgroup normalizes its supplied Sylow. -/
theorem solvable_sylow_overgroup_normalizes (hF : 2 < Nat.card F)
    (S : Sylow 2 (Sp F)) (J : Subgroup (Sp F)) (hj : Group.IsSolvable J)
    (hSJ : (S : Subgroup (Sp F)) ≤ J) : J ≤ normalizer (S : Set (Sp F)) := by
  let := hj
  have hproper : J ≠ ⊤ := by
    intro he
    have ht : Group.IsSolvable (⊤ : Subgroup (Sp F)) := he ▸ hj
    let := ht
    let : Group.IsSolvable (Sp F) := Group.isSolvable_of_surjective
      (f := (⊤ : Subgroup (Sp F)).subtype) topEquiv.surjective
    have hs : Group.IsSolvable (closure {x : pointLocal (F := F) | orderOf x = 3}) :=
      inferInstance
    exact pointLocal_cubic_not_solvable hF hs
  exact ThreeResidualPlacement.proper_sylow_overgroup_le_normalizer hF S J hSJ hproper
    inferInstance

omit [Finite F] [CharP F 2] in
/-- The point local subgroup fixes every vector fixed by the standard unipotent. -/
theorem pointLocal_fixes_unipotent_fixed_space
    (a : Sp F) (ha : a ∈ pointLocal (F := F))
    (v : (Fin 2 ⊕ Fin 2) → F)
    (hv : v ∈ fixedSpace (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2))
      (unipotent (F := F))) :
    restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2) a v = v := by
  have hpoint : v ∈ point F := (fixedBy_unipotent_iff v).mp (by
    intro u hu
    exact hv ⟨u,hu⟩)
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hpoint
  change symplecticNatural (k := F) 2 a (c • e 0) = c • e 0
  rw [map_smul]
  have hf : symplecticNatural (k := F) 2 a (e 0) = e 0 :=
    (mem_pointLocal_iff_fixed a).mp ha
  rw [hf]

/-- The literal binary natural action has a nonsolvable Sylow fixed-space cubic fixer. -/
theorem four_sylow_fixed_cubic_not_solvable (hF : Nat.card F = 4)
    (S : Sylow 2 (Sp F)) :
    ¬ Group.IsSolvable (closure {a : subspaceKernel
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2))
      (fixedSpace (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2))
        (S : Subgroup (Sp F))) ⊤ | orderOf a = 3}) := by
  let S₀ := unipotentSylow (n := 2) (by simpa using hF) (by decide)
  apply Representation.cubic_sylow_fixer_not_solvable_of_standard
    (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)) S₀ (pointLocal (F := F))
  · exact pointLocal_fixes_unipotent_fixed_space
  · exact pointLocal_cubic_not_solvable (by omega)
end Theory.SpecificGroups.SymplecticFour
