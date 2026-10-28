module
public import Theory.SpecificGroups.SL2.SylowOvergroupComponentUnique
public import Theory.SpecificGroups.G2.OddSupplement

/-!
# Unique C-components in characteristic-two G₂ Sylow overgroups

The two actual root parabolics contain every proper full-Sylow overgroup.
Their solvable residuals have two-core quotient PSL₂ over the coefficient
field. These literal quotient isomorphisms prove the component restriction.
Source: Aschbacher--Smith A.3.12, pp.47--48; 1.2.8(1), p.506.
The imported octonion calculations retain the attribution in LICENSES/ATLAS.txt.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Atlas.G2
open LieParabolicSetup HigherFieldResiduals
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
theorem parabolic_sylow_component_unique (hq : 2 < Nat.card F) (i : Fin 2) :
    SylowOvergroupComponentUnique (parabolicAt (F := F) i) := by
  apply SylowOvergroupComponentUnique.of_residual_image _ _ (parabolicAt_residual hq i)
  let : Group.IsNilpotent (pCore 2 (HigherFieldResiduals.localAt (F := F) i)) := pCore_isNilpotent
  apply SylowOvergroupComponentUnique.of_quotient (pCore 2 (HigherFieldResiduals.localAt (F := F) i))
  exact SylowOvergroupComponentUnique.of_equiv (localCoreQuotientEquivPSL i)
    (Theory.PSL2.sylow_overgroup_component_unique F)

theorem sylow_overgroup_component_unique [IsSimpleGroup (Model F)] [Group.IsPerfect (Model F)]
    (hq : 2 < Nat.card F) : SylowOvergroupComponentUnique (Model F) := by
  apply SylowOvergroupComponentUnique.of_proper_conjugate_cover
  intro S P hSP hP
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Model F) S (sylow (F := F))
  let a := MulAut.conj g
  have hS : (S : Subgroup (Model F)).map a.toMonoidHom = unipotent :=
    congrArg Sylow.toSubgroup hg
  have hp : P.map a.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hP
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [ht,map_top_of_surjective _ a.surjective]
  obtain hp | hp := ProperSylowOvergroups.le_parabolic (P.map a.toMonoidHom)
    (hS ▸ map_mono hSP) (lt_top_iff_ne_top.mpr hp)
  · exact ⟨g,_,hp,parabolic_sylow_component_unique F hq 0⟩
  · exact ⟨g,_,hp,parabolic_sylow_component_unique F hq 1⟩
end Atlas.G2

