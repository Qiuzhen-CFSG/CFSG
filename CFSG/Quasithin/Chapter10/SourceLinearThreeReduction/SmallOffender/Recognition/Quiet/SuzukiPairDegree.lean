module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Quiet.SuzukiCentralizer
public import Theory.Representation.Suzuki.ComponentPairDegree
public import Theory.Representation.CliffordSubquotient

/-!
# Degree of sections of the quiet Suzuki orbit

The literal full action contains two distinct conjugate Suzuki components.
Both have zero fixed space. Clifford semisimplicity and the Suzuki pair degree
bound imply that every nonzero orbit submodule has binary dimension at least
8(2m+1), and hence at least 24.

Source: Aschbacher–Smith, 10.1.1 and 10.2.12 (printed pp.741–742, 754–755).
-/

public noncomputable section
open scoped IsMulCommutative MonoidAlgebra
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02 BenderSuzuki.MatrixGroups PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem quiet_suzuki_orbit_submodule_degree
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {m : ℕ} (hm : 1 ≤ m) (e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let := (source_full_module_reduced D).elementary
    let q := ChapterB.InternalThompsonAction.actionMk U
    let ρ := ChapterB.InternalThompsonAction.action U
    let X := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    ∀ W : Subrepresentation (ρ.comp X.subtype), W ≠ ⊥ →
      8 * (2*m+1) ≤ Module.finrank (ZMod 2) W.toSubmodule := by
  dsimp only
  let M := D.maximalLocal
  let R := localOrbit T L
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let Q := M ⧸ centralizer (U : Set M)
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let X := (R.subgroupOf M).map q
  let A := L.subgroupOf M
  let S := A.map q
  have hLM : L ≤ M := (le_componentOrbit L T).trans R.le_normalizer
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp c.nonnormal
  let tM : M := ⟨t,le_normalizer_componentOrbit L T ht⟩
  let K := S.map (MulAut.conj (q tM)).toMonoidHom
  obtain ⟨hS,hK,hne⟩ := ModuleChoice.full_action_component_pair D ht htn
  have hKeq : (A.map (MulAut.conj tM).toMonoidHom).map q = K := by
    dsimp only [K,S]
    rw [map_map,map_map]
    congr 1
  rw [hKeq] at hK hne
  obtain ⟨a⟩ := ModuleChoice.full_action_original_component_equiv D c.nonnormal
  let eS : S ≃* SuzukiMatrixGroup m := a.trans e
  let : Fact (0 < m) := ⟨by omega⟩
  let : IsSimpleGroup S := eS.isSimpleGroup
  let : IsQuasisimple S := hS.2
  let : IsSimpleGroup K := (((MulAut.conj (q tM)).subgroupMap S).symm.trans eS).isSimpleGroup
  let : IsQuasisimple K := hK.2
  have hZS : center S = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative S (center_eq_top_iff.mp h))
  have hZK : center K = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp h))
  have hfull := quiet_suzuki_moved_eq_full D c hJ hNL hm e
  have hz := quiet_moved_fixed_eq_bot D c.many c.minimal c.nonnormal hJ
  rw [hfull] at hz
  have hfixS : fixedSpace ρ S = ⊥ := by
    apply bot_unique
    intro v hv
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    apply hz.le
    refine ⟨v.toMul.property,?_⟩
    intro l hl
    let lM : M := ⟨l,hLM hl⟩
    have hh := hv ⟨q lM,mem_map_of_mem q hl⟩
    have hact := ChapterB.InternalThompsonAction.action_apply U lM v
    have he : l * (v.toMul : G) * l⁻¹ = (v.toMul : G) := by
      exact (congrArg (fun x : M => (x : G)) hact).symm.trans
        (congrArg (fun x : Additive U => ((x.toMul : M) : G)) hh)
    exact mul_inv_eq_iff_eq_mul.mp he
  have hfixK : fixedSpace ρ K = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    rw [←(fixedSpaceConjEquiv ρ S (q tM)).finrank_eq,hfixS,finrank_bot]
  let : ρ.IsIrreducible := ModuleChoice.quiet_full_action_irreducible D c.many c.minimal hJ
  let : IsSemisimpleModule (ZMod 2)[S] (Representation.asModule (ρ.comp S.subtype)) :=
    subnormal_restriction_semisimple ρ S hS.1
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : X.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hSX : S ≤ X := map_mono (comap_mono (le_componentOrbit L T))
  have hKX : K ≤ X := by
    rintro _ ⟨s,hs,rfl⟩
    exact (inferInstance : X.Normal).conj_mem s (hSX hs) (q tM)
  intro W hW
  let P : Subrepresentation (ρ.comp (S ⊔ K).subtype) := {
    toSubmodule := W.toSubmodule
    apply_mem_toSubmodule x v hv := W.apply_mem_toSubmodule
      ⟨x.val,(sup_le hSX hKX) x.property⟩ hv }
  have hP : P ≠ ⊥ := by
    intro he
    exact hW (Subrepresentation.toSubmodule_injective
      (congrArg (fun Z : Subrepresentation (ρ.comp (S ⊔ K).subtype) => Z.toSubmodule) he))
  exact Suzuki.pair_subrepresentation_finrank_ge ρ S K hS hK hne hZS hZK
    hfixS hfixK m (by omega) eS P hP

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
