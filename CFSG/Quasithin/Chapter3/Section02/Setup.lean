module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import CFSG.Quasithin.ChapterA.Section04.Defs
public import Theory.GroupTheory.ReducedNormal.Representation

/-!
# The Fundamental Setup of Hypothesis 3.2.1

The local component belongs to the original maximal faithful family and has
quasisimple two-core quotient. L₀ is its T-conjugate closure. The chosen
constituent is an actual homogeneous Irr⁺ subspace of R₂(L₀T), under literal
conjugation. Its ambient image is V◦; V and V_M are the indicated conjugate
closures, and M is the full normalizer of L₀.

Only the source hypotheses are fields. Maximal two-locality, uniqueness,
reducedness, module decompositions and centralizer bounds are conclusions
to be proved in the following module, not conditions imposed on the setup.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Hypothesis 3.2.1, printed p.579, with Definitions 1.2.3 and A.1.40.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The source L₀ = ⟨Lᵀ⟩, before adjoining T. -/
abbrev localOrbit (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  componentOrbit L (T : Subgroup G)

/-- The group L₀T on whose actual reduced-two subgroup the seed is chosen. -/
abbrev localJoin (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  localOrbit T L ⊔ (T : Subgroup G)

/-- The original homogeneous Irr⁺ choice; the nontrivial central quotient
and the full homogeneous-component equality are contained in IsIrrPlusWith. -/
structure FundamentalSetup (K : GroupClass.{u}) (T : Sylow 2 G) (L : Subgroup G) where
  simpleQTKE : IsSimpleQTKE K G
  maximal : L ∈ Chapter1.LStar G (T : Subgroup G)
  faithful : ChapterA.Section04.IsFaithfulSignalizerType L
  quasisimple : IsQuasisimple (L ⧸ pCore 2 L)
  seedSpace : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup (localJoin T L)))
  homogeneous : IsIrrPlusWith (ReducedNormal.representation (localJoin T L))
    ((localOrbit T L).subgroupOf (localJoin T L))
    ((T : Subgroup G).subgroupOf (localJoin T L)) seedSpace

namespace FundamentalSetup
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup K T L)

/-- The chosen constituent V◦, as a subgroup of the original G. -/
def seed : Subgroup G := ReducedNormal.subspaceImage (localJoin T L) D.seedSpace

/-- V = ⟨V◦ᵀ⟩. -/
def moduleSubgroup : Subgroup G := componentOrbit D.seed (T : Subgroup G)

/-- M = N_G(L₀). -/
abbrev maximalLocal (_D : FundamentalSetup K T L) : Subgroup G :=
  normalizer (localOrbit T L : Set G)

/-- V_M = ⟨Vᴹ⟩, retaining the source's order of construction. -/
def fullModule : Subgroup G := componentOrbit D.moduleSubgroup D.maximalLocal

/-- M_V = N_M(V), with normalization relative to M. -/
def moduleNormalizer : Subgroup G := D.maximalLocal ⊓ normalizer (D.moduleSubgroup : Set G)

theorem seed_le_reduced : D.seed ≤
    (ReducedNormal.ModuleGroup (localJoin T L)).map (localJoin T L).subtype :=
  ReducedNormal.subspaceImage_le_reduced _ _

theorem seed_elementary : IsElementaryAbelian 2 D.seed :=
  ReducedNormal.subspaceImage_elementary _ _

theorem seed_ne_bot : D.seed ≠ ⊥ :=
  ReducedNormal.subspaceImage_ne_bot _ _
    (D.homogeneous.isIrrPlus.ne_bot _)

theorem seed_le_core : D.seed ≤ (localJoin T L).pCoreIn 2 :=
  ReducedNormal.subspaceImage_le_core _ _

theorem seed_le_sylow : D.seed ≤ (T : Subgroup G) := by
  apply D.seed_le_core.trans
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
    pCoreIn_le_sylow (localJoin T L) (T.subtype le_sup_right)

theorem orbit_normalizes_seed : localOrbit T L ≤ normalizer (D.seed : Set G) :=
  ReducedNormal.subspaceImage_normalizes _ _ le_sup_left _ D.homogeneous.invariant

theorem module_eq_subspaceImage :
    D.moduleSubgroup = ReducedNormal.subspaceImage (localJoin T L)
      (orbitSpan (ReducedNormal.representation (localJoin T L))
        ((T : Subgroup G).subgroupOf (localJoin T L)) D.seedSpace) :=
  (ReducedNormal.subspaceImage_orbitSpan _ _ le_sup_right _).symm

theorem module_le_reduced : D.moduleSubgroup ≤
    (ReducedNormal.ModuleGroup (localJoin T L)).map (localJoin T L).subtype := by
  rw [D.module_eq_subspaceImage]
  exact ReducedNormal.subspaceImage_le_reduced _ _

theorem module_elementary : IsElementaryAbelian 2 D.moduleSubgroup := by
  rw [D.module_eq_subspaceImage]
  exact ReducedNormal.subspaceImage_elementary _ _

theorem module_ne_bot : D.moduleSubgroup ≠ ⊥ := by
  intro he
  exact D.seed_ne_bot (bot_unique ((le_componentOrbit D.seed T).trans_eq he))

theorem module_le_core : D.moduleSubgroup ≤ (localJoin T L).pCoreIn 2 := by
  rw [D.module_eq_subspaceImage]
  exact ReducedNormal.subspaceImage_le_core _ _

theorem module_le_sylow : D.moduleSubgroup ≤ (T : Subgroup G) := by
  apply D.module_le_core.trans
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
    pCoreIn_le_sylow (localJoin T L) (T.subtype le_sup_right)

theorem sylow_normalizes_module :
    (T : Subgroup G) ≤ normalizer (D.moduleSubgroup : Set G) :=
  le_normalizer_componentOrbit _ _

theorem orbit_normalizes_module : localOrbit T L ≤ normalizer (D.moduleSubgroup : Set G) := by
  rw [D.module_eq_subspaceImage]
  apply ReducedNormal.subspaceImage_normalizes _ _ le_sup_left
  exact orbitSpan_component_invariant _ D.homogeneous.normalizes D.homogeneous.isIrrPlus

theorem join_normalizes_module : localJoin T L ≤ normalizer (D.moduleSubgroup : Set G) :=
  sup_le D.orbit_normalizes_module D.sylow_normalizes_module

theorem module_le_orbit : D.moduleSubgroup ≤ localOrbit T L := by
  rw [D.module_eq_subspaceImage]
  apply ReducedNormal.subspaceImage_le_of_full_commutator _ _
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T))
  exact orbitSpan_full_commutator _ D.homogeneous.normalizes D.homogeneous.isIrrPlus

/-- The core containment used later by 3.2.11 follows from the actual
commutator-generated seed and relative normality, without D.3 classification. -/
theorem module_le_orbitCore : D.moduleSubgroup ≤ (localOrbit T L).pCoreIn 2 := by
  let := D.module_elementary
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 _)
    D.module_le_orbit D.orbit_normalizes_module

theorem core_centralizes_module :
    (localJoin T L).pCoreIn 2 ≤ centralizer (D.moduleSubgroup : Set G) := by
  rw [D.module_eq_subspaceImage]
  exact ReducedNormal.subspaceImage_core_centralizes _ _

theorem fullModule_le_orbit : D.fullModule ≤ localOrbit T L :=
  iSup_conjugates_le_of_le_normalizer _ _ _ D.module_le_orbit le_rfl

theorem maximalLocal_normalizes_fullModule :
    D.maximalLocal ≤ normalizer (D.fullModule : Set G) :=
  le_normalizer_componentOrbit _ _

/-- The two source notations for V_M agree because T is contained in M. -/
theorem fullModule_eq_seed_orbit : D.fullModule = componentOrbit D.seed D.maximalLocal := by
  have hV : D.moduleSubgroup ≤ componentOrbit D.seed D.maximalLocal :=
    iSup_le fun t => le_iSup_of_le
      (⟨t.val, le_normalizer_componentOrbit L T t.property⟩ : D.maximalLocal) le_rfl
  apply le_antisymm
  · exact iSup_conjugates_le_of_le_normalizer _ _ _ hV (le_normalizer_componentOrbit _ _)
  · exact iSup_le fun m => (map_mono (le_componentOrbit D.seed T)).trans
      (le_iSup (fun n : D.maximalLocal =>
        D.moduleSubgroup.map (MulAut.conj n.val).toMonoidHom) m)

/-- The actual conjugation map on V with domain M_V. -/
def moduleAction : D.moduleNormalizer →* MulAut D.moduleSubgroup :=
  D.moduleSubgroup.normalizerMonoidHom.comp (inclusion inf_le_right)

/-- C_{M_V}(V) inside M_V, rather than an independent quotient kernel. -/
def moduleCentralizer : Subgroup D.moduleNormalizer :=
  (centralizer (D.moduleSubgroup : Set G)).subgroupOf D.moduleNormalizer

theorem moduleAction_ker : D.moduleAction.ker = D.moduleCentralizer := by
  ext x
  change D.moduleSubgroup.normalizerMonoidHom (inclusion inf_le_right x) = 1 ↔ _
  rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
  rfl

instance moduleCentralizer_normal : D.moduleCentralizer.Normal := by
  rw [← D.moduleAction_ker]
  infer_instance

/-- The source M̄_V = M_V/C_{M_V}(V). -/
abbrev moduleActionQuotient := D.moduleNormalizer ⧸ D.moduleCentralizer

/-- C_{V_M}(L₀) inside the actual conjugate closure V_M. -/
def fullCentralizer : Subgroup D.fullModule :=
  (centralizer (localOrbit T L : Set G)).subgroupOf D.fullModule

instance fullCentralizer_normal : D.fullCentralizer.Normal := by
  let f := inclusion (D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer)
  change (((centralizer (localOrbit T L : Set G)).subgroupOf
    (normalizer (localOrbit T L : Set G))).comap f).Normal
  infer_instance

/-- The source Ṽ_M = V_M/C_{V_M}(L₀). -/
abbrev fullCentralQuotient := D.fullModule ⧸ D.fullCentralizer

end FundamentalSetup
end CFSG.Quasithin.Chapter3.Section02
