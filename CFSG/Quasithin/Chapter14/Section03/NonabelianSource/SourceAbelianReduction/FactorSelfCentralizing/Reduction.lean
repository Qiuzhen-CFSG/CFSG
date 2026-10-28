module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.Component

/-!
# The remaining source branches of factor self-centralization

The strict-centralizer branch constructs a marked deleted point. Its four-center
geometry promotes the local Sylow subgroup; the global core and C-component
inputs then give an actual component with the original 1.1.5 model action.
Excluding those models proves the literal `FactorSelfCentralizing` assertion.

The three source families below remain explicit independent obligations.
In particular this conditional reduction does not prove original 14.3.20.
Source: Aschbacher--Smith, 14.3.20, printed pp.997--998.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}

/-- The center and product-fusion calculation in the actual marked model. -/
def FourCenterSource (F : InvariantFlag T V 2) (L : Subgroup G) : Prop :=
  ∀ A : Subgroup G, ElementaryFactor F L A → A < centralizer (A : Set G) →
    ∀ (P : MarkedPoint F L A) (z : G), F.Vi 1 = zpowers z → P.FourCenterGeometry z

/-- The global core and component argument may assume the independently
proved global Sylow assertion. -/
def CoreComponentSource (F : InvariantFlag T V 2) (L : Subgroup G) : Prop :=
  ∀ A : Subgroup G, ElementaryFactor F L A → A < centralizer (A : Set G) →
    ∀ (P : MarkedPoint F L A) (z : G), F.Vi 1 = zpowers z →
      P.FourCenterGeometry z → Chapter1.IsSylowIn 2 P.sylowCentralizer P.globalCentralizer →
      P.CoreComponentInputs z

/-- Exclude the actual marked 1.1.5 components, retaining the original
centralizer core and Sylow embedding as independent inputs. -/
def ModelExclusionSource (F : InvariantFlag T V 2) (L : Subgroup G) : Prop :=
  ∀ A : Subgroup G, ElementaryFactor F L A → A < centralizer (A : Set G) →
    ∀ (P : MarkedPoint F L A) (z : G), F.Vi 1 = zpowers z →
      P.FourCenterGeometry z → Chapter1.IsSylowIn 2 P.sylowCentralizer P.globalCentralizer →
      P.globalCentralizer.pCoreIn 2 = zpowers P.element →
      P.ClassifiedComponent z → False

/-- Assemble the three remaining geometric/model obligations on the original
factor. Solvability remains the independent premise of the parent task. -/
theorem factorSelfCentralizing_of_source_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hgeometry : FourCenterSource F (sourceResidual M Mc))
    (hcore : CoreComponentSource F (sourceResidual M Mc))
    (hexclude : ModelExclusionSource F (sourceResidual M Mc)) :
    FactorSelfCentralizing F (sourceResidual M Mc) := by
  intro A hEA hAR hVA hAc hc8 hAN
  let := hEA
  have hfactor : ElementaryFactor F (sourceResidual M Mc) A :=
    ⟨hEA, hAR, hVA, hAc, hc8, hAN⟩
  have hAC : A ≤ centralizer (A : Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
  by_contra hneA
  have hlt : A < centralizer (A : Set G) := lt_of_le_of_ne hAC hneA
  obtain ⟨P⟩ := markedPoint_of_strict_centralizer
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN hlt
  obtain ⟨z, _, hz⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hg := hgeometry A hfactor hlt P z hz
  have hSylow := (global_sylow_of_fourCenterGeometry
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    A hAR hVA hAc hc8 hAN hlt P z hz hg).2
  have hi := hcore A hfactor hlt P z hz hg hSylow
  have hVT := (source_lemma_14_2_4 hG T hempty hM hu hmany hcard e).seed_le_sylow
  exact hexclude A hfactor hlt P z hz hg hSylow hi.core_eq
    (P.classifiedComponent_of_coreComponentInputs hG hVA hVT z hz hSylow hi)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
