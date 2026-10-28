module
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.SectionActions.NormalJoin
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit

/-!
# Perfect-section bounds in the nonabelian chief-orbit branch

A component of a nonabelian chief subgroup is simple and perfect. Applying the
perfect-section invariant to its literal two-core quotient gives exactly the
`pCoreJoinAction` image required by the existing chief-orbit assembly. This
connects the alternative YT/quotient induction interface to that consumer.

The two orbit-diagonal and hyperplane-diagonal containment premises are retained
unchanged. Their proofs and the order induction remain separate source branches.

Source: Aschbacher--Smith, E.1.11, printed pp.212--214; the local generation
hypothesis on J N_T(J) is used on p.213.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- The weaker factor hypothesis supplies the exact action-image premise of
the nonabelian chief-orbit assembly, with no new simplicity or perfectness premise. -/
theorem PerfectSectionActionBound.chiefComponentAction {i : ℕ} (T : Sylow 2 G)
    (h : PerfectSectionActionBound i (T : Subgroup G)) {X J : Subgroup G}
    (hX : ChiefFactor.IsChief X ⊥) (hna : ¬ IsMulCommutative X)
    (hJ : IsComponentIn J X) :
    IsEGenerated i (pCoreJoinAction 2
      (show ChiefOrbit.stabilizer T J ≤ normalizer J from inf_le_right)).range := by
  have hJG : IsComponent G J :=
    ⟨Subgroup.IsSubnormal.trans hJ.1 hJ.2.1 hX.normal_upper.isSubnormal, hJ.quasisimple⟩
  let := hX.component_isSimple hna hJ
  let := (simpleComponentCoreEquiv J hJG).isSimpleGroup
  let : Group.IsPerfect J := hJ.quasisimple.toIsPerfect
  let : Group.IsPerfect (J ⧸ pCore 2 J) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
  let s := ChiefFactor.SimpleSection.coreSection 2 J hJG.1
  have hg := h _ s (inferInstanceAs (Group.IsPerfect J))
    (Group.IsPerfect.not_isMulCommutative _)
  exact hg.map_equiv (MulEquiv.subgroupCongr
    (ChiefFactor.SimpleSection.coreSection_extension 2 J (T : Subgroup G) hJG.1))

namespace ChiefOrbit

/-- The existing chief-orbit assembly accepts the perfect-section invariant.
The two geometric branches remain the same explicit source obligations. -/
theorem isEGenerated_of_perfectSections_and_component_branches {n : ℕ} (T : Sylow 2 G)
    (hX : ChiefFactor.IsChief (pResidual 2 G) ⊥)
    (hna : ¬ IsMulCommutative (pResidual 2 G))
    (h : PerfectSectionActionBound n (T : Subgroup G))
    (hmembers : ∀ (Ω : Set (Subgroup G)), IsElementaryFamily Ω →
      ∀ J : Subgroup G, IsComponentIn J (pResidual 2 G) →
        localNormalizer T J Ω ≤ generationTarget n T Ω →
        localEFamily n T J Ω ≤ generationTarget n T Ω)
    (hnormalizers : ∀ (Ω : Set (Subgroup G)), IsElementaryFamily Ω →
      ∀ J : Subgroup G, IsComponentIn J (pResidual 2 G) →
        localNormalizer T J Ω ≤ generationTarget n T Ω) :
    IsEGenerated n G :=
  isEGenerated_of_component_branches T hX hna
    (fun _ hJ => h.chiefComponentAction T hX hna hJ) hmembers hnormalizers

end ChiefOrbit
end CFSG.Quasithin.ChapterE
