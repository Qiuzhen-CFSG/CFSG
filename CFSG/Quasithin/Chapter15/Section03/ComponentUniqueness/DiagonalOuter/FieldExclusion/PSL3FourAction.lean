module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.ModelAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.PSL3FourAction.Descent
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.PSL3FourAction.FixedIndex
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.PSL3FourAction.InnerPlane
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.PSL3FourAction.OuterPlane

/-!
# The PSL₃(4) component action calculation

The TI plane has a fixed subgroup normal of index at most two in each of its
nonidentity actors' fixed subgroups. Descent through the specified equivalence
K/Z(K) ≃ PSL₃(4) is faithful on automorphisms, detects innerness, and preserves
the three-core of the actual joint-centralizer action image. In particular,
these steps apply to genuine central covers, including the SL₃(4) alternative.

The outer-plane calculation forces a nonidentity inner actor. The inner-plane
calculation then gives a trivial three-core in the actual joint-centralizer
action image. Consequently the E₉ joint residual centralizes K, contradicting
the complete component-centralizer alternative, including its exceptional
cover branch. Both model calculations are discharged; only the actual local
witnesses remain as inputs. Component selection and the other model branches
belong to the parent field-exclusion argument.

The older conditional projective-image transfer is retained. The completed
local calculation uses the stronger TI fixed-centralizer index constraint;
it does not assert `ThreeCoreFreeAction` from `FixesTwoPerfectSubgroups` alone.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
15.3.38, printed p.1137. `JointCentralizer` explains the correction from the
printed order-27 residual to the actual E₉ joint residual used here.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.PSL3FourAction
variable {G : Type*} [Group G] [Finite G]

/-- The projective-image calculation gives the required containment, through
the actual covering map. Its three-core hypothesis remains a model obligation. -/
theorem jointResidual_le_centralizer_of_projective_threeCore
    (U K : Subgroup G) [IsQuasisimple K] (f : G)
    (eK : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL)
    (eR : jointResidual U f ≃* ElementaryNine)
    (hJN : jointCentralizer U f ≤ normalizer (K : Set G))
    (hcore : pCore 3 ((jointAction U K f hJN).range.map (projectiveAutMap eK)) = ⊥) :
    jointResidual U f ≤ centralizer (K : Set G) := by
  apply jointResidual_le_centralizer_of_threeCore U K f eR hJN
  exact (projective_threeCore_eq_bot_iff eK _).mp hcore

/-- The E₉ joint residual centralizes a relatively normal quasisimple PSL₃(4)
cover acted on by a TI four-group. All model calculations are discharged,
without restricting the center or assuming surjectivity of fixed-point descent. -/
theorem jointResidual_le_centralizer
    (U K : Subgroup G) [IsKleinFour U] [IsQuasisimple K] (f : G)
    (hTI : CFSG.Quasithin.ChapterI.Section06To08.IsTISubgroup U)
    (hKf : K ≤ centralizer ({f} : Set G))
    (hn : (K.subgroupOf (centralizer ({f} : Set G))).Normal)
    (hUf : U ≤ centralizer ({f} : Set G))
    (eK : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL)
    (eR : jointResidual U f ≃* ElementaryNine) :
    jointResidual U f ≤ centralizer (K : Set G) := by
  obtain ⟨hUN, hinner⟩ := OuterPlane.exists_inner_actor U K hTI f hKf hn hUf eK
  have hJN : jointCentralizer U f ≤ normalizer (K : Set G) :=
    inf_le_right.trans ((normal_subgroupOf_iff_le_normalizer hKf).mp hn)
  have hfree := InnerPlane.threeCoreFreeAction_of_inner eK
    (K.normalizerMonoidHom.comp (inclusion hUN))
    (faithful_action_of_jointResidual_model U K f hTI hKf hUN eR)
    (conjugation_fixedCentralizerControl U K hTI hUN) hinner
  exact jointResidual_le_centralizer_of_threeCore U K f eR hJN
    (hfree _ (jointAction_range_le_centralizer U K f hUN hJN)
      (fixed_inner_le_jointAction_range U K f hKf hUN hJN))

/-- The PSL₃(4) component alternative is impossible under the actual local
witnesses, including the full exceptional-cover centralizer alternative. -/
theorem contradiction
    (U K : Subgroup G) [IsKleinFour U] [IsQuasisimple K] (f : G)
    (hTI : CFSG.Quasithin.ChapterI.Section06To08.IsTISubgroup U)
    (hKf : K ≤ centralizer ({f} : Set G))
    (hn : (K.subgroupOf (centralizer ({f} : Set G))).Normal)
    (hUf : U ≤ centralizer ({f} : Set G))
    (eK : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL)
    (eR : jointResidual U f ≃* ElementaryNine)
    (hC : FieldComponentCentralizerAlternative (centralizer ({f} : Set G)) K) :
    False :=
  jointResidual_not_le_component_centralizer U K f eR hC
    (jointResidual_le_centralizer U K f hTI hKf hn hUf eK eR)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.PSL3FourAction
