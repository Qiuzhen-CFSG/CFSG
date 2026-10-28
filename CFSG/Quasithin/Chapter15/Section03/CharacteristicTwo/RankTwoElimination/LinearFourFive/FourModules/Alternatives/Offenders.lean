module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Alternatives.Offenders.Thompson
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.ModelCases
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Alternatives.Offenders.InnerAction
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.Quasithin.Rank

/-!
# The genuine B.5.1 input for the L₄ commutator module

The original conjugation representation on U_L = [W_L,L] satisfies every
field of FFInput. Maximum elementary subgroups of R produce offenders;
normality of the offender-generated subgroup and simplicity of L/O₂(L)
then give generation. Quasisimplicity gives the generalized Fitting
identity, and SQTK passes from I through L to its actual two-core quotient,
using the full KnownSimple.IsKnownSimple class.

The explicit earlier premises have their source meanings: hcore is
15.3.12(1); hW, hred, hLRcore and hJ are the span, two-reducedness,
core-bound and Thompson-commutator conclusions used in 15.3.16; hYL is
15.3.17(2). The centralizer bounds come from the earlier local setup.
The inner-action premise is the first paragraph of 15.3.24 and is supplied
from Preparation.IsInnerOnComponent by inner_on_join_of_sylow.
The elementary instance on U_L is supplied by commutator_elementary.

No FF hypothesis or module alternative is assumed. Applying B.5.1 and
excluding its orthogonal case remain with the classification assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.4–11,
B.5.1 and 15.3.12,16–17,24, printed pp.75–77,99 and 1124–1129.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Alternatives.Offenders
open RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization
variable {G : Type*} [Group G] [Finite G] (d : LocalData G)
  {I : Subgroup G} (c : ComponentWitness d I)

/-- The genuine SQTK hypothesis descends to the actual component quotient. -/
theorem core_sqtk (hSQTK : IsSQTK KnownSimple.IsKnownSimple I) :
    IsSQTK KnownSimple.IsKnownSimple (c.L ⧸ pCore 2 c.L) := by
  have hL : IsSQTK KnownSimple.IsKnownSimple c.L :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (component_le c))).mp
      (hSQTK.subgroup (c.L.subgroupOf I))
  refine ⟨?_, hL.isKGroup.quotient _⟩
  intro p hp ho
  let _ : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (hL.stronglyQuasithin p hp ho)

variable [IsElementaryAbelian 2 (d.componentSpan c.L)]
  [IsElementaryAbelian 2 (spanCommutator d c.L)]
  (hcore : c.L.pCoreIn 2 ≤ d.R) (hR : d.R ≤ centralizer (d.V : Set G))

/-- Every B.5.1 input field for the literal U_L representation, from the earlier source conclusions. -/
theorem ffInput
    (model : (c.L ⧸ pCore 2 c.L) ≃* Projective 4)
    (hSQTK : IsSQTK KnownSimple.IsKnownSimple I)
    (hYL : d.Yplus ≤ c.L)
    (hn : d.R ≤ normalizer (c.L : Set G))
    (hi : ∀ g : (c.L ⊔ d.R : Subgroup G),
      pCoreJoinAction 2 hn g ∈ MulAut.innerSubgroup (c.L ⧸ pCore 2 c.L))
    (hW : d.componentSpan c.L ≤ c.L ⊔ d.R)
    (hred : IsR2Within (d.componentSpan c.L) (c.L ⊔ d.R))
    (hLRcore : (c.L ⊔ d.R).pCoreIn 2 ≤ d.R)
    (hJ : c.L = ⁅c.L, Stellmacher.elementaryAbelianMaxJ d.R⁆)
    (hC : centralizer (d.V : Set G) ≤ d.M) :
    FFInput KnownSimple.IsKnownSimple (coreRepresentation d c.L hcore hR) ⊤ := by
  let _ : Group.IsPerfect c.L := component_perfect d c hYL
  let _ : IsSimpleGroup (Projective 4) := Atlas.psl_simple_high_rank 4 (by decide)
  let _ : IsSimpleGroup (c.L ⧸ pCore 2 c.L) := model.isSimpleGroup
  let _ := c.core_quotient_quasisimple
  have hq : Theory.GroupTheory.IsQuasisimple (⊤ : Subgroup (c.L ⧸ pCore 2 c.L)) :=
    Theory.GroupTheory.IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm
  have hf := coreRepresentation_faithful d c.L hcore hR model (commutator_ne_bot d c hC)
  have hff := coreRepresentation_isFFModule d c.L hn (core_center_eq_bot d c model)
    hi hW hred hcore hR hf hLRcore hJ
  have hgen : offenderSubgroup (coreRepresentation d c.L hcore hR) = ⊤ := by
    let _ := offenderSubgroup_normal (coreRepresentation d c.L hcore hR)
    apply (inferInstance : (offenderSubgroup (coreRepresentation d c.L hcore hR)).Normal).eq_bot_or_eq_top.resolve_left
    intro hb
    obtain ⟨A, hA⟩ := (isFFModule_iff_exists_bestOffender _).mp hff
    apply hA.1.1
    apply le_bot_iff.mp
    rw [← hb]
    exact le_iSup_of_le A (le_iSup_of_le ⟨hA, le_top⟩ le_rfl)
  refine ⟨inferInstance, hq, ?_, hf, pCore_quotient_pCore_eq_bot 2, hgen, ?_,
    coreRepresentation_full d c.L hcore hR⟩
  · exact (IsSQTK.equiv Subgroup.topEquiv).mpr (core_sqtk d c hSQTK)
  · rw [top_sup_eq]
    exact top_unique (Theory.GroupTheory.component_le_generalizedFitting _ ⊤
      ⟨(inferInstance : (⊤ : Subgroup (c.L ⧸ pCore 2 c.L)).Normal).isSubnormal, hq⟩)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Alternatives.Offenders

end
