module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.BinaryG2
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.LocalGeometry
public import Theory.SpecificGroups.SU3.TernaryPerfectCover
public import Theory.GroupTheory.CComponent.QuotientLifting
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Geometry

/-!
# Excluding the literal binary-derived G₂ star row

The actual core-to-star map L/O₂(L) → L* is a perfect central cover.
When L* is the concrete commutator group G₂(2)′, the proved ternary-unitary
cover theorem makes its kernel a two-group. The trivial two-core of
L/O₂(L) kills that kernel. The resulting component-core model feeds the
original 15.3.21 exclusion, using the three-rank supplied by RankTwoCase.

The final application retains the actual star representation, its moved
section and the B.5 marked subgroup equivalence. It requires no block
reconstruction or additional multiplier hypothesis.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.21,
printed p.1127, C.2.7, printed pp.145–147, and I.1.3, printed p.407.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

/-- The literal core-to-star map is injective for the binary-derived G₂ model. -/
theorem coreToStar_injective_of_binaryG2_star
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hR : d.R ≤ normalizer (c.L : Set G))
    (e : starImage c.L d.R c.L ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    Function.Injective (coreToStar hR) := by
  let _ : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) :=
    Atlas.G2.isSimple_commutator_binary
  let _ : Nontrivial (starImage c.L d.R c.L) := e.symm.injective.nontrivial
  have hne : starImage c.L d.R c.L ≠ ⊥ := (nontrivial_iff_ne_bot _).mp inferInstance
  let f := coreStarCover hR c.core_quotient_quasisimple hne
  let g : PerfectCentralCovering.Cover (c.L ⧸ pCore 2 c.L)
      (commutator (Atlas.G2.Model (ZMod 2))) :=
    { toMonoidHom := e.toMonoidHom.comp f.toMonoidHom
      surjective := e.surjective.comp f.surjective
      isPerfect := f.isPerfect
      ker_le_center := by
        rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
        exact f.ker_le_center }
  have hk : IsPGroup 2 (coreToStar hR).ker := by
    have h := BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectCover.binaryDerived_kernel_isTwoGroup g
    change IsPGroup 2 (e.toMonoidHom.comp f.toMonoidHom).ker at h
    rwa [MonoidHom.ker_comp_of_injective _ _ e.injective] at h
  apply (MonoidHom.ker_eq_bot_iff _).mp
  have hle : (coreToStar hR).ker ≤ pCore 2 (c.L ⧸ pCore 2 c.L) :=
    le_sSup ⟨inferInstance, hk⟩
  exact eq_bot_iff.mpr (hle.trans
    (pCore_quotient_pCore_eq_bot (G := c.L) 2).le)

/-- The binary-derived star model also models the actual component core. -/
theorem core_quotient_binaryG2_of_star
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hR : d.R ≤ normalizer (c.L : Set G))
    (e : starImage c.L d.R c.L ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    Nonempty ((c.L ⧸ pCore 2 c.L) ≃* commutator (Atlas.G2.Model (ZMod 2))) :=
  ⟨(MulEquiv.ofBijective (coreToStar hR)
      ⟨coreToStar_injective_of_binaryG2_star d c hR e,
        coreToStar_surjective hR⟩).trans e⟩

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
include hG hempty hM hu hmany hI htwo hf

/-- The original rank-two source hypotheses exclude the binary-derived star model. -/
theorem source_15_3_21_binaryG2_star
    (e : starImage c.L d.R c.L ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨eCore⟩ := core_quotient_binaryG2_of_star d c h.normalizes e
  exact source_15_3_21_binaryG2_quotient hG d hempty hM hu hmany hI
    (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) c eCore

/-- The literal marked g2Two row contradicts the original rank-two source hypotheses. -/
theorem source_15_3_21_g2Two_row :
    let C := starImage c.L d.R c.L
    let J := offenderSubgroup (starRepresentation c.L d.R)
    ∀ (_hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation c.L d.R).comp J.subtype) (C.subgroupOf J))
      (H : Subgroup J),
      MarkedActionEquiv s.action H (C.subgroupOf J) (g2Natural (ZMod 2))
        (commutator (Atlas.G2.Model (ZMod 2))) → False := by
  intro C J hCJ s H e
  exact source_15_3_21_binaryG2_star hG d hempty hM hu hmany hI htwo hf c
    ((subgroupOfEquivOfLe hCJ).symm.trans e.subgroupEquiv)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
