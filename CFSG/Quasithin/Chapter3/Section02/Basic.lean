module

public import CFSG.Quasithin.Chapter3.Section02.Setup
public import CFSG.Quasithin.Chapter3.Section02
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.NoncentralStructure
public import Theory.Representation.BinaryOffender.Homogeneous.TypeSelection

/-!
# Constituent selection and uniqueness in the Fundamental Setup

The constituent selection in Lemma 3.2.3 is applied to the literal reduced
module R₂(L₀T). It constructs a source Fundamental Setup while retaining an
equivariant isomorphism between the two central quotients. The uniqueness
conclusion comes from the actual Theorem 1.2.7 interface. The same setup
also discharges the internal-module premises of Lemma 3.2.11.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemmas 3.2.3 and 3.2.11, printed pp.580 and 585.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The constituent assertion of 3.2.3, including the original module type
modulo its centralizer. The homogeneous choice is constructed by A.1.42. -/
theorem lemma_3_2_3_constituent
    {K : GroupClass.{u}} (hG : IsSimpleQTKE K G) (T : Sylow 2 G) (L : Subgroup G)
    (hL : L ∈ Chapter1.LStar G (T : Subgroup G))
    (hf : ChapterA.Section04.IsFaithfulSignalizerType L)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (I : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup (localJoin T L))))
    (hI : IsIrrPlus (ReducedNormal.representation (localJoin T L))
      ((localOrbit T L).subgroupOf (localJoin T L)) I) :
    ∃ D : FundamentalSetup K T L,
      D.seedSpace ≤ orbitSpan (ReducedNormal.representation (localJoin T L))
        ((T : Subgroup G).subgroupOf (localJoin T L)) I ∧
      Nonempty (Representation.RepEquiv
        (centralQuotientRepresentation (ReducedNormal.representation (localJoin T L))
          ((localOrbit T L).subgroupOf (localJoin T L)) I hI.choose)
        (centralQuotientRepresentation (ReducedNormal.representation (localJoin T L))
          ((localOrbit T L).subgroupOf (localJoin T L)) D.seedSpace
            D.homogeneous.invariant)) := by
  let X := (localOrbit T L).subgroupOf (localJoin T L)
  have hnormal : X.Normal :=
    (normal_subgroupOf_iff_le_normalizer (show localOrbit T L ≤ localJoin T L from
      le_sup_left)).mpr
      (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T))
  have hT : (T : Subgroup G).subgroupOf (localJoin T L) ≤ normalizer X := by
    rw [normalizer_eq_top]
    exact le_top
  obtain ⟨J, hJI, hJ, he⟩ := exists_isIrrPlusWith_le_orbitSpan_sameModule
    (ReducedNormal.representation (localJoin T L)) hT T.isPGroup'.comap_subtype hI
  refine ⟨⟨hG, hL, hf, hq, J, hJ⟩, hJI, ?_⟩
  exact ⟨(centralImageRepEquiv _ _ _ hI.choose).trans
    (((sameModule_iff_repEquiv _ _).mp he).some.trans
      (centralImageRepEquiv _ _ _ hJ.invariant).symm)⟩

namespace FundamentalSetup
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup K T L)

/-- The uniqueness assertion of 3.2.3 from its named earlier source theorem. -/
theorem lemma_3_2_3_uniqueness
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L) :
    IsMaximalTwoLocal D.maximalLocal ∧ localJoin T L ≤ D.maximalLocal ∧
      ∀ M : Subgroup G, IsMaximalTwoLocal M → localJoin T L ≤ M →
        M = D.maximalLocal := by
  simpa only [localJoin, localOrbit, componentOrbit_sup] using
    And.intro h127.normalizer_maximal
      (And.intro h127.normalizer_contains h127.normalizer_unique)

/-- The source internal module supplies all structural premises of 3.2.11.
Only its additional hypothesis V = O₂(L₀T) and earlier uniqueness remain. -/
theorem lemma_3_2_11
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L)
    (hV : D.moduleSubgroup = (localJoin T L).pCoreIn 2) :
    (D.maximalLocal).pCoreIn 2 = D.moduleSubgroup ∧
      normalizer (D.moduleSubgroup : Set G) = D.maximalLocal ∧
      centralizer (D.moduleSubgroup : Set G) = D.moduleSubgroup ∧
      (((localJoin T L).subgroupOf (normalizer (D.moduleSubgroup : Set G))).map
          D.moduleSubgroup.normalizerMonoidHom =
        ((D.maximalLocal).subgroupOf (normalizer (D.moduleSubgroup : Set G))).map
          D.moduleSubgroup.normalizerMonoidHom → localJoin T L = D.maximalLocal) := by
  obtain ⟨hmax, hjoin, _⟩ := D.lemma_3_2_3_uniqueness h127
  let := D.module_elementary
  exact lemma_3_2_11_of_core_containment T (localOrbit T L) (localJoin T L)
    D.maximalLocal D.moduleSubgroup le_sup_right hjoin (le_sup_left.trans hjoin) rfl
    hmax (D.simpleQTKE.evenCharacteristic T D.maximalLocal hmax
      (le_sup_right.trans hjoin)) hV D.module_le_orbitCore D.module_ne_bot

end FundamentalSetup

/-- Lemma 3.2.3 with both conclusions, obtained from A.1.42 and the actual
earlier A.3.12/noncentral A.3.6 inputs to Theorem 1.2.7. These premises retain
their source owners; they are not assertions about the desired FSU module. -/
theorem lemma_3_2_3_of_noncentral_structure
    {K : GroupClass.{u}}
    (hContainment : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK K X → pCore 2 X = ⊥ → ∀ (S : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents S →
      ∃! C : Subgroup X, C.IsCComponent ∧ B ≤ C)
    (h36 : ChapterA.Section03.CComponentCommutation.NoncentralStructureInput K)
    (hG : IsSimpleQTKE K G) (T : Sylow 2 G) (L : Subgroup G)
    (hL : L ∈ Chapter1.LStar G (T : Subgroup G))
    (hf : ChapterA.Section04.IsFaithfulSignalizerType L)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (I : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup (localJoin T L))))
    (hI : IsIrrPlus (ReducedNormal.representation (localJoin T L))
      ((localOrbit T L).subgroupOf (localJoin T L)) I) :
    ∃ D : FundamentalSetup K T L,
      IsMaximalTwoLocal D.maximalLocal ∧ localJoin T L ≤ D.maximalLocal ∧
      (∀ M : Subgroup G, IsMaximalTwoLocal M → localJoin T L ≤ M →
        M = D.maximalLocal) ∧
      D.seedSpace ≤ orbitSpan (ReducedNormal.representation (localJoin T L))
        ((T : Subgroup G).subgroupOf (localJoin T L)) I ∧
      Nonempty (Representation.RepEquiv
        (centralQuotientRepresentation (ReducedNormal.representation (localJoin T L))
          ((localOrbit T L).subgroupOf (localJoin T L)) I hI.choose)
        (centralQuotientRepresentation (ReducedNormal.representation (localJoin T L))
          ((localOrbit T L).subgroupOf (localJoin T L)) D.seedSpace
            D.homogeneous.invariant)) := by
  obtain ⟨D, hDI, he⟩ := lemma_3_2_3_constituent hG T L hL hf hq I hI
  obtain ⟨hmax, hjoin, hu⟩ := D.lemma_3_2_3_uniqueness
    (Chapter1.Section02.nonsolvable_uniqueness_of_noncentral_structure
      hContainment h36 hG T hL)
  exact ⟨D, hmax, hjoin, hu, hDI, he⟩

end CFSG.Quasithin.Chapter3.Section02
