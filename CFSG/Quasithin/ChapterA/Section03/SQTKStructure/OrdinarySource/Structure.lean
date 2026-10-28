module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Catalogue
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremC
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.NilpotentRadical
public import Theory.GroupTheory.CComponent.FittingCentralizer
/-!
# Source assembly of A.3.6

Central Fitting subgroup makes a C-component ordinary. Genuine Theorem A
applies to its semisimple radical quotient, and Theorem C gives the full
model list. The catalogue reduces the odd-center calculations to the three
explicit Ree, Held and J₄ inputs; the noncentral branch is already proved.
The final universal theorem remains conditional on these earlier inputs.

Source: Aschbacher–Smith A.3.6, printed pp.43–45.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.SQTKStructure
open Chapter1.Section02
universe u

/-- A C-component with central Fitting subgroup is an ordinary component;
Theorem A and C apply to its literal radical quotient. -/
theorem ordinary_model_of_central_fitting
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremC KnownSimple.IsKnownSimple X)
    {G : Type u} [Group G] [Finite G]
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (L : Subgroup G) (hL : L.IsCComponent)
    (hf : fittingSubgroup L ≤ center L) :
    IsComponent G L ∧ LocalModels.TheoremCModel (L ⧸ center L) := by
  have hr : solvableRadical L = center L := le_antisymm
    (solvableRadical_le_center_of_fitting_le_center hf)
    (le_solvableRadical _ inferInstance
      (Group.isSolvable_of_comm (fun a b => Subtype.ext
        (mem_center_iff.mp a.property b).symm)))
  let : Group.IsPerfect L := hL.perfect
  let : IsSimpleGroup (L ⧸ solvableRadical L) := hL.isSimpleGroup_quotient_solvableRadical
  let : Group.IsPerfect (L ⧸ solvableRadical L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  let e := QuotientGroup.quotientMulEquivOfEq hr
  let : IsQuasisimple L := ⟨e.symm.isSimpleGroup⟩
  have hsq := Section03.SourceComponents.GenerationCore.radical_quotient_sqtk hA hG hL
  have hm := (hC (L ⧸ solvableRadical L)) inferInstance
    hL.not_isMulCommutative_quotient_solvableRadical hsq.stronglyQuasithin hsq.isKGroup
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Group.IsPerfect (L ⧸ center L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  exact ⟨⟨hL.subnormal, inferInstance⟩,
    Section03.SourceComponents.sourceTheoremC_to_local
      (Group.IsPerfect.not_isMulCommutative (L ⧸ center L))
      (hm.of_mulEquiv e.symm)⟩

/-- Assembly of A.3.6 from genuine earlier A/C and the three remaining
odd-primary kernel calculations. The noncentral-Fitting branch is unconditional. -/
theorem a36Input_of_theoremsAC_and_odd_covers
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hrem : OrdinarySource.RemainingOddCoverInputs.{u}) :
    A36Input.{u} KnownSimple.IsKnownSimple := by
  intro G _ _ hG hcore L hL
  by_cases hf : fittingSubgroup L ≤ center L
  · obtain ⟨hcomp, hm⟩ := ordinary_model_of_central_fitting hA hC hG L hL hf
    exact OrdinarySource.ordinary_conclusion hrem hcore L hcomp hm
  · exact (Section03.NoncentralFitting.conclusion_of_noncentral hG hcore hL hf).1
/-- The actual B.5.2 quotient consumer: a nilpotent radical forces the
original two-core quotient of the C-component to be quasisimple. -/
theorem quasisimple_twoCore_quotient_of_sources
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hrem : OrdinarySource.RemainingOddCoverInputs.{u})
    {H : Type u} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {C : Subgroup H} (hc : C.IsCComponent)
    [Group.IsNilpotent (solvableRadical C)] :
    IsQuasisimple (C ⧸ pCore 2 C) :=
  quasisimple_twoCore_quotient_of_a36
    (a36Input_of_theoremsAC_and_odd_covers hA hC hrem) hH hc

end CFSG.Quasithin.ChapterA.SQTKStructure
