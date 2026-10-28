module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels
public import Theory.GroupTheory.SolvableRadical.NormalTwoExtension
public import Theory.SpecificGroups.Alternating.TwoThreeCycles

/-!
# Normality of an SQTK component with A₆ radical quotient

Suppose the component is nonnormal. Its image modulo the ambient two-core
is an ordinary component. The proved A.3.8 source makes that image simple
with odd ranks at most one. Simplicity then identifies the original
component's radical with its two-core, contradicting the three-rank two
of its given A₆ radical quotient. This argument does not assume the
radical/two-core equality in the normal branch.

Source: Aschbacher--Smith A.3.8(3) and 1.2.1(3), pp.45--46,504.
The actual terminal consumer is SmallRows.AlternatingSixActionSource.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
open ChapterA.SQTKStructure
variable {G : Type*} [Group G] [Finite G]

/-- An A₆ radical quotient forces relative component normality. -/
theorem normal_of_alternatingSix_radical_quotient
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    {B : Subgroup G} (hB : B.IsCComponent)
    (e : (B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 6)) : B.Normal := by
  by_contra hn
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  let Q := G ⧸ pCore 2 G
  have hQ : IsSQTK KnownSimple.IsKnownSimple Q := by
    refine ⟨?_, hG.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 G) pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  let D := B.map (QuotientGroup.mk' (pCore 2 G))
  have hD : IsComponent Q D := nonnormal_twoCore_image_isComponent hQ hB hn
  have hnD : ¬ D.Normal := fun hh => hn (cComponent_normal_of_quotient_normal hB _ hh)
  let : IsQuasisimple D := hD.2
  have hf : fittingSubgroup D ≤ center D :=
    (le_solvableRadical _ inferInstance inferInstance).trans
      IsQuasisimple.solvableRadical_le_center
  have hm := (ordinary_model_of_central_fitting
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    hQ D hD.isCComponent hf).2
  have hsimple := NonnormalOuterSource.FourModels.simple_of_model
    (hQ.stronglyQuasithin 3 (by decide) (by decide))
    (pCore_quotient_pCore_eq_bot 2) D hD hnD hm
  let := hsimple
  let c : (B ⧸ pCore 2 B) ≃* D := cComponentTwoCoreQuotientEquiv hB
  let : IsSimpleGroup (B ⧸ pCore 2 B) := c.isSimpleGroup
  let : Group.IsPerfect B := hB.perfect
  have hR : solvableRadical B = pCore 2 B := radical_eq_core_of_perfect_simple_core_quotient
  let d : D ≃* alternatingGroup (Fin 6) :=
    c.symm.trans ((QuotientGroup.quotientMulEquivOfEq hR.symm).trans e)
  have hr := NonnormalOuterSource.FourModels.odd_ranks_of_model hQ.stronglyQuasithin
    (pCore_quotient_pCore_eq_bot 2) D hD hnD hm 3 (by decide) (by decide)
  rw [primeRank_congr 3 d] at hr
  have hh := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 6) (by decide)
  omega

end CFSG.Quasithin.Chapter1.Section02
