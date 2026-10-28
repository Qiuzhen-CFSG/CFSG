module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.Classical

/-!
# Normality for the binary unitary central quotient

A nonnormal C-component maps to an ordinary component modulo the ambient
two-core. The complete A.3.8 source kills its center and bounds every odd
prime rank by one. The actual PSU₃(2^s) norm-one torus contradicts that bound
for s≥2. Both quotients are transported through the canonical component map;
no unitary family tag or assumed normality is used.

Source: Aschbacher--Smith, A.3.8(3), pp.45--46; applied to the contained
branch of 4.2.5 on p.609. This argument does not apply to Suzuki groups.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G]

/-- The induced equivalence of central quotients. -/
def centerQuotientCongr {P Q : Type*} [Group P] [Group Q]
    (e : P ≃* Q) : (P ⧸ center P) ≃* (Q ⧸ center Q) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact (centerCongr e ⟨z,hz⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

/-- A component with an actual binary unitary central core quotient is normal. -/
theorem normal_of_unitary_central_core_quotient
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    {B : Subgroup G} (hB : B.IsCComponent) {s : ℕ} (hs : 2 ≤ s)
    (hu : ClassicalGroup.IsPSU ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) 3 (2 ^ s)) :
    B.Normal := by
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
  have hD : IsComponent Q D := Chapter1.Section02.nonnormal_twoCore_image_isComponent hQ hB hn
  have hnD : ¬ D.Normal := fun hh => hn (cComponent_normal_of_quotient_normal hB _ hh)
  let : IsQuasisimple D := hD.2
  have hf : fittingSubgroup D ≤ center D :=
    (le_solvableRadical _ inferInstance inferInstance).trans
      IsQuasisimple.solvableRadical_le_center
  have hm := (ChapterA.SQTKStructure.ordinary_model_of_central_fitting
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    hQ D hD.isCComponent hf).2
  have hz := ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.center_eq_bot_of_model
    (hQ.stronglyQuasithin 3 (by decide) (by decide))
    (pCore_quotient_pCore_eq_bot 2) D hD hnD hm
  have hr := ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.odd_ranks_of_model
    hQ.stronglyQuasithin (pCore_quotient_pCore_eq_bot 2) D hD hnD hm
  let c : (B ⧸ pCore 2 B) ≃* D := cComponentTwoCoreQuotientEquiv hB
  let z : D ≃* D ⧸ center D := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hz.symm)
  exact ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.unitary_three_binary_false
    hr s hs (hu.of_mulEquiv (z.trans (centerQuotientCongr c.symm)))
end CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
