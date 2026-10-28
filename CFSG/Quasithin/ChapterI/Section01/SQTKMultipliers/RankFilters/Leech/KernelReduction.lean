module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.LeechSections.Co1
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.LeechSections.Co2
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.LeechSections.Suz
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.LeechClassicalSectionRanks
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.FischerCentralizerSections
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.ScalarQuotients
public import Theory.SpecificGroups.SymplecticSix.EvenProjective
import all CFSG.Quasithin.ChapterA.Section02.Sporadic.CentralizerQuotientOperations
import all CFSG.Quasithin.ChapterA.Section02.Sporadic.LeechSections.Co1
import all CFSG.Quasithin.ChapterA.Section02.Sporadic.LeechSections.Co2
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co2.CentralizerSection
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection

/-!
# Concrete action-kernel inputs for the Leech rank exclusions

Co₁'s classical quotient restricts its eight-dimensional image to the range of
an orthogonal embedding, then projectivizes. Restriction keeps the kernel a
two-group, and the binary scalar quotient is injective. Co₂'s projectivization
also adds no kernel. Suz's comparison is an actual isomorphism, so its kernel
is precisely that of the action on 27 pairs.

The conditional rank applications below therefore require only the two-group
property of each original action kernel. They use the proved rank-three
classical targets and coprime-kernel lifting, with no section-rank induction.
They do not prove those three kernel properties. Each concrete kernel producer
can import this module to supply its unconditional source application without
depending on the final four-case assembly.

The `import all` edges intentionally make this an internal proof extension of
the existing quotient constructors. Their bodies are used only in proofs;
their public boundaries and the old section constructors remain unchanged.

Source: Aschbacher--Smith A.2.19 and I.1.3, printed pp.40--41 and 407;
GLS3 Tables 5.3k, l and o. Normality is inside each displayed numerator.
-/

public section
namespace CFSG.Quasithin.ChapterI.SQTKMultipliers.RankFilters.Leech
open ChapterA

private theorem isPGroup_restrictTarget {G S : Type*} [Group G] [Group S]
    (d : InvolutionCentralizerQuotientData G S) (L : Subgroup S)
    (h : IsPGroup 2 d.quotientMap.ker) :
    IsPGroup 2 (d.restrictTarget L).quotientMap.ker := by
  let P := L.comap d.quotientMap
  let e := P.equivMapOfInjective d.numerator.subtype Subtype.val_injective
  let f : (d.restrictTarget L).quotientMap.ker →* d.quotientMap.ker :=
    { toFun := fun x => ⟨(e.symm x.val).val, congrArg Subtype.val x.property⟩
      map_one' := Subtype.ext (congrArg (fun y : P => y.val) e.symm.map_one)
      map_mul' := fun x y =>
        Subtype.ext (congrArg (fun y : P => y.val) (e.symm.map_mul x.val y.val)) }
  apply h.of_injective f
  intro x y hxy
  apply Subtype.ext
  apply e.symm.injective
  apply Subtype.ext
  exact congrArg (fun y : d.quotientMap.ker => y.val) hxy

/-- The original Co₁ action-kernel bound suffices for the literal classical quotient. -/
theorem co1_classical_kernel_isPGroup
    (h : IsPGroup 2 _root_.Sporadic.LeechRelated.Co1.CentralizerSection.quotientMap.ker) :
    IsPGroup 2 LeechSections.Co1.classicalQuotientData.quotientMap.ker := by
  let f := _root_.Sporadic.LeechRelated.Co1.CentralizerSection.omegaEmbedding
  let hf := _root_.Sporadic.LeechRelated.Co1.CentralizerSection.omegaEmbedding_injective
  let d := LeechSections.Co1.binaryQuotientData.restrictTarget f.range
  let e := MonoidHom.ofInjective hf
  let p := ClassicalOrthogonal.projectiveElementaryMap
    (ClassicalOrthogonal.formD 4 (ZMod 2))
  change IsPGroup 2 (p.comp (e.symm.toMonoidHom.comp d.quotientMap)).ker
  rw [MonoidHom.ker_comp_of_injective _ p
    (ClassicalOrthogonal.TheoremDRootNormalizer.elementaryProjective_injective _),
    MonoidHom.ker_comp_of_injective _ e.symm.toMonoidHom e.symm.injective]
  exact isPGroup_restrictTarget _ _ h

/-- Co₂'s literal projective quotient has the same kernel as its symplectic action. -/
theorem co2_quotient_kernel_eq :
    _root_.Sporadic.LeechRelated.Co2.CentralizerSection.quotientMap.ker =
    _root_.Sporadic.LeechRelated.Co2.CentralizerSection.symplecticMap.ker := by
  ext g
  change (QuotientGroup.mk' (Subgroup.center
    (Matrix.symplecticGroup (Fin 3) (ZMod 2))))
      (_root_.Sporadic.LeechRelated.Co2.CentralizerSection.symplecticMap g) = 1 ↔
      _root_.Sporadic.LeechRelated.Co2.CentralizerSection.symplecticMap g = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Theory.SpecificGroups.SymplecticSix.EvenProjective.center_eq_bot]
  rfl

/-- Suz's canonical orthogonal comparison preserves the pair-action kernel. -/
theorem suz_quotient_kernel_eq : SuzCentralizerSection.quotientData.quotientMap.ker =
    _root_.Sporadic.LeechRelated.Suz.CentralizerSection.blockAction.ker := by
  exact MonoidHom.ker_comp_of_injective _ _
    _root_.Sporadic.LeechRelated.Suz.CentralizerSection.blockEquivPOmegaMinus.injective

/-- Conditional Co₁ rank exclusion, requiring only the concrete action kernel. -/
theorem co1_not_quasithin_of_kernel
    (hk : IsPGroup 2 _root_.Sporadic.LeechRelated.Co1.CentralizerSection.quotientMap.ker) :
    ¬ IsQuasithin _root_.Sporadic.LeechRelated.Co1.Carrier :=
  LeechSections.Co1.classicalQuotientData.not_quasithin_of_rank
    (co1_classical_kernel_isPGroup hk) 3 (by decide) leechPOmega8PlusTwo_primeRank_three_gt_two

/-- Conditional Co₂ rank exclusion, requiring only the concrete symplectic action kernel. -/
theorem co2_not_quasithin_of_kernel
    (hk : IsPGroup 2 _root_.Sporadic.LeechRelated.Co2.CentralizerSection.symplecticMap.ker) :
    ¬ IsQuasithin _root_.Sporadic.LeechRelated.Co2.Carrier := by
  apply LeechSections.co2CentralizerQuotient.not_quasithin_of_rank
    (p := 3) _ (by decide) leechPSp6Two_primeRank_three_gt_two
  change IsPGroup 2 _root_.Sporadic.LeechRelated.Co2.CentralizerSection.quotientMap.ker
  rw [co2_quotient_kernel_eq]
  exact hk

/-- Conditional Suz rank exclusion for the exact simple orthogonal target. -/
theorem suz_not_quasithin_of_kernel
    (hk : IsPGroup 2 _root_.Sporadic.LeechRelated.Suz.CentralizerSection.blockAction.ker) :
    ¬ IsQuasithin _root_.Sporadic.LeechRelated.Suz.Carrier := by
  apply SuzCentralizerSection.quotientData.not_quasithin_of_rank
    (p := 3) _ (by decide) leechPOmega6MinusTwo_primeRank_three_gt_two
  rw [suz_quotient_kernel_eq]
  exact hk

variable {G : Type*} [Group G] [Finite G]

/-- The source Co₁ application still requires the concrete eight-space kernel proof. -/
theorem co1_not_stronglyQuasithin_of_equiv_of_kernel
    (hk : IsPGroup 2 _root_.Sporadic.LeechRelated.Co1.CentralizerSection.quotientMap.ker)
    (e : G ≃* _root_.Sporadic.LeechRelated.Co1.Carrier) : ¬ IsStronglyQuasithin G :=
  fun h => co1_not_quasithin_of_kernel hk (Theory.GroupTheory.isQuasithin_of_equiv e h.quasithin)

/-- The source Co₂ application still requires the concrete coloring-action kernel proof. -/
theorem co2_not_stronglyQuasithin_of_equiv_of_kernel
    (hk : IsPGroup 2 _root_.Sporadic.LeechRelated.Co2.CentralizerSection.symplecticMap.ker)
    (e : G ≃* _root_.Sporadic.LeechRelated.Co2.Carrier) : ¬ IsStronglyQuasithin G :=
  fun h => co2_not_quasithin_of_kernel hk (Theory.GroupTheory.isQuasithin_of_equiv e h.quasithin)

/-- The source Suz application still requires the concrete pair-action kernel proof. -/
theorem suz_not_stronglyQuasithin_of_equiv_of_kernel
    (hk : IsPGroup 2 _root_.Sporadic.LeechRelated.Suz.CentralizerSection.blockAction.ker)
    (e : G ≃* _root_.Sporadic.LeechRelated.Suz.Carrier) : ¬ IsStronglyQuasithin G :=
  fun h => suz_not_quasithin_of_kernel hk (Theory.GroupTheory.isQuasithin_of_equiv e h.quasithin)

end CFSG.Quasithin.ChapterI.SQTKMultipliers.RankFilters.Leech
