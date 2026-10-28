module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.BlockModuleSource.Classification
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.BlockModuleSource.RowReduction

/-!
# Block types in the strict seed branch

Apply the complete corrected B.4 catalogue to the literal lifted block
module. All rows with the proper Sylow-overgroup Fitting bound force the
seed to equal the component and contradict strict containment. The remaining
marked odd alternating natural actions and four-dimensional A₇ row give
the actual χ or exceptional block type, retaining the original module.

Source: Aschbacher--Smith C.1.28, printed p.133.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BlockModuleSource
open ChapterB ComponentRecognition ComponentRecognition.SylowOvergroups SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G]
variable (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]

/-- In the strict B.1.13 branch, the lifted block has an actual odd
alternating natural module or is the exceptional A₇ block. -/
theorem block_type_of_proper_seed
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hv : IsPReduced 2 V)
    (L : Subgroup G) (hL : IsBlock L) (hU : (blockU L).map L.subtype ≤ V)
    (K : Subgroup (G ⧸ centralizer (V : Set G)))
    (T : Sylow 2 (G ⧸ centralizer (V : Set G)))
    (hB : IsComponent (G ⧸ centralizer (V : Set G))
      (L.map (QuotientGroup.mk' (centralizer (V : Set G)))))
    (hBK : ⁅L.map (QuotientGroup.mk' (centralizer (V : Set G))), K⁆ =
      L.map (QuotientGroup.mk' (centralizer (V : Set G))))
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hKsub : (K.subgroupOf (K ⊔ (T : Subgroup _))).IsSubnormal)
    (hcomm :
      let ρ := NormalElementaryQuotient.representation V
        (QuotientGroup.mk' (centralizer (V : Set G))) (QuotientGroup.mk'_surjective _)
        (QuotientGroup.ker_mk' _);
      K = ⁅K, generatedBy {A | IsBestOffender ρ A} (T : Subgroup _)⁆)
    (hKB : K ≤ L.map (QuotientGroup.mk' (centralizer (V : Set G))))
    (hne : K ≠ L.map (QuotientGroup.mk' (centralizer (V : Set G)))) :
    IsChiBlock L ∨ IsExceptionalA7Block L := by
  let q := QuotientGroup.mk' (centralizer (V : Set G))
  let ρ := NormalElementaryQuotient.representation V q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)
  let B := L.map q
  have hf := NormalElementaryQuotient.representation_injective V q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have hN := ChapterB.offenderSubgroup_le_normalizer_component ρ hf hB
  dsimp only at hcomm
  change K = ⁅K, generatedBy {A | IsBestOffender ρ A}
    (T : Subgroup (G ⧸ centralizer (V : Set G)))⁆ at hcomm
  have hOff : ∃ A : Subgroup (G ⧸ centralizer (V : Set G)),
      IsBestOffender ρ A ∧ A ≤ (T : Subgroup (G ⧸ centralizer (V : Set G))) ∧ ⁅B,A⁆ = B := by
    apply exists_bestOffender_commutator ρ K B (T : Subgroup (G ⧸ centralizer (V : Set G)))
    · exact hB
    · exact hBK
    · exact hcomm
    · exact hN
  obtain ⟨A,hoff,_,hBA⟩ := hOff
  obtain ⟨H,hBH,_,hI,hHI,hHN,_,him,he,hcase⟩ :=
    exists_classified_block_section V hA hC h4 hG hv L hL hU A hB hBA hoff
  let I := space V ((blockU L).map L.subtype)
  let σ := centralSectionRepresentation ρ B H I hHI hHN
  let M := actionSubgroup σ (B.subgroupOf H)
  let : IsQuasisimple M := him.quasisimple
  obtain ⟨a,ha⟩ := he
  rcases action_bound_or_alternating_module_of_marking (imageRepresentation σ)
      (centralQuotientRepresentation ρ B I hI.choose) M
      (offenderSubgroup (imageRepresentation σ)) a ha hcase with hb | hn | hd
  · exact False.elim (hne (eq_component_of_proper_sylow_fitting_bound K B T hB hBK hkind
      hKsub hKB hb))
  · obtain ⟨n,hn,⟨d⟩⟩ := hn
    have hm := linearBlockModel_of_irrPlus_chart V L hL hU
      (le_centralizer_iff.mp hv.le_centralizer_pCore) _ I hI d
    left
    right
    refine ⟨n,?_,?_,hL.short,hm⟩
    · rcases hn with rfl | rfl <;> decide
    · rcases hn with rfl | rfl <;> decide
  · obtain ⟨⟨e⟩,hd⟩ := hd
    exact Or.inr (exceptionalA7_of_irrPlus_dimension V L hL hU
      (le_centralizer_iff.mp hv.le_centralizer_pCore) e I hI hd)

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BlockModuleSource
