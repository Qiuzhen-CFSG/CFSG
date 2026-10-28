module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.BlockModuleSource.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ComponentSource.BlockConsumer

/-!
# B.4 on the actual lifted block module

The original SQTK cover supplies the component's source hypotheses.
B.1.11 and corrected B.4 give a classified section inside V. The proved
Irr⁺ uniqueness identifies this section with U(L), retaining the literal
actor image. Natural action charts and the exceptional four-dimensional
A₇ row now give the actual named block types.

Source: Aschbacher--Smith C.1.28, printed pp.133--134; the earlier universal
A/C and corrected B.4 implications are retained explicitly.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BlockModuleSource
open ChapterB ComponentRecognition.SQTKSectionImage SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G]
variable (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]

/-- B.4 classifies the literal U(L)/C_U(L), with its actual image actor. -/
theorem exists_classified_block_section
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hv : IsPReduced 2 V)
    (L : Subgroup G) (hL : IsBlock L) (hU : (blockU L).map L.subtype ≤ V)
    (A : Subgroup (G ⧸ centralizer (V : Set G)))
    (hcomp : IsComponent (G ⧸ centralizer (V : Set G))
      (L.map (QuotientGroup.mk' (centralizer (V : Set G)))))
    (hmove : ⁅L.map (QuotientGroup.mk' (centralizer (V : Set G))), A⁆ =
      L.map (QuotientGroup.mk' (centralizer (V : Set G))))
    (hoff : IsBestOffender (NormalElementaryQuotient.representation V
      (QuotientGroup.mk' (centralizer (V : Set G))) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _)) A) :
    let q := QuotientGroup.mk' (centralizer (V : Set G))
    let ρ := NormalElementaryQuotient.representation V q (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _)
    let B := L.map q
    let I := space V ((blockU L).map L.subtype)
    ∃ H : Subgroup (G ⧸ centralizer (V : Set G)),
      B ≤ H ∧ H ≤ B ⊔ A ∧
      ∃ (hI : IsIrrPlus ρ B I)
        (hHI : H ≤ subspaceStabilizer ρ I) (hHN : H ≤ normalizer (B : Set _)),
        let σ := centralSectionRepresentation ρ B H I hHI hHN
        let M := actionSubgroup σ (B.subgroupOf H)
        Function.Injective (centralQuotientRepresentation ρ B I hI.choose) ∧
        ImageHypotheses σ (B.subgroupOf H) ∧
        (∃ e : B ≃* M, ∀ b, imageRepresentation σ (e b) =
          centralQuotientRepresentation ρ B I hI.choose b) ∧
        ProjectiveLine.IrreducibleActionCase (imageRepresentation σ) M
          (offenderSubgroup (imageRepresentation σ)) := by
  let q := QuotientGroup.mk' (centralizer (V : Set G))
  let ρ := NormalElementaryQuotient.representation V q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)
  let B := L.map q
  let : IsQuasisimple B := hcomp.2
  have hcov : Nonempty (SQTKQuotient KnownSimple.IsKnownSimple (G ⧸ centralizer (V : Set G))) :=
    ⟨{ Cover := G, kernel := centralizer (V : Set G), sqtk := hG, equiv := MulEquiv.refl _ }⟩
  obtain ⟨hsqtk,hcenter⟩ := ComponentSource.component_source_of_sqtk_quotient hA
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC hA hC) hcov hv.quotient_pCore_eq_bot B hcomp
  obtain ⟨H,I,hBH,hHA,hI,hHI,hHN,hf,him,he,hcase⟩ :=
    exists_classified_section ρ (NormalElementaryQuotient.representation_injective V q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) B A hsqtk hcenter hmove hoff h4
  have hi := irrPlus_eq_blockSpace V q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) L hL hU hI
  subst I
  exact ⟨H,hBH,hHA,hI,hHI,hHN,hf,him,he,hcase⟩

/-- A natural action chart on the classified section marks the actual block. -/
theorem linearBlockModel_of_irrPlus_chart
    (L : Subgroup G) (hL : IsBlock L) (hU : (blockU L).map L.subtype ≤ V)
    (hQC : pCore 2 G ≤ centralizer (V : Set G))
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    (π : Representation (ZMod 2) A W)
    (I : Submodule (ZMod 2) (Additive V))
    (hI : IsIrrPlus (NormalElementaryQuotient.representation V
      (QuotientGroup.mk' (centralizer (V : Set G))) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _)) (L.map (QuotientGroup.mk' (centralizer (V : Set G)))) I)
    (e : QuasisimpleSource.ActionEquiv (centralQuotientRepresentation
      (NormalElementaryQuotient.representation V (QuotientGroup.mk' (centralizer (V : Set G)))
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _))
      (L.map (QuotientGroup.mk' (centralizer (V : Set G)))) I hI.choose) π) :
    IsLinearBlockModel L π := by
  have hi := irrPlus_eq_blockSpace V _ (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) L hL hU hI
  subst I
  exact linearBlockModel_of_coordinates V _ (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) L hU hI.choose
    (core_eq_centralizer_quotient_kernel V L hL.subnormal hL.short.fitting hU hQC)
    π e.groupEquiv e.linearEquiv e.intertwines

/-- The exceptional B.4 A₇ row retains the cardinal of the original block quotient. -/
theorem exceptionalA7_of_irrPlus_dimension
    (L : Subgroup G) (hL : IsBlock L) (hU : (blockU L).map L.subtype ≤ V)
    (hQC : pCore 2 G ≤ centralizer (V : Set G))
    (e : L.map (QuotientGroup.mk' (centralizer (V : Set G))) ≃* alternatingGroup (Fin 7))
    (I : Submodule (ZMod 2) (Additive V))
    (hI : IsIrrPlus (NormalElementaryQuotient.representation V
      (QuotientGroup.mk' (centralizer (V : Set G))) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _)) (L.map (QuotientGroup.mk' (centralizer (V : Set G)))) I)
    (hd : Module.finrank (ZMod 2) (centralQuotient
      (NormalElementaryQuotient.representation V (QuotientGroup.mk' (centralizer (V : Set G)))
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _))
      (L.map (QuotientGroup.mk' (centralizer (V : Set G)))) I) = 4) :
    IsExceptionalA7Block L := by
  have hi := irrPlus_eq_blockSpace V _ (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) L hL hU hI
  subst I
  refine ⟨hL.short,⟨(coreQuotientEquivCentralizerImage V L hL.subnormal
    hL.short.fitting hU hQC).trans e⟩,?_⟩
  rw [Nat.card_congr (moduleQuotientEquiv V _ (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) L hU).toEquiv]
  change Nat.card (centralQuotient _ _ _) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BlockModuleSource
