module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.MovedModule
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.SymmetricSeven
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.Source
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Mathieu.Recognition
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.RankOneExclusion
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ComponentOrbitExclusion
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.MarkedMultiplicity
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.HigherMultiplicity
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedNatural
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineModels
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSelection
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineCoefficient
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineProjective
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineTensor
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSix
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CatalogueTensor
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CatalogueComponents
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CatalogueExchanged

/-!
# Excluding the marked large-action catalogue

Apply the completed orthogonal, symmetric-seven, tensor and Mathieu source
arguments to the four rows of `RankCore.ActionAlternative`. The tensor
adapter retains the original central quotient and conjugation equation;
the Mathieu adapter derives the native marking from its component row.
Every branch therefore concerns the original flag and quotient action.

This is a conditional consumer, not catalogue exhaustion or source 14.4.14.
The marked catalogue remains to be derived from the original hypotheses.
The independent Chapter 10 mixed-size input is also explicit and must be
discharged by the final source assembly owner.

Source: Aschbacher--Smith, 14.4.2(3--6), 14.4.9--14,
printed pp.1006--1007,1009--1012.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative Matrix TensorProduct
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Tensor CoreGeometry
open LargerDimension.LocalAction.Components
universe u w
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The action-catalogue tensor coordinates retain the literal central
quotient and conjugation map consumed by the source tensor exclusion. -/
private noncomputable def tensorCoordinates
    (F : InvariantFlag T V 3) [IsMulCommutative V] [IsElementaryAbelian 2 F.Uhat]
    (hk : F.terminalHatAction.ker = pCore 2 F.H)
    {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    {D : Subgroup Five} (hAD : AltFive ≤ D)
    (σ : Representation (ZMod 2) D W) (hD : D = ⊤ ∨ D = AltFive)
    (hσ : IsSourceConstituent hAD σ)
    (e : coreQuotient F.H ≃* Three × D)
    (f : Additive F.Uhat ≃ₗ[ZMod 2] (BinaryPermutation.core (Fin 3) ⊗[ZMod 2] W))
    (hf : letI := F.U_normal
      ∀ a v, f ((sourceAction F hk).representation a v) = sourceTensorAction σ (e a) (f v)) :
    CaseFiveCoordinates hAD (V := W) F.H F.U := by
  let m : F.Uhat ≃* Multiplicative (BinaryPermutation.core (Fin 3) ⊗[ZMod 2] W) := {
    toFun v := Multiplicative.ofAdd (f (Additive.ofMul v))
    invFun w := (f.symm w.toAdd).toMul
    left_inv v := congrArg Additive.toMul (f.symm_apply_apply (Additive.ofMul v))
    right_inv w := congrArg Multiplicative.ofAdd (f.apply_symm_apply w.toAdd)
    map_mul' a b := congrArg Multiplicative.ofAdd (map_add f (Additive.ofMul a) (Additive.ofMul b)) }
  refine {
    actor_case := hD
    constituent := σ
    constituent_model := hσ
    actor := e
    space := m
    U_le_H := F.U_le_H
    H_normalizes_U := le_normalizer_conjugateSpanBy V F.H
    equivariant := ?_ }
  intro h a
  apply congrArg Multiplicative.ofAdd
  change f (Additive.ofMul (QuotientGroup.mk' (center F.U) (F.uAction h a))) = _
  rw [← F.uhatAction_apply_mk]
  exact hf (QuotientGroup.mk' (pCore 2 F.H) h)
    (Additive.ofMul (QuotientGroup.mk' (center F.U) a))

/-- Assemble all four completed large-row exclusions on the literal action.
This is conditional on the marked action catalogue; it does not establish
its exhaustiveness. The only other extra input is the authorized mixed size
source theorem. -/
theorem source_large_exclusion_of_marked_action_of_mixed_size (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hlarge : 64 < Nat.card F.U)
    (models : letI := chosen.elementary
      letI := F.U_normal
      RankCore.ActionAlternative.{w} (sourceAction F
        (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ))) : False := by
  let := chosen.elementary
  let := F.U_normal
  let hk := source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ
  cases models with
  | orthogonal κ e he =>
    exact Orthogonal.source_orthogonal_exclusion d earlier hq chosen structural alternatives
      F hne hZ κ e he
  | symmetricSeven e p he =>
    obtain ⟨g,hg,hgP,hgH⟩ := exists_source_conjugator d earlier hq chosen structural F
    apply source_symmetric_seven_contradiction d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hg hgP hgH e p
    intro a v
    exact (he (QuotientGroup.mk' (pCore 2 F.H) a) v).symm
  | tensor D hAD σ hD hσ e f hf =>
    exact source_tensor_exclusion_of_mixed_size d earlier hq chosen structural alternatives
      classification size F hne hZ (tensorCoordinates F hk hAD σ hD hσ e f hf)
  | tripleM22 hK hirr hd =>
    exact source_mathieu_exclusion d earlier hq chosen structural alternatives classification
      F hne hZ hlarge hK hirr hd


/-- The actual four tensor alternatives of G.11.2(9) contradict the original
large extraspecial geometry, with only the authorized mixed-size input. -/
theorem source_case_nine_exclusion_of_mixed_size (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hlarge : 64 < Nat.card F.U)
    (hm : ChapterG.Section11.CaseNine F.terminalRepresentation) : False := by
  exact source_large_exclusion_of_marked_action_of_mixed_size d earlier hq chosen
    structural alternatives classification size F hne hZ hlarge
    (source_case_nine_catalogue d earlier hq chosen structural alternatives F hne hZ hm)


/-- The original deleted constituent embedding now supplies the full marked
catalogue row consumed by the tensor exclusion. No surjectivity or catalogue
premise is retained. -/
theorem source_deleted_tensor_embedding_exclusion_of_mixed_size (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hlarge : 64 < Nat.card F.U)
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (H : Subgroup F.TerminalHdot)
    (hm : FixedLineActions.PermutationTensorEmbedding F.terminalRepresentation H
      (BinaryPermutation.coreRepresentation (Fin 5))) : False := by
  exact source_large_exclusion_of_marked_action_of_mixed_size d earlier hq chosen
    structural alternatives classification size F hne hZ hlarge
    (source_deleted_tensor_catalogue d earlier hq chosen structural alternatives
      F hne hZ g hyp H hm)


section FixedLineReduction
local instance : Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.Field 1) := ZMod.algebra _ 2

/-- The remaining original fixed-line constituent actions, after the two
permutation tensor rows have been discharged. -/
@[expose] def FixedLineRemainder {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (B : LinearMap.BilinForm (ZMod 2) W)
    (v : W) (E : Submodule (ZMod 2) W) (X : Subgroup D) : Prop :=
  ∃ C : Subgroup D, IsComponent D C ∧ ⁅C,X⁆ ≠ ⊥ ∧
    ChapterG.Section10.ComponentOrthogonalData ρ B C ∧
    ∃ I : Submodule (ZMod 2) W, Representation.BinaryOffender.Homogeneous.IsIrrPlusWith ρ (componentOrbit C ⊤) X I ∧
      ((v ∈ I ∧ C.Normal ∧ finrank (ZMod 2) I = 4 ∧ finrank (ZMod 2) W = 8 ∧
        Nat.card X = 8 ∧
        ChapterG.Section09.Quasiequivalent (ρ.comp (componentOrbit C ⊤).subtype)
          ((SL2.BinarySmall.natural (K := OrthogonalFourMinus.FiniteModel.Field 1)).prod
            (SL2.BinarySmall.natural (K := OrthogonalFourMinus.FiniteModel.Field 1)))) ∨
      (v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry ρ B v E X I))

/-- The source selection with both permutation tensor branches removed.
The surviving natural double and exchanged constituent are literal actions
on the original flag; neither is asserted to identify the whole group. -/
theorem source_large_catalogue_or_fixed_line_remainder_of_mixed_size (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      (ChapterG.Section11.Conclusion F.terminalRepresentation B (F.terminalDot (F.X g)) ∨
        (¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
          FixedLineModuleData F.terminalRepresentation B v (F.terminalDot (F.X g)) ∧
          FixedLineRemainder F.terminalRepresentation B v
            (hatSpace F (F.E g)) (F.terminalDot (F.X g)))) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hS,hcases⟩ := source_large_catalogue_or_fixed_line_actions
    d earlier hq chosen structural alternatives classification F hne hZ hlarge g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hS,?_⟩
  rcases hcases with hc | ⟨hn,hmodule,C,hC,hm,horth,I,hI,hmarked | hex⟩
  · exact Or.inl hc
  · obtain ⟨hv,hCn,hI4,hV8,hX8,_,_,hamb⟩ := hmarked
    rcases hamb with hnat | hfive | hsix
    · exact Or.inr ⟨hn,hmodule,C,hC,hm,horth,I,hI,Or.inl ⟨hv,hCn,hI4,hV8,hX8,hnat⟩⟩
    · exact (source_deleted_tensor_embedding_exclusion_of_mixed_size d earlier hq chosen
        structural alternatives classification size F hne hZ hlarge g hyp _ hfive).elim
    · exact (source_six_tensor_embedding_exclusion d earlier hq chosen structural alternatives
        F hne hZ hlarge g hyp _ hsix).elim
  · exact Or.inr ⟨hn,hmodule,C,hC,hm,horth,I,hI,Or.inr hex⟩

/-- Under the original large-case hypotheses the low-rank clause is impossible.
The fixed-line clause retains precisely the natural SL₂(4) double and the
unmarked exchanged-constituent geometry. This constructs the remainder from
the original flag; it assumes no action-catalogue or recognition premise. -/
theorem source_large_fixed_line_remainder_of_mixed_size (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      FixedLineModuleData F.terminalRepresentation B v (F.terminalDot (F.X g)) ∧
      FixedLineRemainder F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g)) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hfix⟩ := source_terminal_marked_hypothesis F d earlier hq
    chosen structural alternatives hne g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,?_,?_⟩
  · exact ⟨_,hfix,source_terminal_actor_normal_in_sylow d earlier hq chosen structural
      alternatives F hne g hgP hgH⟩
  by_cases hw : ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))
  · have hc := source_large_lowRank_conclusion d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH B v hyp hline hfix hw
    have hd := source_large_terminal_dimension_ge_six d earlier hq chosen structural alternatives
      F hne hZ hlarge
    rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
    · have := h1.1; omega
    · have := h2.1; omega
    · exact (source_case_three_exclusion d earlier hq chosen structural alternatives
        F hne hZ hlarge h3).elim
    · exact (source_case_four_exclusion d earlier hq chosen structural alternatives F hne hZ h4).elim
    · exact (source_case_five_exclusion d earlier hq chosen structural alternatives F hne hZ B h5).elim
    · exact (source_case_six_exclusion d earlier hq chosen structural alternatives F hne hZ h6).elim
    · exact (source_large_exclusion_of_marked_action_of_mixed_size d earlier hq chosen
        structural alternatives classification size F hne hZ hlarge
        (source_case_seven_catalogue d earlier hq chosen structural alternatives F hne hZ _ h7)).elim
    · exact (CatalogueExchanged.case_eight_not_lowRank v hyp.point_ne_zero h8 hw).elim
    · exact (source_case_nine_exclusion_of_mixed_size d earlier hq chosen structural alternatives
        classification size F hne hZ hlarge h9).elim
    · exact (source_case_ten_exclusion d earlier hq chosen structural alternatives F hne hZ _ h10).elim
    · exact (source_case_eleven_not_lowRank F v hyp.point_ne_zero _ h11 hw).elim
    · exact (CatalogueExchanged.case_twelve_not_lowRank v hyp.point_ne_zero h12 hw).elim
    · exact (source_large_exclusion_of_marked_action_of_mixed_size d earlier hq chosen
        structural alternatives classification size F hne hZ hlarge
        (source_case_thirteen_catalogue d earlier hq chosen structural alternatives F hne hZ hlarge h13)).elim
  · have hmodule := source_fixed_line_module d earlier hq chosen structural alternatives
      F hne hZ hlarge g hgP hgH B v hyp hline hw
    obtain ⟨C,hC,hm,horth,I,hI,hmarked | hex⟩ := source_large_fixed_line_constituent_reduction
      d earlier hq chosen structural alternatives classification F hne hZ hlarge g hgP hgH hyp hline hw
    · obtain ⟨hv,hCn,hI4,hV8,hX8,_,_,hamb⟩ := hmarked
      rcases hamb with hnat | hfive | hsix
      · exact ⟨hw,hmodule,C,hC,hm,horth,I,hI,Or.inl ⟨hv,hCn,hI4,hV8,hX8,hnat⟩⟩
      · exact (source_deleted_tensor_embedding_exclusion_of_mixed_size d earlier hq chosen
          structural alternatives classification size F hne hZ hlarge g hyp _ hfive).elim
      · exact (source_six_tensor_embedding_exclusion d earlier hq chosen structural alternatives
          F hne hZ hlarge g hyp _ hsix).elim
    · exact ⟨hw,hmodule,C,hC,hm,horth,I,hI,Or.inr hex⟩

/-- The two remaining source branches, now with the entire doubled-natural
ambient group represented in compatible component and coefficient coordinates. -/
@[expose] def SemilinearRemainder {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (B : LinearMap.BilinForm (ZMod 2) W)
    (v : W) (E : Submodule (ZMod 2) W) (X : Subgroup D) : Prop :=
  ∃ C : Subgroup D, IsComponent D C ∧ ⁅C,X⁆ ≠ ⊥ ∧
    ChapterG.Section10.ComponentOrthogonalData ρ B C ∧
    ∃ I : Submodule (ZMod 2) W,
      Representation.BinaryOffender.Homogeneous.IsIrrPlusWith ρ (componentOrbit C ⊤) X I ∧
      ((v ∈ I ∧ C.Normal ∧ finrank (ZMod 2) I = 4 ∧ finrank (ZMod 2) W = 8 ∧
        Nat.card X = 8 ∧
        Nat.card ((centralizer (componentOrbit C ⊤ : Set D)).subgroupOf X) = 2 ∧
        Nonempty (FixedLineSemilinear.Coordinates ρ (componentOrbit C ⊤))) ∨
      (v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry ρ B v E X I))

/-- On the original flag, construct the full semilinear ambient action in the
marked branch and prove that its actor centralizer has order two. The unmarked
exchanged constituent retains its literal geometry.
The independent mixed-size and earlier-source premises are unchanged; this does
not yet classify the coefficient image or assert the final large-case exclusion. -/
theorem source_large_semilinear_remainder_of_mixed_size (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      FixedLineModuleData F.terminalRepresentation B v (F.terminalDot (F.X g)) ∧
      SemilinearRemainder F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g)) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,hrem⟩ :=
    source_large_fixed_line_remainder_of_mixed_size d earlier hq chosen structural alternatives
      classification size F hne hZ hlarge g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,?_⟩
  obtain ⟨C,hC,hm,horth,I,hI,ha | hx⟩ := hrem
  · obtain ⟨hv,hCn,hI4,hV8,hX8,hdouble⟩ := ha
    let : (componentOrbit C ⊤).Normal := componentOrbit_top_normal C
    obtain ⟨a⟩ := FixedLineSemilinear.coordinates_of_double
      F.terminalRepresentation hyp.faithful _ hdouble
    have hk := a.actor_centralizer_ne_bot (F.terminalDot (F.X g)) (by omega)
    have hY := (source_large_marked_double_kernel d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH hyp hC hm hI.isIrrPlus hv hline hn
      (by omega) hk).1
    exact ⟨C,hC,hm,horth,I,hI,Or.inl ⟨hv,hCn,hI4,hV8,hX8,hY,⟨a⟩⟩⟩
  · exact ⟨C,hC,hm,horth,I,hI,Or.inr hx⟩

/-- The remaining source branches with the whole doubled-natural action split
over its literal coefficient image. The marked branch retains the full field
image of the original actor, the exact component-centralizer index and
generation, and the trivial two-core of the linear coefficient kernel.
The coefficient subgroup itself has not yet been classified. -/
@[expose] def CoefficientRemainder {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (B : LinearMap.BilinForm (ZMod 2) W)
    (v : W) (E : Submodule (ZMod 2) W) (X : Subgroup D) : Prop :=
  ∃ C : Subgroup D, IsComponent D C ∧ ⁅C,X⁆ ≠ ⊥ ∧
    ChapterG.Section10.ComponentOrthogonalData ρ B C ∧
    ∃ I : Submodule (ZMod 2) W,
      Representation.BinaryOffender.Homogeneous.IsIrrPlusWith ρ (componentOrbit C ⊤) X I ∧
      ((v ∈ I ∧ C.Normal ∧ finrank (ZMod 2) I = 4 ∧ finrank (ZMod 2) W = 8 ∧
        Nat.card X = 8 ∧
        Nat.card ((centralizer (componentOrbit C ⊤ : Set D)).subgroupOf X) = 2 ∧
        ∃ a : FixedLineSemilinear.Coordinates ρ (componentOrbit C ⊤),
          Function.Surjective (a.ambientField.comp X.subtype) ∧
          pCore 2 a.coefficientField.ker = ⊥ ∧
          (componentOrbit C ⊤ ⊔ centralizer (componentOrbit C ⊤ : Set D)).index = 2 ∧
          componentOrbit C ⊤ ⊔ centralizer (componentOrbit C ⊤ : Set D) ⊔ X = ⊤) ∨
      (v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry ρ B v E X I))

/-- Split the actual whole doubled SL₂(4) action over its coefficient image
and derive its field and centralizer restrictions from the original flag.
`a.splitEquiv` and `a.splitEquiv_action` identify the entire group and action,
and `a.centralizerCoefficientEquiv` identifies the literal linear kernel.
This adds no recognition premise. Classifying that kernel and the unmarked
exchanged constituents, and supplying the guarded earlier-source application,
remain obligations of the large-case assembly. -/
theorem source_large_coefficient_remainder_of_mixed_size (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      FixedLineModuleData F.terminalRepresentation B v (F.terminalDot (F.X g)) ∧
      CoefficientRemainder F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g)) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,hrem⟩ :=
    source_large_semilinear_remainder_of_mixed_size d earlier hq chosen structural alternatives
      classification size F hne hZ hlarge g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,?_⟩
  obtain ⟨C,hC,hm,horth,I,hI,ha | hx⟩ := hrem
  · obtain ⟨hv,hCn,hI4,hV8,hX8,hY,⟨a⟩⟩ := ha
    have hf := (source_terminal_ranks_of_no_lowRank d earlier hq chosen structural alternatives
      F hne hZ g hgP hgH v hline hn).1
    rw [←hline] at hf
    exact ⟨C,hC,hm,horth,I,hI,Or.inl ⟨hv,hCn,hI4,hV8,hX8,hY,a,
      a.actor_field_surjective _ v hyp.point_ne_zero hf,
      a.coefficient_kernel_twoCore hyp.twoCore_eq_bot,
      a.component_centralizer_index _ v hyp.point_ne_zero hf,
      a.generated_by_component_centralizer_actor _ v hyp.point_ne_zero hf⟩⟩
  · exact ⟨C,hC,hm,horth,I,hI,Or.inr hx⟩

/-- The original coefficient image as a faithful five-point subgroup. Its even
part is the actual component centralizer with trivial two-core. The original
actor has order-four image, excluding all five-cycle normalizers. -/
@[expose] def ProjectiveRemainder {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (B : LinearMap.BilinForm (ZMod 2) W)
    (v : W) (E : Submodule (ZMod 2) W) (X : Subgroup D) : Prop :=
  ∃ C : Subgroup D, IsComponent D C ∧ ⁅C,X⁆ ≠ ⊥ ∧
    ChapterG.Section10.ComponentOrthogonalData ρ B C ∧
    ∃ I : Submodule (ZMod 2) W,
      Representation.BinaryOffender.Homogeneous.IsIrrPlusWith ρ (componentOrbit C ⊤) X I ∧
      ((v ∈ I ∧ C.Normal ∧ finrank (ZMod 2) I = 4 ∧ finrank (ZMod 2) W = 8 ∧
        Nat.card X = 8 ∧
        Nat.card ((centralizer (componentOrbit C ⊤ : Set D)).subgroupOf X) = 2 ∧
        ∃ a : FixedLineSemilinear.Coordinates ρ (componentOrbit C ⊤),
          Function.Surjective (a.ambientField.comp X.subtype) ∧
          pCore 2 a.coefficientField.ker = ⊥ ∧
          (componentOrbit C ⊤ ⊔ centralizer (componentOrbit C ⊤ : Set D)).index = 2 ∧
          componentOrbit C ⊤ ⊔ centralizer (componentOrbit C ⊤ : Set D) ⊔ X = ⊤ ∧
          Function.Injective a.coefficientFive ∧
          pCore 2 (a.coefficientFive.range ⊓ alternatingGroup (Fin 5) : Subgroup (Equiv.Perm (Fin 5))) = ⊥ ∧
          Nat.card (X.map a.ambientFive) = 4 ∧
          ∀ P : Sylow 5 (Equiv.Perm (Fin 5)),
            ¬ a.coefficientFive.range ≤ normalizer ((P : Subgroup (Equiv.Perm (Fin 5))) : Set _)) ∨
      (v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry ρ B v E X I))

/-- Apply projective coefficient recognition to the same original flag and
whole doubled action. The coefficient quotient, field kernel and actor map are
literal; no new source premise is introduced. The remaining coefficient-image
classification, unmarked exchanged branch and guarded earlier-source assembly
are not asserted by this reduction. -/
theorem source_large_projective_remainder_of_mixed_size (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      FixedLineModuleData F.terminalRepresentation B v (F.terminalDot (F.X g)) ∧
      ProjectiveRemainder F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g)) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,hrem⟩ :=
    source_large_coefficient_remainder_of_mixed_size d earlier hq chosen structural alternatives
      classification size F hne hZ hlarge g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,?_⟩
  obtain ⟨C,hC,hm,horth,I,hI,ha | hx⟩ := hrem
  · obtain ⟨hv,hCn,hI4,hV8,hX8,hY,a,hfield,hcore,hindex,hgen⟩ := ha
    have hf := (source_terminal_ranks_of_no_lowRank d earlier hq chosen structural alternatives
      F hne hZ g hgP hgH v hline hn).1
    rw [←hline] at hf
    exact ⟨C,hC,hm,horth,I,hI,Or.inl ⟨hv,hCn,hI4,hV8,hX8,hY,a,
      hfield,hcore,hindex,hgen,
      a.coefficientFive_injective B hyp.nondegenerate hyp.preserves,
      a.coefficientFive_even_twoCore B hyp.nondegenerate hyp.preserves hyp.twoCore_eq_bot,
      a.actor_five_card B hyp.nondegenerate hyp.preserves _ v hyp.point_ne_zero hf hY,
      a.coefficientFive_not_le_fiveNormalizer B hyp.nondegenerate hyp.preserves
        _ v hyp.point_ne_zero hf hY⟩⟩
  · exact ⟨C,hC,hm,horth,I,hI,Or.inr hx⟩

end FixedLineReduction

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
