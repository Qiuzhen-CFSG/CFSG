module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.At.Tensor
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedNatural
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineActions
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineTensor
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSix
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CatalogueTensor
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CatalogueComponents
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CatalogueExclusion
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineRecognition
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineOrthogonal
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineNaturalSource

/-!
# Exhausting the marked large-action rows at G,T

Combine the completed component, orthogonal, Mathieu and tensor exclusions
on the same terminal action. The fixed-line coefficient calculation and
natural tensor coordinates remove the transposition-centralizer case.
The remaining branch is the original exchanged constituent, retaining
both fixed-point clauses, multiplicity and the marked point stabilizer.

The earlier inputs are restricted to the original group and Sylow subgroup.
The universal APIs remain unchanged. The `import all` edges intentionally
reuse the private calculations of the corresponding source implementation;
only deductions depending on the earlier inputs are specialized here.
Source: Aschbacher--Smith, G.11.6--8, 14.4.2,9--12; printed pp.365--369,1006--1012; refs/quasithin.pdf.
-/

public noncomputable section

/- Specialization of CaseOneLarge/ExchangedNatural.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.LocalAction.Components

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_large_lowRank_five_constituent_reduction_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hfix : ∀ t ∈ F.terminalDot (T : Subgroup G), F.terminalRepresentation t v = v)
    (hw : ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    ChapterG.Section11.Conclusion F.terminalRepresentation B (F.terminalDot (F.X g)) ∨
      (IsIrreducible F.terminalRepresentation ∧
        ∃ C : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot C ∧
          ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
          ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B C ∧
          ∃ I : Submodule (ZMod 2) (Additive F.Uhat),
            ∃ hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation
              (componentOrbit C ⊤) (F.terminalDot (F.X g)) I,
              v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry
                F.terminalRepresentation B v (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I ∧
              (∃ x : F.terminalDot (F.X g), I.map (F.terminalRepresentation x) ≠ I ∧
                IsCompl I (I.map (F.terminalRepresentation x))) ∧
              finrank (ZMod 2) (Additive F.Uhat) = 2 * finrank (ZMod 2) I ∧
              finrank (ZMod 2) (Additive F.Uhat) = 8 ∧
              (B.restrict I).Nondegenerate ∧
              ChapterG.Section06.HasModelOn
                (kerRepresentation (ChapterG.Section09.constituentAction F.terminalRepresentation
                  (componentOrbit C ⊤) (F.terminalDot (F.X g) ⊓
                    subspaceStabilizer F.terminalRepresentation I) I hI.invariant inf_le_right)) ⊤ ⊤
                (BinaryPermutation.naturalRepresentation (Fin 5))) := by
  rcases source_large_lowRank_exchanged_reduction_at d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH B v hyp hfix hw with hc |
      ⟨hi,C,hC,hm,horth,I,hI,hv,hgeo,hcompl,hdim,_,hnd,n,hn5,hn8,hn7,hmodel⟩
  · exact Or.inl hc
  have hS : ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) :=
    ⟨_,hfix,source_terminal_actor_normal_in_sylow_at d earlier hq chosen structural alternatives
      F hne g hgP hgH⟩
  have hn := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hcover := source_terminal_cover F d chosen
  have hr := ChapterG.Section11.ExchangedRecognition.exchanged_natural_ranks
    hyp hcover hw hS hn hC hm hI hgeo n hn5 hn8 hmodel
  have hn' : n = 5 := by
    rcases hr with hh | hh | hh
    · exact hh.1
    · have he : n = 6 := hh.1
      subst n
      have hb : 3 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
        rcases hh.2.2.2 with h | h <;> omega
      exact (ExchangedNatural.no_exchanged_six hyp hcover hw hS hn
        hC hm hI hv hgeo hb hmodel).elim
    · have he : n = 8 := hh.1
      subst n
      exact (ExchangedNatural.no_exchanged_eight_of_actor_five hyp hcover hw hS hn
        hC hm hI hv hgeo hh.2.2.2.1 hmodel).elim
  subst n
  have hd : finrank (ZMod 2) (Additive F.Uhat) = 8 := by
    rcases hr with hh | hh | hh <;> omega
  exact Or.inr ⟨hi,C,hC,hm,horth,I,hI,hv,hgeo,hcompl,hdim,hd,hnd,hmodel⟩

theorem source_large_lowRank_conclusion_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hfix : ∀ t ∈ F.terminalDot (T : Subgroup G), F.terminalRepresentation t v = v)
    (hw : ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    ChapterG.Section11.Conclusion F.terminalRepresentation B (F.terminalDot (F.X g)) := by
  rcases source_large_lowRank_five_constituent_reduction_at d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH B v hyp hfix hw with hc |
      ⟨hi,C,hC,hm,horth,I,hI,hv,hgeo,hcompl,hdim,hd,hnd,hmodel⟩
  · exact hc
  have hS : ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) :=
    ⟨_,hfix,source_terminal_actor_normal_in_sylow_at d earlier hq chosen structural alternatives
      F hne g hgP hgH⟩
  have hn := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  let P := ChapterG.Section10.pointCentralizer F.terminalRepresentation v
  let D := F.terminalDot (centralizer (F.ZU : Set G))
  have hHc : F.H ≤ centralizer (F.ZU : Set G) := by
    rw [hZ]
    exact normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
  have hD : D = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact mem_map_of_mem _ (hHc b.property)
  have hu := CaseOneHS.source_center_centralizing_point_image_three_rank_le_one_at
    d earlier hq chosen structural alternatives F hne v hline.symm g hgP hgH
  change primeRank 3 (P.subgroupOf D) ≤ 1 at hu
  have hpD : P ≤ D := by rw [hD]; exact le_top
  rw [primeRank_equiv 3 (subgroupOfEquivOfLe hpD)] at hu
  exact (ExchangedNatural.no_exchanged_five_of_point_rank hyp (source_terminal_cover F d chosen)
    hw hS hn hC hm hI hgeo hmodel hu).elim

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/FixedLineActions.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative MatrixGroups MonoidAlgebra TensorProduct

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge


open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter14.Section03.NonabelianSource.Recognition

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.LocalAction.Components

open Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable

universe u

section Marked

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
  (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
  (structural : Structural1222At KnownSimple.IsKnownSimple T)
  (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
  (classification : EarlierFaithfulClassification G (T : Subgroup G))
  (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
  (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
  (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
  [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
    (hatSpace F (F.E g)) (F.terminalDot (F.X g))
    ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
  {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
  (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
  {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (hI : IsIrrPlus F.terminalRepresentation (componentOrbit C ⊤) I) (hv : v ∈ I)

include d earlier hq chosen structural alternatives classification hne hZ hlarge hgP hgH hyp hC hm hI hv

theorem source_large_fixed_line_marked_actions_at
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    let R := invariantSubspace F.terminalRepresentation (componentOrbit C ⊤) I hI.choose
    C.Normal ∧ finrank (ZMod 2) I = 4 ∧
      finrank (ZMod 2) (Additive F.Uhat) = 8 ∧ Nat.card (F.terminalDot (F.X g)) = 8 ∧
      FixedLineActions.Models R.toRepresentation := by
  let := chosen.elementary
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let R := invariantSubspace F.terminalRepresentation H I hI.choose
  have hns := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hi := hyp.irreducible_of_not_solvable hns
  let : IsIrreducible R.toRepresentation := hI.irreducible_of_normal_restriction _ hi H
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨hXP,hN⟩ := source_terminal_actor_normal_in_sylow_at d earlier hq chosen
    structural alternatives F hne g hgP hgH
  have hind := terminal_component_normalizer_index_le_two d.qtke F (by decide) C hC
  have hdata := hyp.constituent_homogeneous_faithful_selfDual_of_point_mem hns hC hm P
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hind hI hv
  have hHC := (source_large_fixed_line_component_normal_at d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn).1
  obtain ⟨hCn,hmodels⟩ := source_large_fixed_line_component_models_at d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn
  obtain ⟨hI4,hV8,hX8⟩ := source_large_fixed_line_marked_degree_at d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn
  refine ⟨hCn,hI4,hV8,hX8,?_⟩
  let eH : H ≃* C := MulEquiv.subgroupCongr hHC
  rcases hmodels with ⟨e5⟩ | ⟨e6⟩ | ⟨e7⟩
  · exact FixedLineActions.five_models R.toRepresentation hdata.2.1 (eH.trans e5.some)
  · exact FixedLineActions.six_models R.toRepresentation hI4 (eH.trans e6.some)
  · exact (FixedLineActions.Seven.no_selfDual R.toRepresentation hdata.2.1
      (eH.trans e7.some) hI4 hdata.2.2.1).elim

theorem source_large_fixed_line_double_actions_at
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    FixedLineActions.DoubledModels
      (F.terminalRepresentation.comp (componentOrbit C ⊤).subtype) := by
  let R := invariantSubspace F.terminalRepresentation (componentOrbit C ⊤) I hI.choose
  have hmR := (source_large_fixed_line_marked_actions_at d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn).2.2.2.2
  obtain ⟨a⟩ := (source_large_marked_double_at d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv).2
  exact FixedLineActions.doubled_models _ R.toRepresentation a hmR

theorem source_large_fixed_line_ambient_actions_at
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    FixedLineActions.AmbientModels F.terminalRepresentation (componentOrbit C ⊤) := by
  let : (componentOrbit C ⊤).Normal := componentOrbit_top_normal C
  exact FixedLineActions.ambient_models _ hyp.faithful _
    (source_large_fixed_line_double_actions_at d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn)

end Marked

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
  (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
  (structural : Structural1222At KnownSimple.IsKnownSimple T)
  (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
  (classification : EarlierFaithfulClassification G (T : Subgroup G))
  (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
  (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
  (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
  [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
    (hatSpace F (F.E g)) (F.terminalDot (F.X g))
    ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))

include d earlier hq chosen structural alternatives classification hne hZ hlarge hgP hgH hyp

theorem source_large_fixed_line_constituent_reduction_at
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    FixedLineActions.ConstituentReduction F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g)) := by
  let := chosen.elementary
  have hns := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hF := hyp.fitting_centralizer_ne_bot_of_not_solvable (source_terminal_cover F d chosen) hns
  obtain ⟨C,hC,hm,hsel,horth⟩ := hyp.exists_moved_component_orthogonal_selection hns hF
  obtain ⟨_,_,I,hI,_⟩ := hsel
  refine ⟨C,hC,hm,horth,I,hI,?_⟩
  by_cases hv : v ∈ I
  · left
    obtain ⟨hCn,hI4,hV8,hX8,hmodel⟩ := source_large_fixed_line_marked_actions_at d earlier hq chosen
      structural alternatives classification F hne hZ hlarge g hgP hgH hyp hC hm hI.isIrrPlus hv hline hn
    exact ⟨hv,hCn,hI4,hV8,hX8,hmodel,source_large_fixed_line_double_actions_at d earlier hq chosen
      structural alternatives classification F hne hZ hlarge g hgP hgH hyp hC hm hI.isIrrPlus hv hline hn,
      source_large_fixed_line_ambient_actions_at d earlier hq chosen structural alternatives
        classification F hne hZ hlarge g hgP hgH hyp hC hm hI.isIrrPlus hv hline hn⟩
  · right
    let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
      (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
    obtain ⟨hXP,hN⟩ := source_terminal_actor_normal_in_sylow_at d earlier hq chosen
      structural alternatives F hne g hgP hgH
    have hind := terminal_component_normalizer_index_le_two d.qtke F (by decide) C hC
    exact ⟨hv,hyp.exchanged_constituent_geometry hns hC hm P
      ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hind hI hv⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/FixedLineTensor.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative TensorProduct


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Tensor CoreGeometry

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_deleted_tensor_catalogue_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (H : Subgroup F.TerminalHdot)
    (hm : FixedLineActions.PermutationTensorEmbedding F.terminalRepresentation H
      (BinaryPermutation.coreRepresentation (Fin 5))) :
    letI := chosen.elementary
    letI := F.U_normal
    RankCore.ActionAlternative.{0} (sourceAction F
      (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)) := by
  let := chosen.elementary
  let := F.U_normal
  let hk := source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ
  obtain ⟨A,hAA,hA,e,f,hf⟩ := FixedLineTensor.five_tensor_coordinates
    F.terminalRepresentation hyp H hm
  let σ := (BinaryPermutation.coreRepresentation (Fin 5)).comp A.subtype
  have hσ : IsSourceConstituent hAA σ :=
    Or.inr ⟨LinearEquiv.refl (ZMod 2) _,fun _ _ => rfl⟩
  let q := QuotientGroup.quotientMulEquivOfEq hk.symm
  exact .tensor A hAA σ hA hσ (q.trans e) f (fun a w => hf (q a) w)

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/FixedLineSix.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative TensorProduct


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Tensor CoreGeometry

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_six_tensor_embedding_exclusion_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
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
      (BinaryPermutation.naturalRepresentation (Fin 6))) : False := by
  let := chosen.elementary
  have hns := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  let := hyp.irreducible_of_not_solvable hns
  have hl := FixedLineSix.six_three_rank F.terminalRepresentation H hm
  have hk := source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ
  have htwo : IsPGroup 2 F.terminalHatAction.ker := hk ▸ pCore_isPGroup
  have hu : primeRank 3 F.TerminalHdot ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ htwo).trans
      ((Chapter14.Section03.NonabelianSource.Recognition.pointNormalizer_sqtk
        d.qtke F (by decide)).stronglyQuasithin 3 Nat.prime_three (by decide))
  omega

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/CatalogueTensor.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Theory.GroupTheory

open scoped IsMulCommutative TensorProduct


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension CoreGeometry

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_case_nine_catalogue_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hm : ChapterG.Section11.CaseNine F.terminalRepresentation) :
    letI := chosen.elementary
    letI := F.U_normal
    RankCore.ActionAlternative.{0} (sourceAction F
      (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)) := by
  let := chosen.elementary
  let := F.U_normal
  let hk := source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ
  let q := QuotientGroup.quotientMulEquivOfEq hk.symm
  exact CatalogueTensor.of_case_nine (sourceAction F hk) F.terminalRepresentation q
    (fun _ _ => rfl) hm

theorem source_case_ten_exclusion_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (X : Subgroup F.TerminalHdot)
    (hm : ChapterG.Section11.CaseTen F.terminalRepresentation X) : False := by
  let := chosen.elementary
  obtain ⟨e,_⟩ := hm.2
  have hl := Theory.GroupTheory.primeRank_le_of_injective 3
    RankTwo.Imprimitive.AlternatingSixTensor.base
    RankTwo.Imprimitive.AlternatingSixTensor.base_injective
  rw [primeRank_prod_eq_add,
    GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 6 3 Nat.prime_three (by decide),
    GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 3 3 Nat.prime_three (by decide)] at hl
  have he := Theory.GroupTheory.primeRank_equiv 3 e
  have hk := source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ
  have htwo : IsPGroup 2 F.terminalHatAction.ker := hk ▸ pCore_isPGroup
  have hu : primeRank 3 F.TerminalHdot ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ htwo).trans
      ((Chapter14.Section03.NonabelianSource.Recognition.pointNormalizer_sqtk
        d.qtke F (by decide)).stronglyQuasithin 3 Nat.prime_three (by decide))
  omega

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/CatalogueComponents.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Theory.GroupTheory

open scoped IsMulCommutative

open ClassicalOrthogonal.FourPlusMatrix

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension CoreGeometry LargerDimension.LocalAction.Components

open Chapter14.Section03.NonabelianSource.Recognition

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_case_seven_catalogue_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (X : Subgroup F.TerminalHdot)
    (hm : ChapterG.Section11.CaseSeven F.terminalRepresentation X) :
    letI := chosen.elementary
    letI := F.U_normal
    RankCore.ActionAlternative.{0} (sourceAction F
      (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)) := by
  let := chosen.elementary
  let := F.U_normal
  obtain ⟨_,_,e₀,f₀,h₀⟩ := hm
  let N := generalizedFitting F.TerminalHdot
  let e := e₀.trans Binary.orthogonalEquiv.symm
  let f := f₀.trans Binary.binaryCoordinates
  have hf (a : N) (w : Additive F.Uhat) :
      f (F.terminalRepresentation a w) = Binary.action (e a) (f w) := by
    change Binary.binaryCoordinates (f₀ (F.terminalRepresentation a w)) = _
    have hh := h₀ a w
    change f₀ (F.terminalRepresentation a w) = _ at hh
    rw [hh]
    have hh := Binary.binaryCoordinates_projective_equivariant
      (Binary.orthogonalEquiv.symm (e₀ a)) (f₀ w)
    rw [MulEquiv.apply_symm_apply] at hh
    exact hh
  obtain ⟨g,_,hgP,hgH⟩ := exists_source_conjugator_at d earlier hq chosen structural F
  obtain ⟨_,_,B,v,hyp,_,_⟩ := source_terminal_marked_hypothesis_at F d earlier hq chosen
    structural alternatives hne g hgP hgH
  have hres := OrthogonalOrbit.residual_eq_of_coordinates F.terminalRepresentation
    hyp.faithful B hyp.nondegenerate hyp.preserves N e f hf
  let hk := source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ
  let q := QuotientGroup.quotientMulEquivOfEq hk.symm
  let R := (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  have hR : R.map q.toMonoidHom = N := by
    dsimp only [R]
    rw [map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _),
      map_pResidual_of_surjective 2 _ q.surjective,hres]
  let eR : R ≃* N := (q.subgroupMap R).trans (MulEquiv.subgroupCongr hR)
  refine .orthogonal ((eR.trans e).trans elementaryEquiv)
    (f.trans Binary.binaryCoordinates.symm) ?_
  intro k w
  apply Binary.binaryCoordinates.injective
  change Binary.binaryCoordinates (Binary.binaryCoordinates.symm
    (f (F.terminalRepresentation (q k.val) w))) = _
  rw [Binary.binaryCoordinates.apply_symm_apply]
  change f (F.terminalRepresentation (eR k) w) =
    Binary.binaryCoordinates (((elementaryEquiv (e (eR k))).val.val)
      (Binary.binaryCoordinates.symm (f w)))
  rw [hf]
  rw [show Binary.binaryCoordinates (((elementaryEquiv (e (eR k))).val.val)
      (Binary.binaryCoordinates.symm (f w))) =
      Binary.action (e (eR k)) (Binary.binaryCoordinates (Binary.binaryCoordinates.symm (f w))) from
        toOrthogonal_coordinates (e (eR k)) (Binary.binaryCoordinates.symm (f w))]
  rw [Binary.binaryCoordinates.apply_symm_apply]

open Sporadic.Mathieu

open Janko4.InvolutionCentralizers.First.QuotientExtension

open ChapterH.Section10To12

theorem source_case_thirteen_catalogue_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hlarge : 64 < Nat.card F.U)
    (hm : ChapterG.Section11.CaseThirteen F.terminalRepresentation) :
    letI := chosen.elementary
    letI := F.U_normal
    RankCore.ActionAlternative.{0} (sourceAction F
      (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)) := by
  let := chosen.elementary
  let := F.U_normal
  obtain ⟨hd,⟨e⟩⟩ := hm
  let hk := source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ
  let q := QuotientGroup.quotientMulEquivOfEq hk.symm
  have hK := triple_of_native (q.trans e) (pCore_quotient_pCore_eq_bot 2)
  obtain ⟨g,_,hgP,hgH⟩ := exists_source_conjugator_at d earlier hq chosen structural F
  obtain ⟨_,_,B,v,hyp,_,_⟩ := source_terminal_marked_hypothesis_at F d earlier hq chosen
    structural alternatives hne g hgP hgH
  have hi := hyp.irreducible_of_not_solvable
    (source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives F hne hZ hlarge)
  refine .tripleM22 hK ?_ hd
  change IsIrreducible (F.terminalRepresentation.comp q.toMonoidHom)
  exact (irreducible_comp_surjective_iff q.toMonoidHom q.surjective _).mpr hi

theorem source_case_three_exclusion_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hlarge : 64 < Nat.card F.U)
    (hm : ChapterG.Section11.CaseThree F.terminalRepresentation) : False := by
  obtain ⟨_,H,_,⟨e⟩⟩ := hm
  let := extraspecial_model_solvable
  exact source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)

theorem source_large_terminal_dimension_ge_six_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hlarge : 64 < Nat.card F.U) : 6 ≤ finrank (ZMod 2) (Additive F.Uhat) := by
  have hcenter := (source_extraspecial_order_at d earlier hq chosen structural alternatives
    F hne hZ).1.center_order_p
  have hc : Nat.card F.U = 2 ^ (finrank (ZMod 2) (Additive F.Uhat) + 1) := by
    rw [card_eq_card_quotient_mul_card_subgroup (center F.U),hcenter]
    change Nat.card (Additive F.Uhat) * 2 = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,pow_succ]
  by_contra hn
  have hb := Nat.pow_le_pow_right (n := 2) (by decide)
    (by omega : finrank (ZMod 2) (Additive F.Uhat) + 1 ≤ 6)
  rw [← hc] at hb
  norm_num at hb
  omega

theorem source_case_four_exclusion_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hm : ChapterG.Section11.CaseFour F.terminalRepresentation) : False := by
  let := chosen.elementary
  obtain ⟨hd,e,f,hf⟩ := hm
  let C := generalizedFitting F.TerminalHdot
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup C := e.isSimpleGroup
  let : Group.IsPerfect (alternatingGroup (Fin 7)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hna : ¬ IsMulCommutative C := Group.IsPerfect.not_isMulCommutative C
  have hC : IsComponent F.TerminalHdot C := SimpleSocle.isComponent hna
  have hc : centralizer (C : Set F.TerminalHdot) = ⊥ := SimpleSocle.centralizer_eq_bot hna
  let τ := (BinaryPermutation.alternatingCoreRepresentation (Fin 7)).comp e.toMonoidHom
  let : IsIrreducible (BinaryPermutation.alternatingCoreRepresentation (Fin 7)) :=
    AlternatingSevenBinarySmallModels.core_irreducible
  have hiτ : IsIrreducible τ :=
    (irreducible_comp_surjective_iff e.toMonoidHom e.surjective _).mpr inferInstance
  let E : Representation.Equiv (F.terminalRepresentation.comp C.subtype) τ := .mk f (by
    intro a
    apply LinearMap.ext
    intro w
    exact hf a w)
  have hi : IsIrreducible (F.terminalRepresentation.comp C.subtype) :=
    (RepEquiv.ofRepresentationEquiv E).irreducible_of_euqiv hiτ
  obtain ⟨g,_,hgP,hgH⟩ := exists_source_conjugator_at d earlier hq chosen structural F
  obtain ⟨_,heX,B,v,hyp,_,_⟩ := source_terminal_marked_hypothesis_at F d earlier hq chosen
    structural alternatives hne g hgP hgH
  let := heX
  have hX : F.terminalDot (F.X g) ≠ ⊥ := by
    intro hz
    have hh := hyp.dimension_bound.1
    have hb := Group.rank_le_of_surjective
      (QuotientGroup.mk' ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
      (QuotientGroup.mk'_surjective _)
    have hzero : Group.rank (F.terminalDot (F.X g)) = 0 := by
      rw [hz]
      exact Group.rank_eq_zero _
    omega
  have hmove : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥ := by
    intro hh
    rw [commutator_comm,commutator_eq_bot_iff_le_centralizer,hc] at hh
    exact hX (le_bot_iff.mp hh)
  exact source_no_alternating_seven_component_at d earlier hq chosen structural alternatives
    F hne hZ hd g hgP hgH C hC hmove hi e

theorem source_case_five_exclusion_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hm : ChapterG.Section11.CaseFive F.terminalRepresentation B) : False := by
  obtain ⟨_,c,K,hKn,_,e,he⟩ := ChapterG.Section11.SplitSix.caseFive_selfcentralizing_marking hm
  let := hKn
  obtain ⟨g,_,hgP,hgH⟩ := exists_source_conjugator_at d earlier hq chosen structural F
  obtain ⟨_,_,B',v,_,hline,_⟩ := source_terminal_marked_hypothesis_at F d earlier hq chosen
    structural alternatives hne g hgP hgH
  let C := ChapterG.Section10.pointCentralizer F.terminalRepresentation v
  let D := F.terminalDot (centralizer (F.ZU : Set G))
  have hHc : F.H ≤ centralizer (F.ZU : Set G) := by
    rw [hZ]
    exact normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
  have hD : D = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact mem_map_of_mem _ (hHc b.property)
  have hu := CaseOneHS.source_center_centralizing_point_image_three_rank_le_one_at
    d earlier hq chosen structural alternatives F hne v hline.symm g hgP hgH
  change primeRank 3 (C.subgroupOf D) ≤ 1 at hu
  have hpD : C ≤ D := by rw [hD]; exact le_top
  rw [primeRank_equiv 3 (subgroupOfEquivOfLe hpD)] at hu
  have hr : 2 ≤ primeRank 3 (C.subgroupOf K) := by
    let a := BinaryNaturalDual.Transport.stabilizerEquiv (F.terminalRepresentation.comp K.subtype)
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) e c.toLinearEquiv he v
    have hb := BinaryPermutation.PointStabilizerRank.two_le_natural_stabilizer
      (by simp : 8 ≤ Fintype.card (Fin 8)) (c v)
    exact hb.trans (primeRank_equiv 3 a).ge
  let j : C.subgroupOf K →* C := {
    toFun a := ⟨a.val.val,a.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun z : C => z.val) hab))
  have hl := Theory.GroupTheory.primeRank_le_of_injective 3 j hj
  omega

theorem source_case_six_exclusion_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hm : ChapterG.Section11.CaseSix F.terminalRepresentation) : False := by
  let := chosen.elementary
  obtain ⟨hd,e,f,hf⟩ := hm
  let c := source_closure_geometry_at F d earlier hq chosen structural alternatives hne
  obtain ⟨g,_,hgP,hgH⟩ := exists_source_conjugator_at d earlier hq chosen structural F
  let q := F.uhatQuadraticForm (by decide) c.two c.frattini_point
    (center_frattini_bot_of_center_point F c hZ)
  obtain ⟨_,hqi,hqn⟩ := quadratic_intersection_of_center_point F c (by decide) hZ g
    (disjoint_iff.mpr (F.parabolic_displaced_centers (by decide) L chosen.normalizes
      c.seed_center g hgP hgH).1)
  have hterminal (a : F.TerminalHdot) (w : Additive F.Uhat) :
      q (F.terminalRepresentation a w) = q w := by
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact hqi a w.toMul
  have htrans : ∀ x y : Additive F.Uhat, x ≠ 0 → y ≠ 0 →
      ∃ b, F.terminalRepresentation b x = y := by
    intro x y hx hy
    obtain ⟨b,hb⟩ := Atlas.G2.Natural.action_transitive (x := f x) (y := f y)
      (fun hz => hx (f.map_eq_zero_iff.mp hz)) (fun hz => hy (f.map_eq_zero_iff.mp hz))
    refine ⟨e.symm b,f.injective ?_⟩
    rw [hf,e.apply_symm_apply]
    exact hb
  exact not_nondegenerate_quadratic_of_nonzero_transitive F.terminalRepresentation
    (by omega) htrans q hterminal hqn

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/CatalogueExclusion.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

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

theorem source_large_exclusion_of_marked_action_of_mixed_size_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hlarge : 64 < Nat.card F.U)
    (models : letI := chosen.elementary
      letI := F.U_normal
      RankCore.ActionAlternative.{w} (sourceAction F
        (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ))) : False := by
  let := chosen.elementary
  let := F.U_normal
  let hk := source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ
  cases models with
  | orthogonal κ e he =>
    exact Orthogonal.source_orthogonal_exclusion_at d earlier hq chosen structural alternatives
      F hne hZ κ e he
  | symmetricSeven e p he =>
    obtain ⟨g,hg,hgP,hgH⟩ := exists_source_conjugator_at d earlier hq chosen structural F
    apply source_symmetric_seven_contradiction_at d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hg hgP hgH e p
    intro a v
    exact (he (QuotientGroup.mk' (pCore 2 F.H) a) v).symm
  | tensor D hAD σ hD hσ e f hf =>
    exact source_tensor_exclusion_of_mixed_size_at d earlier hq chosen structural alternatives
      classification size F hne hZ (tensorCoordinates F hk hAD σ hD hσ e f hf)
  | tripleM22 hK hirr hd =>
    exact source_mathieu_exclusion_at d earlier hq chosen structural alternatives classification
      F hne hZ hlarge hK hirr hd

theorem source_case_nine_exclusion_of_mixed_size_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hlarge : 64 < Nat.card F.U)
    (hm : ChapterG.Section11.CaseNine F.terminalRepresentation) : False := by
  exact source_large_exclusion_of_marked_action_of_mixed_size_at d earlier hq chosen
    structural alternatives classification size F hne hZ hlarge
    (source_case_nine_catalogue_at d earlier hq chosen structural alternatives F hne hZ hm)

theorem source_deleted_tensor_embedding_exclusion_of_mixed_size_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
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
  exact source_large_exclusion_of_marked_action_of_mixed_size_at d earlier hq chosen
    structural alternatives classification size F hne hZ hlarge
    (source_deleted_tensor_catalogue_at d earlier hq chosen structural alternatives
      F hne hZ g hyp H hm)

section FixedLineReduction
local instance : Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.Field 1) := ZMod.algebra _ 2

theorem source_large_fixed_line_remainder_of_mixed_size_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
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
  obtain ⟨heU,heX,B,v,hyp,hline,hfix⟩ := source_terminal_marked_hypothesis_at F d earlier hq
    chosen structural alternatives hne g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,?_,?_⟩
  · exact ⟨_,hfix,source_terminal_actor_normal_in_sylow_at d earlier hq chosen structural
      alternatives F hne g hgP hgH⟩
  by_cases hw : ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))
  · have hc := source_large_lowRank_conclusion_at d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH B v hyp hline hfix hw
    have hd := source_large_terminal_dimension_ge_six_at d earlier hq chosen structural alternatives
      F hne hZ hlarge
    rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
    · have := h1.1; omega
    · have := h2.1; omega
    · exact (source_case_three_exclusion_at d earlier hq chosen structural alternatives
        F hne hZ hlarge h3).elim
    · exact (source_case_four_exclusion_at d earlier hq chosen structural alternatives F hne hZ h4).elim
    · exact (source_case_five_exclusion_at d earlier hq chosen structural alternatives F hne hZ B h5).elim
    · exact (source_case_six_exclusion_at d earlier hq chosen structural alternatives F hne hZ h6).elim
    · exact (source_large_exclusion_of_marked_action_of_mixed_size_at d earlier hq chosen
        structural alternatives classification size F hne hZ hlarge
        (source_case_seven_catalogue_at d earlier hq chosen structural alternatives F hne hZ _ h7)).elim
    · exact (CatalogueExchanged.case_eight_not_lowRank v hyp.point_ne_zero h8 hw).elim
    · exact (source_case_nine_exclusion_of_mixed_size_at d earlier hq chosen structural alternatives
        classification size F hne hZ hlarge h9).elim
    · exact (source_case_ten_exclusion_at d earlier hq chosen structural alternatives F hne hZ _ h10).elim
    · exact (source_case_eleven_not_lowRank F v hyp.point_ne_zero _ h11 hw).elim
    · exact (CatalogueExchanged.case_twelve_not_lowRank v hyp.point_ne_zero h12 hw).elim
    · exact (source_large_exclusion_of_marked_action_of_mixed_size_at d earlier hq chosen
        structural alternatives classification size F hne hZ hlarge
        (source_case_thirteen_catalogue_at d earlier hq chosen structural alternatives F hne hZ hlarge h13)).elim
  · have hmodule := source_fixed_line_module_at d earlier hq chosen structural alternatives
      F hne hZ hlarge g hgP hgH B v hyp hline hw
    obtain ⟨C,hC,hm,horth,I,hI,hmarked | hex⟩ := source_large_fixed_line_constituent_reduction_at
      d earlier hq chosen structural alternatives classification F hne hZ hlarge g hgP hgH hyp hline hw
    · obtain ⟨hv,hCn,hI4,hV8,hX8,_,_,hamb⟩ := hmarked
      rcases hamb with hnat | hfive | hsix
      · exact ⟨hw,hmodule,C,hC,hm,horth,I,hI,Or.inl ⟨hv,hCn,hI4,hV8,hX8,hnat⟩⟩
      · exact (source_deleted_tensor_embedding_exclusion_of_mixed_size_at d earlier hq chosen
          structural alternatives classification size F hne hZ hlarge g hyp _ hfive).elim
      · exact (source_six_tensor_embedding_exclusion_at d earlier hq chosen structural alternatives
          F hne hZ hlarge g hyp _ hsix).elim
    · exact ⟨hw,hmodule,C,hC,hm,horth,I,hI,Or.inr hex⟩

theorem source_large_semilinear_remainder_of_mixed_size_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
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
    source_large_fixed_line_remainder_of_mixed_size_at d earlier hq chosen structural alternatives
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
    have hY := (source_large_marked_double_kernel_at d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH hyp hC hm hI.isIrrPlus hv hline hn
      (by omega) hk).1
    exact ⟨C,hC,hm,horth,I,hI,Or.inl ⟨hv,hCn,hI4,hV8,hX8,hY,⟨a⟩⟩⟩
  · exact ⟨C,hC,hm,horth,I,hI,Or.inr hx⟩

theorem source_large_coefficient_remainder_of_mixed_size_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
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
    source_large_semilinear_remainder_of_mixed_size_at d earlier hq chosen structural alternatives
      classification size F hne hZ hlarge g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,?_⟩
  obtain ⟨C,hC,hm,horth,I,hI,ha | hx⟩ := hrem
  · obtain ⟨hv,hCn,hI4,hV8,hX8,hY,⟨a⟩⟩ := ha
    have hf := (source_terminal_ranks_of_no_lowRank_at d earlier hq chosen structural alternatives
      F hne hZ g hgP hgH v hline hn).1
    rw [←hline] at hf
    exact ⟨C,hC,hm,horth,I,hI,Or.inl ⟨hv,hCn,hI4,hV8,hX8,hY,a,
      a.actor_field_surjective _ v hyp.point_ne_zero hf,
      a.coefficient_kernel_twoCore hyp.twoCore_eq_bot,
      a.component_centralizer_index _ v hyp.point_ne_zero hf,
      a.generated_by_component_centralizer_actor _ v hyp.point_ne_zero hf⟩⟩
  · exact ⟨C,hC,hm,horth,I,hI,Or.inr hx⟩

theorem source_large_projective_remainder_of_mixed_size_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
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
    source_large_coefficient_remainder_of_mixed_size_at d earlier hq chosen structural alternatives
      classification size F hne hZ hlarge g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,?_⟩
  obtain ⟨C,hC,hm,horth,I,hI,ha | hx⟩ := hrem
  · obtain ⟨hv,hCn,hI4,hV8,hX8,hY,a,hfield,hcore,hindex,hgen⟩ := ha
    have hf := (source_terminal_ranks_of_no_lowRank_at d earlier hq chosen structural alternatives
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

end

/- Specialization of CaseOneLarge/FixedLineRecognition.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.LocalAction.Components

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

namespace FixedLineReduction

theorem source_large_classified_remainder_of_mixed_size_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
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
      ClassifiedRemainder F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g)) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,hrem⟩ :=
    source_large_projective_remainder_of_mixed_size_at d earlier hq chosen structural alternatives
      classification size F hne hZ hlarge g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,?_⟩
  obtain ⟨C,hC,hm,horth,I,hI,ha | hx⟩ := hrem
  · obtain ⟨hv,hCn,hI4,hV8,hX8,hY,a,hfield,hcore,hindex,hgen,hinj,heven,hfour,hfive⟩ := ha
    have hf := (source_terminal_ranks_of_no_lowRank_at d earlier hq chosen structural alternatives
      F hne hZ g hgP hgH v hline hn).1
    rw [←hline] at hf
    exact ⟨C,hC,hm,horth,I,hI,Or.inl ⟨hv,hCn,hI4,hV8,hX8,hY,a,
      hfield,hcore,hindex,hgen,hinj,heven,hfour,hfive,
      a.coefficientFive_models B hyp.nondegenerate hyp.preserves hyp.twoCore_eq_bot
        _ v hyp.point_ne_zero hf hY⟩⟩
  · exact ⟨C,hC,hm,horth,I,hI,Or.inr hx⟩

end FixedLineReduction

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/FixedLineOrthogonal.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Matrix

open scoped MatrixGroups IsMulCommutative


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Theory.GroupTheory ClassicalOrthogonal.FourPlusMatrix

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.LocalAction.Components

open Chapter14.Section03.NonabelianSource.Recognition

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_coefficient_top_exclusion_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    {H : Subgroup F.TerminalHdot}
    (a : FixedLineSemilinear.Coordinates F.terminalRepresentation H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hnd : B.Nondegenerate)
    (hB : ∀ g u v, B (F.terminalRepresentation g u) (F.terminalRepresentation g v) = B u v)
    (htop : a.coefficientFive.range = ⊤) : False := by
  let := chosen.elementary
  let := F.U_normal
  obtain ⟨e,f,hf⟩ := a.orthogonal_coordinates_of_coefficient_top B hnd hB htop
  let N := H ⊔ centralizer (H : Set F.TerminalHdot)
  let : N.Normal := by
    change (H ⊔ centralizer (H : Set F.TerminalHdot)).Normal
    rw [←a.ambientField_kernel]
    infer_instance
  have hres := OrthogonalOrbit.residual_eq_of_coordinates F.terminalRepresentation
    F.terminalRepresentation_injective B hnd hB N e f hf
  let hk := source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ
  let q := QuotientGroup.quotientMulEquivOfEq hk.symm
  let R := (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  have hR : R.map q.toMonoidHom = N := by
    dsimp only [R]
    rw [map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _),
      map_pResidual_of_surjective 2 _ q.surjective,hres]
  let eR : R ≃* N := (q.subgroupMap R).trans (MulEquiv.subgroupCongr hR)
  apply Orthogonal.source_orthogonal_exclusion_at d earlier hq chosen structural alternatives F hne hZ
    ((eR.trans e).trans elementaryEquiv) (f.trans Binary.binaryCoordinates.symm)
  dsimp only
  intro k w
  apply Binary.binaryCoordinates.injective
  change Binary.binaryCoordinates (Binary.binaryCoordinates.symm
    (f (F.terminalRepresentation (q k.val) w))) = _
  rw [Binary.binaryCoordinates.apply_symm_apply]
  change f (F.terminalRepresentation (eR k) w) =
    Binary.binaryCoordinates (((elementaryEquiv (e (eR k))).val.val)
      (Binary.binaryCoordinates.symm (f w)))
  rw [hf]
  rw [show Binary.binaryCoordinates (((elementaryEquiv (e (eR k))).val.val)
      (Binary.binaryCoordinates.symm (f w))) =
      Binary.action (e (eR k)) (Binary.binaryCoordinates (Binary.binaryCoordinates.symm (f w))) from
        toOrthogonal_coordinates (e (eR k)) (Binary.binaryCoordinates.symm (f w))]
  rw [Binary.binaryCoordinates.apply_symm_apply]

namespace FixedLineReduction

theorem source_large_transposition_remainder_of_mixed_size_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
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
      TranspositionRemainder F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g)) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,hrem⟩ :=
    source_large_classified_remainder_of_mixed_size_at d earlier hq chosen structural alternatives
      classification size F hne hZ hlarge g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,?_⟩
  obtain ⟨C,hC,hm,horth,I,hI,ha | hx⟩ := hrem
  · obtain ⟨hv,hCn,hI4,hV8,hX8,hY,a,hfield,hcore,hindex,hgen,hinj,heven,hfour,hfive,hmodels⟩ := ha
    rcases hmodels with ⟨e,he⟩ | ht
    · have htop : a.coefficientFive.range = ⊤ := MonoidHom.range_eq_top.mpr (by
        intro s
        obtain ⟨b,rfl⟩ := e.surjective s
        exact ⟨b,(he b).symm⟩)
      exact (source_coefficient_top_exclusion_at d earlier hq chosen structural alternatives F hne hZ
        a B hyp.nondegenerate hyp.preserves htop).elim
    · exact ⟨C,hC,hm,horth,I,hI,Or.inl ⟨hv,hCn,hI4,hV8,hX8,hY,a,
        hfield,hcore,hindex,hgen,hinj,heven,hfour,hfive,ht⟩⟩
  · exact ⟨C,hC,hm,horth,I,hI,Or.inr hx⟩

end FixedLineReduction

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/FixedLineNaturalSource.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Matrix Theory.GroupTheory

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Tensor CoreGeometry

open LargerDimension.LocalAction.Components

open scoped IsMulCommutative TensorProduct

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_natural_tensor_catalogue_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    {H : Subgroup F.TerminalHdot}
    (a : FixedLineSemilinear.Coordinates F.terminalRepresentation H)
    (t : Equiv.Perm (Fin 5)) (ht : t.IsSwap)
    (e : a.coefficient.range ≃* centralizer ({t} : Set (Equiv.Perm (Fin 5))))
    (he : ∀ b, (e b).val = a.coefficientFive b) :
    letI := chosen.elementary
    letI := F.U_normal
    RankCore.ActionAlternative.{0} (sourceAction F
      (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)) := by
  let := chosen.elementary
  let := F.U_normal
  let hk := source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ
  obtain ⟨σ,hσ,actor,space,hspace⟩ := a.natural_tensor_coordinates t ht e he
  let q := QuotientGroup.quotientMulEquivOfEq hk.symm
  exact .tensor ⊤ le_top σ (Or.inl rfl) (Or.inl hσ) (q.trans actor) space
    (fun g w => hspace (q g) w)

namespace FixedLineReduction

theorem source_large_exchanged_remainder_of_mixed_size_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
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
      ∃ C : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot C ∧
        ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
        ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B C ∧
        ∃ I : Submodule (ZMod 2) (Additive F.Uhat),
          Representation.BinaryOffender.Homogeneous.IsIrrPlusWith F.terminalRepresentation
            (componentOrbit C ⊤) (F.terminalDot (F.X g)) I ∧
          v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry F.terminalRepresentation B v
            (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I := by
  obtain ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,hrem⟩ :=
    source_large_transposition_remainder_of_mixed_size_at d earlier hq chosen structural alternatives
      classification size F hne hZ hlarge g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,?_⟩
  obtain ⟨C,hC,hm,horth,I,hI,ha | hx⟩ := hrem
  · obtain ⟨_,_,_,_,_,_,a,_,_,_,_,_,_,_,_,t,ht,e,he⟩ := ha
    exact (source_large_exclusion_of_marked_action_of_mixed_size_at d earlier hq chosen
      structural alternatives classification size F hne hZ hlarge
      (source_natural_tensor_catalogue_at d earlier hq chosen structural alternatives F hne hZ a t ht e he)).elim
  · exact ⟨C,hC,hm,horth,I,hI,hx⟩

end FixedLineReduction

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end
