module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.At.Catalogue
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedGeometry
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedIsotropic
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedIsotropicModels
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedIsotropicAction
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedNondegenerate
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedNondegenerateExclusion

/-!
# Excluding the exchanged constituent at G,T

The literal constituent quotient gives the genuine G.9 and G.12
recognitions. The isotropic pair yields the marked symmetric-seven
contradiction. For the nondegenerate constituent, both kernel cases are
resolved; the noncentral case gives the actual orthogonal A5 pair, whose
point rank contradicts the original marked centralizer bound.

The earlier inputs are restricted to the original group and Sylow subgroup.
The universal APIs remain unchanged. The `import all` edges intentionally
reuse the private calculations of the corresponding source implementation;
only deductions depending on the earlier inputs are specialized here.
Source: Aschbacher--Smith, G.11.6, G.12, 14.4.2,9--14; printed pp.365--372,1006--1012; refs/quasithin.pdf.
-/

public noncomputable section

/- Specialization of CaseOneLarge/ExchangedGeometry.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Tensor CoreGeometry

open LargerDimension.LocalAction.Components

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_exchanged_completion_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)))
    {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit C ⊤)
      (F.terminalDot (F.X g)) I) (hv : v ∉ I) :
    ExchangedGeometry.CompletedData F.terminalRepresentation B C (F.terminalDot (F.X g)) I hI := by
  let := chosen.elementary
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨hXP,hN⟩ := source_terminal_actor_normal_in_sylow_at d earlier hq chosen
    structural alternatives F hne g hgP hgH
  have hns := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hind := Chapter14.Section03.NonabelianSource.Recognition.terminal_component_normalizer_index_le_two
    d.qtke F (by decide) C hC
  obtain ⟨_,hE,hX,_⟩ := source_terminal_ranks_of_no_lowRank_at d earlier hq chosen
    structural alternatives F hne hZ g hgP hgH v hline hn
  have hb : 2 * (Group.rank (F.terminalDot (F.X g)) + 1) =
      finrank (ZMod 2) (Additive F.Uhat) := by omega
  have hPX : (P : Subgroup F.TerminalHdot) ≤ normalizer (F.terminalDot (F.X g) : Set F.TerminalHdot) :=
    (normal_subgroupOf_iff_le_normalizer hXP).mp hN
  exact ExchangedGeometry.complete_data hyp hns hC hm P hXP hPX hind hI hv hb


end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/ExchangedIsotropic.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Tensor CoreGeometry

open LargerDimension.LocalAction.Components

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_exchanged_component_input_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)))
    {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit C ⊤)
      (F.terminalDot (F.X g)) I) (hv : v ∉ I) :
    ExchangedGeometry.CompletedData F.terminalRepresentation B C (F.terminalDot (F.X g)) I hI ∧
    ((B.restrict I).Nondegenerate ∨
      ((∀ a ∈ I, ∀ b ∈ I, B a b = 0) ∧
        ExchangedIsotropic.IsotropicData F.terminalRepresentation C
          (F.terminalDot (F.X g)) I hI)) := by
  have hc := source_exchanged_completion_at d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hline hn hC hm hI hv
  refine ⟨hc,?_⟩
  rcases hc.2.2.2.2.2.2 with hnd | ⟨hiso,hf,hns,_⟩
  · exact Or.inl hnd
  have hfaith : Function.Injective
      (invariantSubspace F.terminalRepresentation (componentOrbit C ⊤) I hI.invariant).toRepresentation := by
    intro a b hab
    exact hf (Units.ext hab)
  have hnonsolv := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  let := chosen.elementary
  have hind := Chapter14.Section03.NonabelianSource.Recognition.terminal_component_normalizer_index_le_two
    d.qtke F (by decide) C hC
  exact Or.inr ⟨hiso,ExchangedIsotropic.isotropic_data hyp hnonsolv hC hind hI hc hiso
    hfaith (source_terminal_cover F d chosen) hns⟩


end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/ExchangedIsotropicModels.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS
noncomputable section

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative MatrixGroups MonoidAlgebra


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Tensor CoreGeometry

open LargerDimension.LocalAction.Components

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

public theorem source_exchanged_recognized_component_input_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)))
    {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit C ⊤)
      (F.terminalDot (F.X g)) I) (hv : v ∉ I) :
    ExchangedGeometry.CompletedData F.terminalRepresentation B C (F.terminalDot (F.X g)) I hI ∧
    ((B.restrict I).Nondegenerate ∨
      ((∀ a ∈ I, ∀ b ∈ I, B a b = 0) ∧
        ExchangedIsotropic.IsotropicData F.terminalRepresentation C
          (F.terminalDot (F.X g)) I hI ∧
        Nonempty (C ≃* alternatingGroup (Fin 7)) ∧
        finrank (ZMod 2) I = 4 ∧ finrank (ZMod 2) (Additive F.Uhat) = 8)) := by
  obtain ⟨hc,hd⟩ := source_exchanged_component_input_at d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hline hn hC hm hI hv
  refine ⟨hc,?_⟩
  rcases hd with hnd | ⟨hiso,hi⟩
  · exact Or.inl hnd
  let := chosen.elementary
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨hXP,hN⟩ := source_terminal_actor_normal_in_sylow_at d earlier hq chosen
    structural alternatives F hne g hgP hgH
  have hnonsolv := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  obtain ⟨e⟩ := ExchangedIsotropicModels.component_alternating_seven hyp hnonsolv hC
    hI hc hiso hi P hXP ((normal_subgroupOf_iff_le_normalizer hXP).mp hN)
  have hf : Function.Injective (invariantSubspace F.terminalRepresentation
      (componentOrbit C ⊤) I hI.invariant).toRepresentation := by
    rcases hc.2.2.2.2.2.2 with hnd | ⟨_,hf,_,_⟩
    · exfalso
      apply hI.isIrrPlus.ne_bot F.terminalRepresentation
      apply le_bot_iff.mp
      intro u hu
      exact congrArg Subtype.val (hnd.1 ⟨u,hu⟩ (fun w => hiso u hu w w.property))
    · exact fun a b hab => hf (Units.ext hab)
  obtain ⟨_,hE,hX,_⟩ := source_terminal_ranks_of_no_lowRank_at d earlier hq chosen
    structural alternatives F hne hZ g hgP hgH v hline hn
  have hb : 2 * (Group.rank (F.terminalDot (F.X g)) + 1) =
      finrank (ZMod 2) (Additive F.Uhat) := by omega
  have hd := ExchangedIsotropicModels.alternating_seven_degree hyp hnonsolv hC hI hc hf hb
    ((MulEquiv.subgroupCongr hi.1).trans e)
  exact Or.inr ⟨hiso,hi,⟨e⟩,hd⟩

namespace FixedLineReduction

public theorem source_large_recognized_isotropic_remainder_of_mixed_size_at (d : Counterexample T L)
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
        ∃ hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation
            (componentOrbit C ⊤) (F.terminalDot (F.X g)) I,
          v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry F.terminalRepresentation B v
            (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I ∧
          ExchangedGeometry.CompletedData F.terminalRepresentation B C
            (F.terminalDot (F.X g)) I hI ∧
          ((B.restrict I).Nondegenerate ∨
            ((∀ a ∈ I, ∀ b ∈ I, B a b = 0) ∧
              ExchangedIsotropic.IsotropicData F.terminalRepresentation C
                (F.terminalDot (F.X g)) I hI ∧
              Nonempty (C ≃* alternatingGroup (Fin 7)) ∧
        finrank (ZMod 2) I = 4 ∧ finrank (ZMod 2) (Additive F.Uhat) = 8)) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,C,hC,hm,horth,I,hI,hv,hgeo⟩ :=
    source_large_exchanged_remainder_of_mixed_size_at d earlier hq chosen structural alternatives
      classification size F hne hZ hlarge g hgP hgH
  let := heU
  let := heX
  exact ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,C,hC,hm,horth,I,hI,hv,hgeo,
    source_exchanged_recognized_component_input_at d earlier hq chosen structural alternatives F hne hZ hlarge
      g hgP hgH hyp hline hn hC hm hI hv⟩

end FixedLineReduction

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

end

/- Specialization of CaseOneLarge/ExchangedIsotropicAction.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Tensor CoreGeometry

open LargerDimension.LocalAction.Components

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_exchanged_isotropic_contradiction_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)))
    {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit C ⊤)
      (F.terminalDot (F.X g)) I) (hv : v ∉ I)
    (hiso : ∀ a ∈ I, ∀ b ∈ I, B a b = 0) : False := by
  have hnotnd : ¬ (B.restrict I).Nondegenerate := by
    intro hnd
    apply hI.isIrrPlus.ne_bot F.terminalRepresentation
    apply le_bot_iff.mp
    intro a ha
    exact congrArg Subtype.val (hnd.1 ⟨a,ha⟩ (fun b => hiso a ha b b.property))
  obtain ⟨hc,hmodel⟩ := source_exchanged_recognized_component_input_at d earlier hq chosen
    structural alternatives F hne hZ hlarge g hgP hgH hyp hline hn hC hm hI hv
  obtain ⟨_,hi,⟨e⟩,hd,_⟩ := hmodel.resolve_left hnotnd
  have hf : Function.Injective (invariantSubspace F.terminalRepresentation
      (componentOrbit C ⊤) I hI.invariant).toRepresentation := by
    obtain ⟨_,hf,_,_⟩ := hc.2.2.2.2.2.2.resolve_left hnotnd
    exact fun a b hab => hf (Units.ext hab)
  have hnonsolv := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  obtain ⟨f,P,hP,_⟩ := ExchangedIsotropicModels.marked_symmetric_seven_pair hyp hnonsolv hC
    hI hc hf hd ((MulEquiv.subgroupCongr hi.1).trans e)
  let q : coreQuotient F.H ≃* F.TerminalHdot :=
    QuotientGroup.quotientMulEquivOfEq
      (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ).symm
  apply source_symmetric_seven_contradiction_at d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hg hgP hgH (q.trans f) P
  intro a w
  exact hP (QuotientGroup.mk' F.terminalHatAction.ker a) w

namespace FixedLineReduction

theorem source_large_nondegenerate_remainder_of_mixed_size_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
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
        ∃ hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation
            (componentOrbit C ⊤) (F.terminalDot (F.X g)) I,
          v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry F.terminalRepresentation B v
            (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I ∧
          ExchangedGeometry.CompletedData F.terminalRepresentation B C
            (F.terminalDot (F.X g)) I hI ∧ (B.restrict I).Nondegenerate := by
  obtain ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,C,hC,hm,horth,I,hI,hv,hgeo,hc,hmodel⟩ :=
    source_large_recognized_isotropic_remainder_of_mixed_size_at d earlier hq chosen structural
      alternatives classification size F hne hZ hlarge g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,C,hC,hm,horth,I,hI,hv,hgeo,hc,?_⟩
  rcases hmodel with hnd | ⟨hiso,_⟩
  · exact hnd
  · exact (source_exchanged_isotropic_contradiction_at d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hg hgP hgH hyp hline hn hC hm hI hv hiso).elim

end FixedLineReduction

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/ExchangedNondegenerate.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Tensor CoreGeometry

open LargerDimension.LocalAction.Components

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_exchanged_nondegenerate_recognition_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)))
    {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit C ⊤)
      (F.terminalDot (F.X g)) I) (hv : v ∉ I) (hnd : (B.restrict I).Nondegenerate) :
    ExchangedNondegenerate.RecognizedData F.terminalRepresentation B C
      (F.terminalDot (F.X g)) I hI ∧
    center (ExchangedNondegenerate.constituentLinearAction F.terminalRepresentation C
      (F.terminalDot (F.X g)) I hI).range = ⊥ ∧ center (componentOrbit C ⊤) = ⊥ := by
  let := chosen.elementary
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨hXP,hN⟩ := source_terminal_actor_normal_in_sylow_at d earlier hq chosen
    structural alternatives F hne g hgP hgH
  have hns := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hind := Chapter14.Section03.NonabelianSource.Recognition.terminal_component_normalizer_index_le_two
    d.qtke F (by decide) C hC
  have hPX : (P : Subgroup F.TerminalHdot) ≤ normalizer (F.terminalDot (F.X g) : Set F.TerminalHdot) :=
    (normal_subgroupOf_iff_le_normalizer hXP).mp hN
  have hc := source_exchanged_completion_at d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hline hn hC hm hI hv
  have hgeo := hyp.exchanged_constituent_geometry hns hC hm P hPX hind hI hv
  have haxis := hyp.exchanged_constituent_not_le_axis hns hC hm P hPX hind hI hv hc.1
  have hr := ExchangedNondegenerate.recognized_data hyp hns hC hI hgeo haxis hnd
  exact ⟨hr,ExchangedNondegenerate.recognized_image_centerless hyp hns hC hI hnd hr,
    ExchangedNondegenerate.recognized_orbit_centerless hyp hns hC hI hnd hr⟩

namespace FixedLineReduction

theorem source_large_recognized_nondegenerate_remainder_of_mixed_size_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
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
        ∃ hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation
            (componentOrbit C ⊤) (F.terminalDot (F.X g)) I,
          v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry F.terminalRepresentation B v
            (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I ∧
          ExchangedGeometry.CompletedData F.terminalRepresentation B C
            (F.terminalDot (F.X g)) I hI ∧ (B.restrict I).Nondegenerate ∧
          ExchangedNondegenerate.RecognizedData F.terminalRepresentation B C
            (F.terminalDot (F.X g)) I hI ∧
          center (ExchangedNondegenerate.constituentLinearAction F.terminalRepresentation C
            (F.terminalDot (F.X g)) I hI).range = ⊥ ∧ center (componentOrbit C ⊤) = ⊥ := by
  obtain ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,C,hC,hm,horth,I,hI,hv,hgeo,hc,hnd⟩ :=
    source_large_nondegenerate_remainder_of_mixed_size_at d earlier hq chosen structural alternatives
      classification size F hne hZ hlarge g hg hgP hgH
  let := heU
  let := heX
  exact ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,C,hC,hm,horth,I,hI,hv,hgeo,hc,hnd,
    source_exchanged_nondegenerate_recognition_at d earlier hq chosen structural alternatives
      F hne hZ hlarge g hgP hgH hyp hline hn hC hm hI hv hnd⟩

end FixedLineReduction

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/ExchangedNondegenerateExclusion.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Tensor CoreGeometry

open LargerDimension.LocalAction.Components

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_exchanged_nondegenerate_impossible_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hS : ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)))
    {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit C ⊤)
      (F.terminalDot (F.X g)) I) (hv : v ∉ I) (hnd : (B.restrict I).Nondegenerate) : False := by
  let := chosen.elementary
  obtain ⟨P,hfix,hXP,hN⟩ := hS
  have hSX := (normal_subgroupOf_iff_le_normalizer hXP).mp hN
  have hns := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hind := Chapter14.Section03.NonabelianSource.Recognition.terminal_component_normalizer_index_le_two
    d.qtke F (by decide) C hC
  have hc := source_exchanged_completion_at d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hline hn hC hm hI hv
  have models := (source_exchanged_nondegenerate_recognition_at d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hline hn hC hm hI hv hnd).1
  have hker := source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ
  have htwo : IsPGroup 2 F.terminalHatAction.ker := hker ▸ pCore_isPGroup
  have hrank : primeRank 3 F.TerminalHdot ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ htwo).trans
      ((Chapter14.Section03.NonabelianSource.Recognition.pointNormalizer_sqtk
        d.qtke F (by decide)).stronglyQuasithin 3 Nat.prime_three (by decide))
  have hpoint : primeRank 3 (ChapterG.Section10.pointCentralizer F.terminalRepresentation v) ≤ 1 := by
    let J := F.terminalDot (centralizer (F.ZU : Set G))
    let Z := ChapterG.Section10.pointCentralizer F.terminalRepresentation v
    have hHc : F.H ≤ centralizer (F.ZU : Set G) := by
      rw [hZ]
      exact normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
    have hJ : J = ⊤ := by
      apply top_unique
      intro a _
      obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
      exact mem_map_of_mem _ (hHc b.property)
    have hu := CaseOneHS.source_center_centralizing_point_image_three_rank_le_one_at
      d earlier hq chosen structural alternatives F hne v hline.symm g hgP hgH
    change primeRank 3 (Z.subgroupOf J) ≤ 1 at hu
    have hZJ : Z ≤ J := by rw [hJ]; exact le_top
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe hZJ)] at hu
    exact hu
  let c := source_closure_geometry_at F d earlier hq chosen structural alternatives hne
  let q := Chapter14.Section03.NonabelianSource.Recognition.centerPointQuadraticForm F c (by decide) hZ
  have hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU := disjoint_iff.mpr
    (F.parabolic_displaced_centers (by decide) L chosen.normalizes c.seed_center g hgP hgH).1
  obtain ⟨hs,hi,hqn⟩ := Chapter14.Section03.NonabelianSource.Recognition.quadratic_intersection_of_center_point
    F c (by decide) hZ g hdis
  have hqpres : ∀ a u, q (F.terminalRepresentation a u) = q u := by
    intro a u
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact hi a u.toMul
  obtain ⟨x,_,_,_,_,i,hi0,_,hiW,_⟩ := hyp.exchanged_constituent_geometry
    hns hC hm P hSX hind hI hv
  have hqi : q (⟨i,i.property.1⟩ : I) = 0 := by
    apply hs
    have hh : (i : Additive F.Uhat) ∈ I ⊓ hatSpace F (F.E g) := by
      rw [hiW]
      exact Submodule.subset_span (Set.mem_singleton _)
    exact hh.2
  exact ExchangedKernel.nondegenerate_impossible hyp hns hC hm P hSX hind hI hv hc hnd
    (source_terminal_cover F d chosen) models hrank hpoint hfix q hqn hqpres
    ⟨i,i.property.1⟩ (fun hz => hi0 (congrArg Subtype.val hz)) hqi

theorem source_large_impossible_of_mixed_size_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) : False := by
  obtain ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,C,hC,hm,horth,I,hI,hv,hgeo,hc,hnd,models,hz,hzH⟩ :=
    FixedLineReduction.source_large_recognized_nondegenerate_remainder_of_mixed_size_at
      d earlier hq chosen structural alternatives classification size F hne hZ hlarge g hg hgP hgH
  let := heU
  let := heX
  exact source_exchanged_nondegenerate_impossible_at d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hline hS hn hC hm hI hv hnd

theorem source_large_exclusion_of_mixed_size_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U) : False := by
  obtain ⟨g,hg,hgP,hgH⟩ := exists_source_conjugator_at d earlier hq chosen structural F
  exact source_large_impossible_of_mixed_size_at d earlier hq chosen structural alternatives
    classification size F hne hZ hlarge g hg hgP hgH

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end
