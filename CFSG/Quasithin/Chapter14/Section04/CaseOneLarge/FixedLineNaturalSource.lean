module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineNaturalTensor
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineOrthogonal

/-!
# Excluding the natural tensor on the original large flag

The explicit tensor coordinates are transported through the literal equality
between the terminal action kernel and O₂(H). They supply the natural tensor
row of the marked action catalogue, so the existing tensor exclusion applies
to the original flag. This exhausts the transposition-centralizer branch.

The conclusion retains the original component, its proper constituent,
component exchange, point-stabilizer geometry and both fixed-point alternatives.
Only the unmarked exchanged constituent remains. The independent mixed-size
premise and all preceding source inputs are retained; this is not yet the
complete large-case theorem or its guarded earlier-source assembly.

Source: Aschbacher--Smith, G.11.8 and 14.4.2(5), printed pp.368--369,1006;
refs/quasithin.pdf.
-/

public noncomputable section
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

/-- Transport the recognized natural tensor through the literal quotient by
the terminal action kernel, retaining the source conjugation action. -/
theorem source_natural_tensor_catalogue (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
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
      (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)) := by
  let := chosen.elementary
  let := F.U_normal
  let hk := source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ
  obtain ⟨σ,hσ,actor,space,hspace⟩ := a.natural_tensor_coordinates t ht e he
  let q := QuotientGroup.quotientMulEquivOfEq hk.symm
  exact .tensor ⊤ le_top σ (Or.inl rfl) (Or.inl hσ) (q.trans actor) space
    (fun g w => hspace (q g) w)

namespace FixedLineReduction

/-- The marked-point fixed-line branch is now exhausted and excluded by the
actual natural tensor action. Only the original unmarked exchanged constituent
remains. The independent mixed-size premise and all earlier inputs are retained. -/
theorem source_large_exchanged_remainder_of_mixed_size (d : Counterexample T L)
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
      ∃ C : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot C ∧
        ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
        ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B C ∧
        ∃ I : Submodule (ZMod 2) (Additive F.Uhat),
          Representation.BinaryOffender.Homogeneous.IsIrrPlusWith F.terminalRepresentation
            (componentOrbit C ⊤) (F.terminalDot (F.X g)) I ∧
          v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry F.terminalRepresentation B v
            (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I := by
  obtain ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,hrem⟩ :=
    source_large_transposition_remainder_of_mixed_size d earlier hq chosen structural alternatives
      classification size F hne hZ hlarge g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,?_⟩
  obtain ⟨C,hC,hm,horth,I,hI,ha | hx⟩ := hrem
  · obtain ⟨_,_,_,_,_,_,a,_,_,_,_,_,_,_,_,t,ht,e,he⟩ := ha
    exact (source_large_exclusion_of_marked_action_of_mixed_size d earlier hq chosen
      structural alternatives classification size F hne hZ hlarge
      (source_natural_tensor_catalogue d earlier hq chosen structural alternatives F hne hZ a t ht e he)).elim
  · exact ⟨C,hC,hm,horth,I,hI,hx⟩

end FixedLineReduction
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
