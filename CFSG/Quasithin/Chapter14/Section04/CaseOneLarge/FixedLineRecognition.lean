module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CatalogueExclusion
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSubgroups

/-!
# The original flag with recognized coefficient image

Apply the coefficient subgroup theorem to the same terminal action and
marked flag as the projective reduction. The resulting coefficient
isomorphisms agree with the literal projective map. The original component,
centralizer, field map, whole-action coordinates, actor and exchanged
constituent geometry are all retained.

This removes the coefficient-subgroup classification step. The two module
identifications, unmarked exchanged recognition and guarded earlier-source
assembly remain obligations; this theorem does not assert the full 14.4.2
catalogue or the large-case contradiction. MixedSizeInput is the same
independent tensor premise as in the preceding reduction.
Source: Aschbacher--Smith G.11.8 and 14.4.2, printed pp.368--369,1006--1007;
refs/quasithin.pdf.
-/

public noncomputable section
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

/-- The surviving coefficient cases with actual isomorphisms and the original
projective map, retaining all preceding original-flag restrictions. -/
@[expose] def ClassifiedRemainder {D W : Type*} [Group D] [Finite D]
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
          (∀ P : Sylow 5 (Equiv.Perm (Fin 5)),
            ¬ a.coefficientFive.range ≤ normalizer ((P : Subgroup (Equiv.Perm (Fin 5))) : Set _)) ∧
          ((∃ e : a.coefficient.range ≃* Equiv.Perm (Fin 5),
              ∀ b, e b = a.coefficientFive b) ∨
            (∃ t : Equiv.Perm (Fin 5), t.IsSwap ∧
              ∃ e : a.coefficient.range ≃* centralizer ({t} : Set (Equiv.Perm (Fin 5))),
                ∀ b, (e b).val = a.coefficientFive b))) ∨
      (v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry ρ B v E X I))

/-- Construct the coefficient image recognition on the original flag.
Every earlier-source and mixed-size premise is retained literally. -/
theorem source_large_classified_remainder_of_mixed_size (d : Counterexample T L)
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
      ClassifiedRemainder F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g)) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,hrem⟩ :=
    source_large_projective_remainder_of_mixed_size d earlier hq chosen structural alternatives
      classification size F hne hZ hlarge g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,?_⟩
  obtain ⟨C,hC,hm,horth,I,hI,ha | hx⟩ := hrem
  · obtain ⟨hv,hCn,hI4,hV8,hX8,hY,a,hfield,hcore,hindex,hgen,hinj,heven,hfour,hfive⟩ := ha
    have hf := (source_terminal_ranks_of_no_lowRank d earlier hq chosen structural alternatives
      F hne hZ g hgP hgH v hline hn).1
    rw [←hline] at hf
    exact ⟨C,hC,hm,horth,I,hI,Or.inl ⟨hv,hCn,hI4,hV8,hX8,hY,a,
      hfield,hcore,hindex,hgen,hinj,heven,hfour,hfive,
      a.coefficientFive_models B hyp.nondegenerate hyp.preserves hyp.twoCore_eq_bot
        _ v hyp.point_ne_zero hf hY⟩⟩
  · exact ⟨C,hC,hm,horth,I,hI,Or.inr hx⟩

end FixedLineReduction
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
