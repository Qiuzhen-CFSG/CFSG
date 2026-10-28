module

public import CFSG.Quasithin.ChapterG.Section06
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.Displacement

/-!
# G.6.2 on the actual displacement action used in 13.8.5

The Chapter 13 construction uses an explicitly spanned orbit of differences.
It is exactly the source displacement span. Consequently both K and O²(K)
generate the original module by commutators, as required in the G.6.4
classification argument. No recognition or splitting premise is used here.

Source: Aschbacher–Smith G.6.2, printed p.345, applied in 13.8.5, p.947.
-/

public section
namespace CFSG.Quasithin.ChapterG.Section06
open Subgroup Representation.BinaryOffender
open Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (a : G)

/-- Identify the literal Chapter 13 orbit span with the source construction. -/
theorem chapter13_displacementOrbit_eq :
    displacementOrbit ρ a = conjugateDisplacementSpan ρ a ⊤ := by
  unfold displacementOrbit conjugateDisplacementSpan
  congr 1
  ext w
  constructor
  · rintro ⟨g, v, he⟩
    exact ⟨g, Subgroup.mem_top _, v, he⟩
  · rintro ⟨g, _, v, he⟩
    exact ⟨g, v, he⟩

/-- G.6.2(1),(2) supply full generation on the actual action in 13.8.5. -/
theorem chapter13_full_commutators [Finite G] [FiniteDimensional (ZMod 2) V]
    (hgen : displacementOrbit ρ a = ⊤) :
    subspaceCommutator ρ ⊤ (normalClosure ({a} : Set G)) = ⊤ ∧
    subspaceCommutator ρ ⊤
      ((pResidual 2 (normalClosure ({a} : Set G))).map
        (normalClosure ({a} : Set G)).subtype) = ⊤ := by
  rw [chapter13_displacementOrbit_eq] at hgen
  exact ⟨lemma_G_6_2_1 ρ a hgen, lemma_G_6_2_2 ρ a hgen⟩
end CFSG.Quasithin.ChapterG.Section06
