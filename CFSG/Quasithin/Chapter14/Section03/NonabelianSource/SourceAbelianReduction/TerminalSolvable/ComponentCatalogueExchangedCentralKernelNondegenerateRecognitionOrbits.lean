module
public import CFSG.Quasithin.ChapterG.Section12.RecognitionOrbits
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerateRecognitionRadicals

/-!
# The two regular radical orbits on the selected constituent

The original G.12 pair already has faithful radical restrictions. Apply the
proved orbit coordinates to each of its two literal point radicals, obtaining
both their exact order and the two regular outside orbits. This supplies
G.12.2(2i) and G.12.6(1) in the actual HY-action, with no extra local hypothesis.

Faithful-radical recognition and the remaining orthogonal exclusions stay
with `qt-e-14315-exchanged-central-kernel`; final exchanged-image assembly
stays with `qt-e-14315-component-exchanged-images`.
Source: Aschbacher--Smith G.12.2 and G.12.6, pp.370--371, used in G.10.15,
p.363, in the original 14.3.12--15 configuration.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
namespace ExchangedCentralSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedCentralSource T M Mc F g B v L I)

include s

/-- Both original point radicals have the exact source order and unique
coordinates on the complement of their perpendicular hyperplane. -/
theorem nondegenerate_classification_inputs_radical_orbits
    (hnd : (B.restrict I).Nondegenerate) :
    ∃ u i : I, ChapterG.Section12.ClassificationHypotheses
      s.constituentGeneratedImage (B.restrict I) u i ∧
      ∀ j ∈ ({u,i} : Set I),
        IsElementaryAbelian 2 (ChapterG.Section12.pointRadical
          s.constituentGeneratedImage (B.restrict I) j) ∧
        Nat.card (ChapterG.Section12.pointRadical
          s.constituentGeneratedImage (B.restrict I) j) =
            2 ^ (finrank (ZMod 2) I-2) ∧
        ∀ x y : I, (B.restrict I) j x=1 → (B.restrict I) j y=1 →
          ∃! p : ChapterG.Section12.pointRadical
            s.constituentGeneratedImage (B.restrict I) j × ZMod 2,
            p.1.val (x+p.2 • j)=y := by
  obtain ⟨u,i,h,hf⟩ := s.nondegenerate_classification_inputs_faithful hnd
  refine ⟨u,i,h,?_⟩
  intro j hj
  have hg : ChapterG.Section12.GoodVector s.constituentGeneratedImage
      (B.restrict I) h.alternating j := by
    have hh : j=u ∨ j=i := by
      simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hj
    rcases hh with rfl|rfl
    · exact h.good_u
    · exact h.good_v
  have hn : (B.restrict I) j ≠ 0 := by
    intro hz
    exact hg.nonzero (hnd.1 j (fun w => LinearMap.congr_fun hz w))
  obtain ⟨x,hx⟩ := Module.Dual.range_eq_top_of_ne_zero hn ▸
    (show (1 : ZMod 2) ∈ (⊤ : Submodule (ZMod 2) (ZMod 2)) from trivial)
  refine ⟨hg.elementary_pointRadical_of_faithful (hf j hj),
    hg.card_pointRadical_of_faithful hnd h.preserves (hf j hj)
    (by have := h.dimension; omega) hx,?_⟩
  intro x y hx hy
  exact hg.radical_pair_exists_unique hnd h.preserves (hf j hj) hx hy

/-- The original center orbit has the G.12.6(3) dichotomy, and its
hyperplane vectors satisfy G.12.6(2), on the same generated action image. -/
theorem nondegenerate_pointRadical_orbit_geometry
    (hnd : (B.restrict I).Nondegenerate) {u i : I}
    (h : ChapterG.Section12.ClassificationHypotheses
      s.constituentGeneratedImage (B.restrict I) u i) :
    (∀ w : I, (B.restrict I) i w=0 →
      w∉Submodule.span (ZMod 2) {i} →
      ((∃ a∈s.constituentGeneratedImage,a i=w) ↔
        ∃ a∈s.constituentGeneratedImage,a i=w+i)) ∧
    ∀ x : I, (B.restrict I) i x=1 →
      (∀ y : I,y≠0 → ∃ a∈s.constituentGeneratedImage,a i=y) ∨
      ((∃ a∈s.constituentGeneratedImage,a i=x) ↔
        ¬∃ a∈s.constituentGeneratedImage,a i=x+i) := by
  refine ⟨fun w hw hn => h.good_v.orbit_iff_add_center hw hn,?_⟩
  intro x hx
  exact h.good_v.outside_orbit_dichotomy hnd h.preserves h.irreducible hx

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
