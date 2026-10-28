module
public import CFSG.Quasithin.ChapterG.Section12.RecognitionQuadraticRadicals
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerateRecognitionOrbits
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerateOrthogonalFourComplete

/-!
# The quadratic branch on the literal selected constituent

For a nontransitive original center orbit, the G.12 orbit construction gives
an invariant quadratic form with the original restricted polar form. At every
nonzero singular point the source point radical equals the full orthogonal
point radical, as subgroups of the same linear group.

In degree four the new invariant form is already impossible: containment
of the original perfect image in either orthogonal sign contradicts the
source actor bounds. Thus the only remaining degree-four recognition case
is transitive. In higher dimensions orthogonal generation, the transitive
recognition alternatives and the remaining model exclusions are retained
by `qt-e-14315-exchanged-central-kernel`. Final exchanged-image assembly
remains with `qt-e-14315-component-exchanged-images`.

Source: Aschbacher--Smith G.12.6, G.12.10 and G.12.1, pp.371, 373--374,
used in the original G.10.15 central-kernel branch, p.363.
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

/-- The nontransitive source branch constructs an actual quadratic form and
identifies every nonzero singular point radical with its literal orthogonal one. -/
theorem nondegenerate_quadratic_of_not_transitive
    (hnd : (B.restrict I).Nondegenerate) {u i : I}
    (h : ChapterG.Section12.ClassificationHypotheses
      s.constituentGeneratedImage (B.restrict I) u i)
    (hnt : ¬∀ x : I, x ≠ 0 → ∃ a ∈ s.constituentGeneratedImage, a i = x) :
    ∃ q : QuadraticForm (ZMod 2) I, q.polarBilin = B.restrict I ∧
      s.constituentGeneratedImage ≤ q.isometrySubgroup ∧
      (∀ x : I, q x = 0 ↔ x = 0 ∨ ∃ a ∈ s.constituentGeneratedImage, a i = x) ∧
      ∀ x : I, x ≠ 0 → q x = 0 →
        ChapterG.Section12.pointRadical s.constituentGeneratedImage (B.restrict I) x =
          ChapterG.Section12.pointRadical q.isometrySubgroup (B.restrict I) x := by
  obtain ⟨q,hq,hD,hs⟩ := h.good_v.exists_quadratic_of_not_transitive
    hnd h.preserves h.irreducible hnt
  refine ⟨q,hq,hD,hs,?_⟩
  intro x hx0 hxq
  obtain ⟨a,ha,hax⟩ := ((hs x).mp hxq).resolve_left hx0
  have hx := h.good_v.conjugate h.preserves ha
  rw [hax] at hx
  exact hx.pointRadical_eq_orthogonal hnd q hq hD hxq (by have := h.dimension; omega)

/-- In dimension four the actual generated action must be transitive on
nonzero vectors. The nontransitive quadratic branch is excluded intrinsically. -/
theorem nondegenerate_transitive_of_dimension_four
    (hnd : (B.restrict I).Nondegenerate) {u i : I}
    (h : ChapterG.Section12.ClassificationHypotheses
      s.constituentGeneratedImage (B.restrict I) u i)
    (hd : finrank (ZMod 2) I = 4) :
    ∀ x : I, x ≠ 0 → ∃ a ∈ s.constituentGeneratedImage, a i = x := by
  by_contra hnt
  obtain ⟨q,hq,hD,_,_⟩ := s.nondegenerate_quadratic_of_not_transitive hnd h hnt
  exact s.false_of_preserves_quadratic_four hnd q hq (le_sup_left.trans hD) hd

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
