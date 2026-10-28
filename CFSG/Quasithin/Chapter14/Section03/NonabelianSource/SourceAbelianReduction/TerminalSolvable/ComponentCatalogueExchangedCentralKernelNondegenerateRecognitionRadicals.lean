module
public import CFSG.Quasithin.ChapterG.Section12.RecognitionRadicals
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerateSymplecticComplete

/-!
# Faithful point radicals in the original exchanged constituent

Apply the proved nonfaithful-radical branch of G.12.1 to the literal HY action
on the selected constituent. Its full-symplectic conclusion contradicts the
completed source exclusion, since HY's embedded solvable residual is exactly
the original H-image. Thus the original G.12 input pair has faithful point
radicals on both perpendicular hyperplanes, without a new premise.

This discharges G.12.5's branch in the central-kernel source. The remaining
faithful-radical recognition and orthogonal exclusion stay with
`qt-e-14315-exchanged-central-kernel`; final exchanged-image assembly stays
with `qt-e-14315-component-exchanged-images`.

Source: Aschbacher--Smith G.10.15, p.363, and G.12.1--5, pp.370--371,
in the original 14.3.12--15 source configuration.
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

/-- The actual radical restriction is faithful: its only element fixing
all vectors of the perpendicular hyperplane is the identity. -/
theorem nondegenerate_pointRadical_faithful
    (hnd : (B.restrict I).Nondegenerate) {u i : I}
    (h : ChapterG.Section12.ClassificationHypotheses
      s.constituentGeneratedImage (B.restrict I) u i)
    {a : I ≃ₗ[ZMod 2] I}
    (ha : a ∈ ChapterG.Section12.pointRadical
      s.constituentGeneratedImage (B.restrict I) i)
    (hf : ∀ w : I, (B.restrict I) i w = 0 → a w = w) : a = 1 := by
  by_contra hn
  have he := h.eq_formStabilizer_of_radical_kernel ⟨a,ha,hn,hf⟩
  apply s.false_of_symplectic hnd
  rw [← he,s.constituentGeneratedImage_residual]

/-- The original G.12 input pair lies in the remaining faithful-radical
branch at both of its nonorthogonal centers. -/
theorem nondegenerate_classification_inputs_faithful
    (hnd : (B.restrict I).Nondegenerate) :
    ∃ u i : I, ChapterG.Section12.ClassificationHypotheses
      s.constituentGeneratedImage (B.restrict I) u i ∧
      ∀ j ∈ ({u,i} : Set I), ∀ a ∈ ChapterG.Section12.pointRadical
        s.constituentGeneratedImage (B.restrict I) j,
        (∀ w : I, (B.restrict I) j w = 0 → a w = w) → a = 1 := by
  obtain ⟨u,i,h⟩ := s.nondegenerate_classification_inputs s.not_fullLinear hnd
  refine ⟨u,i,h,?_⟩
  intro j hj a ha hf
  have hj' : j = u ∨ j = i := by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hj
  rcases hj' with hj | hj
  · subst j
    have h' : ChapterG.Section12.ClassificationHypotheses
        s.constituentGeneratedImage (B.restrict I) i u :=
      ⟨h.alternating,h.nondegenerate,h.preserves,h.dimension,h.good_v,h.good_u,
        fun hz => h.pairing (h.alternating.eq_iff.mpr hz)⟩
    exact s.nondegenerate_pointRadical_faithful hnd h' ha hf
  · subst j
    exact s.nondegenerate_pointRadical_faithful hnd h ha hf

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
