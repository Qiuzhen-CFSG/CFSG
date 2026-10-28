module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourMinus
public import Theory.LinearAlgebra.QuadraticForm.BinaryAnisotropic
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerateOrthogonalFour
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerateSymplecticComplete

/-!
# Excluding every four-dimensional orthogonal exchanged constituent

Irreducibility makes the singular vectors span the literal selected constituent:
the zero set is invariant and the binary anisotropic dimension bound rules out
its trivial span. A singular plane gives the already excluded solvable plus
model. Otherwise singular coordinates embed the perfect nontrivial H-image
in S5 and identify it with A5. The original elementary actor is too large
for Aut(A5), by the previously proved source actor bound.

The stronger exclusion only needs containment in the orthogonal group.
The final adapter removes degree four from the remaining orthogonal premise
of the actual exchanged-constituent assembly. Faithful-radical G.12 recognition
and orthogonal degrees at least six remain with
`qt-e-14315-exchanged-central-kernel`; final exchanged-image assembly remains
with `qt-e-14315-component-exchanged-images`.

Source: Aschbacher--Smith G.10.15, p.363, G.12.1(2), p.370, and the original
14.3.12--15 small-actor configuration, pp.993--994.
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

private theorem orthogonal_singular_span
    (q : QuadraticForm (ZMod 2) I)
    (hK : s.constituentLinearAction.range ≤ q.isometrySubgroup) :
    Submodule.span (ZMod 2) {x : I | q x=0}=⊤ := by
  have hinv : ∀ a∈s.constituentLinearAction.range,
      ∀ x∈Submodule.span (ZMod 2) {x : I | q x=0},
        a x ∈ Submodule.span (ZMod 2) {x : I | q x=0} := by
    intro a ha x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (((QuadraticMap.mem_isometrySubgroup q a).mp (hK ha) x).trans hx)
    | zero => simp
    | add x y hx hy hax hay => simpa using Submodule.add_mem _ hax hay
    | smul c x hx hax => simpa using Submodule.smul_mem _ c hax
  rcases s.constituentImage_irreducible _ hinv with hzero|htop
  · have haniso : q.Anisotropic := fun x hx =>
      by
        have hm : x ∈ Submodule.span (ZMod 2) {x : I | q x=0} := Submodule.subset_span hx
        rw [hzero] at hm
        exact hm
    have hb := q.finrank_le_twice_of_anisotropic_binary haniso
    have hd := s.dimension_gt_two
    simp only [Module.finrank_self,mul_one] at hb
    omega
  · exact htop

/-- In degree four even containment in an orthogonal group is impossible
for the original perfect constituent image. No residual recognition is needed. -/
theorem false_of_preserves_quadratic_four
    (hnd : (B.restrict I).Nondegenerate)
    (q : QuadraticForm (ZMod 2) I) (hq : q.polarBilin = B.restrict I)
    (hK : s.constituentLinearAction.range ≤ q.isometrySubgroup)
    (hd : finrank (ZMod 2) I = 4) : False := by
  let : Group.IsPerfect s.constituentLinearAction.range := s.constituentImage_perfect
  by_cases hp : ∃ U : Submodule (ZMod 2) I, finrank (ZMod 2) U = 2 ∧ ∀ x ∈ U, q x = 0
  · obtain ⟨U,hU,hUs⟩ := hp
    have hle := Subgroup.le_map_solvableResidual_of_isPerfect
      s.constituentLinearAction.range q.isometrySubgroup hK
    rw [QuadraticForm.BinaryFour.residual_eq_bot_of_singular_plane q
      (hq.symm ▸ hnd) hd U hU hUs] at hle
    exact s.constituentImage_ne_bot (le_bot_iff.mp hle)
  · obtain ⟨e⟩ := QuadraticForm.BinaryFour.perfect_subgroup_equiv_alternatingFive
      q hd (s.orthogonal_singular_span q hK) hp s.constituentLinearAction.range
      s.constituentImage_ne_bot hK
    exact s.false_of_constituentImage_alternatingFive s.not_fullLinear hd.ge e

/-- Both orthogonal signs in degree four contradict the original source.
The image remains the literal embedded solvable residual throughout. -/
theorem false_of_orthogonal_four
    (hnd : (B.restrict I).Nondegenerate)
    (q : QuadraticForm (ZMod 2) I) (hq : q.polarBilin = B.restrict I)
    (heq : s.constituentLinearAction.range =
      ChapterG.Section12.embeddedResidual q.isometrySubgroup)
    (hd : finrank (ZMod 2) I = 4) : False := by
  apply s.false_of_preserves_quadratic_four hnd q hq _ hd
  rw [heq]
  rintro _ ⟨a,ha,rfl⟩
  exact a.property

/-- The literal faithful-constituent assembly now needs the orthogonal exclusion
only in degrees at least six. The remaining premises retain this source owner. -/
theorem faithful_data_of_recognition_orthogonal_ge_six
    (hrecognition : ∀ u i : I, ChapterG.Section12.ClassificationHypotheses
      s.constituentGeneratedImage (B.restrict I) u i →
      ChapterG.Section12.ResidualModel
        (ChapterG.Section12.embeddedResidual s.constituentGeneratedImage) (B.restrict I))
    (horthogonal : (B.restrict I).Nondegenerate →
      6 ≤ finrank (ZMod 2) I →
      ∀ q : QuadraticForm (ZMod 2) I, q.polarBilin = B.restrict I →
        s.constituentLinearAction.range = ChapterG.Section12.embeddedResidual
          q.isometrySubgroup → False) :
    ExchangedFaithfulConstituentData F.terminalRepresentation B L
      (F.terminalDot (F.X g)) I s.selected := by
  apply s.faithful_data_of_recognition_orthogonal hrecognition
  intro hnd q hq heq
  by_cases hd : finrank (ZMod 2) I=4
  · exact s.false_of_orthogonal_four hnd q hq heq hd
  · obtain ⟨n,hn⟩ := AlternatingForm.even_finrank (B.restrict I)
      (fun w => s.hypothesis.alternating w) hnd
    have hdim := s.dimension_gt_two
    exact horthogonal hnd (by omega) q hq heq

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
