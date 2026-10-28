module
public import Theory.SpecificGroups.AlternatingSix.PerfectSubgroups
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerateRecognitionResidual

/-!
# Exclusion of the degree-four nondegenerate constituent

The selected constituent image is a nontrivial perfect subgroup of its full
symplectic group. The actual degree-four symplectic action identifies that
ambient group with S₆. Perfect-subgroup recognition gives either its literal
A₆ residual or an actual A₅. The previously proved source actor obstructions
exclude both, leaving the original isotropic, faithful constituent data.

Source: Aschbacher--Smith G.10.15(3), printed p.363. This proves the complete
degree-four branch. Higher degrees remain with
`qt-e-14315-exchanged-central-kernel`; final exchanged-image assembly remains
with `qt-e-14315-component-exchanged-images`.
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

/-- No nondegenerate degree-four constituent occurs in the original source.
The perfect image is either the literal symplectic residual or an actual A₅. -/
theorem not_nondegenerate_four
    (hd : finrank (ZMod 2) I=4) : ¬(B.restrict I).Nondegenerate := by
  intro hnd
  obtain ⟨f⟩ := Matrix.PSp4Three.exists_isometry 2 (B.restrict I)
    (fun w => s.hypothesis.alternating w) hnd hd
  let e : ChapterG.Section12.formStabilizer (B.restrict I) ≃* Equiv.Perm (Fin 6) :=
    (ChapterG.Section12.formStabilizerEquivSp (B.restrict I) f).trans
      Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  let : Group.IsPerfect s.constituentLinearAction.range := s.constituentImage_perfect
  have hle : s.constituentLinearAction.range≤ChapterG.Section12.formStabilizer (B.restrict I) :=
    (show s.constituentLinearAction.range≤s.constituentGeneratedImage from le_sup_left).trans
      s.constituentGeneratedImage_preserves
  rcases AlternatingSix.PerfectSubgroups.in_symmetric_six
    s.constituentLinearAction.range (ChapterG.Section12.formStabilizer (B.restrict I))
    e s.constituentImage_ne_bot hle with heq|he
  · exact s.false_of_symplectic_four s.not_fullLinear hnd heq hd
  · obtain ⟨a⟩ := he
    exact s.false_of_constituentImage_alternatingFive s.not_fullLinear hd.ge a

/-- The source isotropic/nondegenerate dichotomy leaves only isotropy in
four dimensions. This is the literal selected constituent's conclusion. -/
theorem isotropic_four (hd : finrank (ZMod 2) I=4) :
    ∀ u∈I,∀ w∈I,B u w=0 :=
  s.form_cases.resolve_right (s.not_nondegenerate_four hd)

/-- The complete faithful constituent data in degree four, with the exact
original constituent witness and action. -/
theorem faithful_data_four (hd : finrank (ZMod 2) I=4) :
    ExchangedFaithfulConstituentData F.terminalRepresentation B L
      (F.terminalDot (F.X g)) I s.selected :=
  s.faithful_data_of_not_nondegenerate (s.not_nondegenerate_four hd)

/-- After the complete degree-four exclusion and the nontransitive residual
recognition, the original consumer retains only higher-degree transitive
recognition and higher-degree orthogonal exclusion. Both are source obligations
of this same owner, not hypotheses discharged by this theorem. -/
theorem faithful_data_of_higher_transitive_orthogonal
    (htransitive : 6 ≤ finrank (ZMod 2) I →
      ∀ u i : I, ChapterG.Section12.ClassificationHypotheses
        s.constituentGeneratedImage (B.restrict I) u i →
        (∀ x : I,x≠0 → ∃ a∈s.constituentGeneratedImage,a i=x) →
        ChapterG.Section12.ResidualModel
          (ChapterG.Section12.embeddedResidual s.constituentGeneratedImage) (B.restrict I))
    (horthogonal : (B.restrict I).Nondegenerate →
      6 ≤ finrank (ZMod 2) I →
      ∀ q : QuadraticForm (ZMod 2) I,q.polarBilin=B.restrict I →
        s.constituentLinearAction.range=ChapterG.Section12.embeddedResidual
          q.isometrySubgroup → False) :
    ExchangedFaithfulConstituentData F.terminalRepresentation B L
      (F.terminalDot (F.X g)) I s.selected := by
  by_cases hd : finrank (ZMod 2) I=4
  · exact s.faithful_data_four hd
  apply s.faithful_data_of_transitive_recognition_orthogonal _ horthogonal
  intro u i h ht
  obtain ⟨n,hn⟩ := AlternatingForm.even_finrank (B.restrict I)
    h.alternating h.nondegenerate
  exact htransitive (by have := h.dimension; omega) u i h ht

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
