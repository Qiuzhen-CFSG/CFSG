module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleSource.AlternatingSix
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleSource.Hexacode
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleSource.G2
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleSource.Symplectic
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.AlternatingSeven.Source
/-!
# Genuine quasisimple natural-factor recognition for B.6.9

Apply every original B.4.2 action row to the same faithful irreducible
B.5.1 moved central quotient. Actual invariant-parabolic and six-letter
image arguments exclude the higher-rank, alternating and triple-cover rows.
Only natural SL2 and the marked symmetric-five action remain. In particular
no module recognition or invariant-parabolic conclusion is an extra premise.

Source: Aschbacher–Smith B.6.9 and E.2.3, printed pp.115–116 and 216–217.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
/-- The original quasisimple source central quotient has only its natural rank-one rows. -/
theorem source_offender_quasisimple_rank_one
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hff : IsFFModule ρ) (hcore : pCore 2 G = ⊥)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ))) :
    (∃ F : BinaryField, IsLinearNatural
      (c.sectionData.action.comp (generalizedFitting (offenderSubgroup ρ)).subtype) F 2) ∨
    Nonempty (MarkedActionEquiv c.sectionData.action (offenderSubgroup c.sectionData.action)
      (generalizedFitting (offenderSubgroup ρ)) (BinaryPermutation.naturalRepresentation (Fin 5))
      (alternatingGroup (Fin 5))) := by
  have hi := source_offender_quasisimple_irreducible ρ T hP hff hcore hq c
  have h3 := source_offender_quasisimple_three_exclusions ρ T hP hff hcore hq c
  have hb := source_offender_quasisimple_binary_rows_excluded ρ T hP hff hcore hq c
  have hsp := source_offender_quasisimple_symplectic_exclusion ρ T hP hff hcore hq c
  have hg := source_offender_quasisimple_g2_exclusions ρ T hP hff hcore hq c
  have h6 := source_offender_quasisimple_six_exclusions ρ T hP hff hcore hq c
  have h7 := source_offender_quasisimple_alternatingSeven_rows_excluded ρ T hP hff hcore hq c
  have hhex := source_offender_quasisimple_tripleSix_excluded ρ T hP hff hcore hq c
  have h8 (e : generalizedFitting (offenderSubgroup ρ) ≃* alternatingGroup (Fin 8)) : False := by
    apply source_offender_quasisimple_not_binary_linear ρ T hP hff hcore hq (Or.inl rfl)
    exact ⟨e.trans (Atlas.Order20160A8.sl4TwoEquivPSL.trans
      Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8).symm⟩
  cases hi.2.2.2 with
  | linearTwo F hgen e ho hr => exact Or.inl ⟨F,⟨e⟩⟩
  | linearThree F hgen e hr => exact (h3.1 F ⟨e⟩).elim
  | symplectic F hF hgen e hr => exact (hsp F hF ⟨e⟩).elim
  | symplecticTwo e hr => exact (h6.2 ⟨e⟩).elim
  | g2 F hF hgen e ho hr => exact (hg.1 F ⟨e⟩).elim
  | g2Two e ho hr => exact (hg.2 ⟨e⟩).elim
  | symmetric n hn e ho hr =>
    rcases hn with rfl | rfl
    · exact Or.inr ⟨e⟩
    · exact (h7.1 ⟨e⟩).elim
  | alternatingSix hgen e ho hr => exact (h6.1 ⟨e⟩).elim
  | alternatingSeven hgen hw e hd ho hr => exact (h7.2 ⟨e⟩).elim
  | tripleSix hgen a hr => exact (hhex ⟨a⟩).elim
  | binaryLinear d hd hgen e hr => exact (hb.1 d hd ⟨e⟩).elim
  | orthogonalSix hgen hw e ho hr => exact (h8 e.groupEquiv).elim
  | symmetricEight hw e hr => exact (h8 e.subgroupEquiv).elim
  | exteriorFive hgen hw e hd ho hr => exact (hb.2.2.2 ⟨e⟩).elim
end CFSG.Quasithin.ChapterB
