module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitarySections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryLocalIdentification
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.EffectiveSections

/-!
# Original special and projective unitary effective sections

The original unitary identifications construct both the actual SU₃
surjection onto R_j and the faithful projective local marking. In the
projective original case the surjection includes the actual scalar
projection; in the special case it is the rank-one isomorphism itself.
The exact existing perfect-factor hypothesis proves n ≥ 2, so the
concrete unitary Frattini-detection and degree results apply.

For the literal radical, root geometry discharges nontriviality and
produces an effective section with at least 6n binary dimensions. Its
numerator is the reflected intersection of the original Sylow image;
the SourceQuotient theorem retains Q.q and the general marked theorem
also applies to the geometric universal completion. Normality remains
relative to the section numerator. The separate nonlinear (2B) input
is explicit, owned by split recognition.

Source: Fong–Seitz I (4D), (5D)–(5F), (6D), printed pp.21–22,26–28,41–43.
These are nonsolvable unitary effective-section inputs. They neither
exclude unitary local type nor dispose of the solvable parameters or
the exponent-six exception, which remain in the full hexagon family.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
  {n : ℕ} (hn : 0 < n) (hcard : Nat.card F = (2^n)^2)
  (hconj : ∀ x, J.conj x = x^(2^n))

include e h hn hcard hconj in
private theorem original_unitary_cover_inputs (j : Fin 2)
    (hp : Group.IsPerfect (L j))
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    2 ≤ n ∧ ∃ σ : J.specialSubgroup →* rankOne Q split j,
      Function.Surjective σ ∧ Nonempty (localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J) := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  rcases hmodel with hmodel | hmodel
  · obtain ⟨μ⟩ := hmodel
    let a := MarkedLocal.projectiveUnitaryRankOneEquiv Q e h split j hp T hT J hn hcard hconj μ
    refine ⟨MarkedLocal.projectiveUnitary_parameter_ge_two j hp J hn hcard hconj μ,
      a.symm.toMonoidHom.comp J.specialToProjective,
      a.symm.surjective.comp J.specialToProjective_surjective, ?_⟩
    exact ⟨MarkedLocal.projectiveUnitaryLocalEquiv Q e h split j hp T hT J hn hcard hconj μ hKj⟩
  · obtain ⟨μ⟩ := hmodel
    let a := MarkedLocal.specialUnitaryRankOneEquiv Q e h split j hp T hT J hn hcard hconj μ
    exact ⟨MarkedLocal.specialUnitary_parameter_ge_two j hp J hn hcard hconj μ,
      a.symm.toMonoidHom, a.symm.surjective,
      ⟨MarkedLocal.specialUnitaryLocalEquiv Q e h split j hp T hT J hn hcard hconj μ hKj⟩⟩

include e h hn hcard hconj in
/-- The nonsolvable unitary (5D) argument on any literal invariant section.
Both special and projective original models are allowed and their actual
local-model inputs are discharged by the existing identifications. -/
theorem effective_unitary_section_of_original_factor (j : Fin 2)
    (hp : Group.IsPerfect (L j))
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (d : RootSection Q split j) (hmove : d.action ≠ 1) :
    d.IsEffective ∧ 2^(6*n) ≤ Nat.card d.EffectiveCarrier := by
  obtain ⟨hlarge,σ,hσ,⟨μ⟩⟩ := original_unitary_cover_inputs Q e h split J hn hcard hconj j hp hmodel hKj
  exact ⟨unitary_section_effective Q split j J hlarge hcard hconj σ hσ hKj μ d hmove,
    unitary_section_card_bound Q split j J hlarge hcard hconj σ hσ d hmove⟩

include hn hcard hconj in
/-- The original/geometric radical is effective, with the actual binary
Frattini degree bound. Its nontrivial action is proved from root geometry. -/
theorem effective_unitary_radical_of_original_factor
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hp : Group.IsPerfect (L j))
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    ∃ d : RootSection Q split j,
      d.numerator = (MarkedLocal.sylowMap Q e h).range ⊓
        rightConjugate (MarkedLocal.sylowMap Q e h).range
          ((UnitarySource.actorReflection Q split j).val : X ⧸ Q.D) ∧
      d.denominator = ⊥ ∧ d.IsEffective ∧
      2^(6*n) ≤ Nat.card (d.numerator ⧸ frattini d.numerator) := by
  obtain ⟨hlarge,σ,hσ,⟨μ⟩⟩ := original_unitary_cover_inputs Q e h split J hn hcard hconj j hp hmodel hKj
  let s := UnitarySource.actorReflection Q split j
  let d := radicalSection Q split j hKj
  obtain ⟨heff,hbound⟩ := unitary_radical_effective_and_card_bound Q split j J hlarge hcard hconj
    σ hσ hm i hij s hKj μ
  exact ⟨d, marked_radical_eq h Q e split j s.val s.class_eq, rfl, heff, hbound⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The unitary effective section under the literal original quotient Q.q. -/
theorem quotient_effective_unitary_radical_of_original_factor
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hp : Group.IsPerfect (L j))
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    ∃ d : RootSection Q split j,
      d.numerator = ((S.subgroupOf (generated L S)).map Q.q) ⊓
        rightConjugate ((S.subgroupOf (generated L S)).map Q.q)
          ((UnitarySource.actorReflection Q split j).val : (generated L S) ⧸ Q.D) ∧
      d.denominator = ⊥ ∧ d.IsEffective ∧
      2^(6*n) ≤ Nat.card (d.numerator ⧸ frattini d.numerator) := by
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  have hh := effective_unitary_radical_of_original_factor Q (originalMarkedIso Q) h split
    J hn hcard hconj hm i j hij hp hmodel hKj
  rwa [MarkedLocal.sylow_range Q (originalMarkedIso Q) h split] at hh
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
