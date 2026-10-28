module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.PerpendicularSupport
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalDerivedRadical

/-!
# Perpendicular support in the original derived core

The actual original two-core equivalence identifies its derived image with
the derived radical on the same marked quotient. The source intersection
dichotomy therefore applies to that image, preserving both endpoint orders.
The final specialization uses literally Q.q composed with the parabolic
inclusion and core subtype. The whole-root alternative is still explicit.

Source: Fong--Seitz I (1973), p.53, the perpendicular-root support argument
in the positive-parameter part of (6H)(b).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits) (i j : Fin 2)
  (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

include e μ hB in
/-- Either original endpoint has the same two possible perpendicular intersections. -/
theorem original_positive_perpendicular_derived_dichotomy
    (hmpos : 0 < m) (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    let D := (commutator (pCore 2 (parabolic L S i))).map
      ((endpointMap Q e i).comp (pCore 2 (parabolic L S i)).subtype)
    let E := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
    D ⊓ E = omegaOneAmbient E ∨ D ⊓ E = E := by
  let hV := marked_suzuki_remainder_le_kernel Q split i m μ hB
  have he : (commutator (pCore 2 (parabolic L S i))).map
      ((endpointMap Q e i).comp (pCore 2 (parabolic L S i)).subtype) =
      (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) := by
    apply le_antisymm
    · rintro x ⟨v,hv,rfl⟩
      exact (originalDerivedRadicalEquiv Q e split i hV ⟨v,hv⟩).property
    · intro x hx
      obtain ⟨v,hv⟩ := (originalDerivedRadicalEquiv Q e split i hV).surjective ⟨x,hx⟩
      exact ⟨v.val,v.property,congrArg Subtype.val hv⟩
  dsimp only
  rw [he]
  exact source_positive_perpendicular_derived_dichotomy Q split i j m μ hB hmpos hm hij

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) (i j : Fin 2)
  (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

include μ hB in
/-- The perpendicular intersection uses the literal quotient image of the original derived core. -/
theorem original_positive_perpendicular_derived_quotient_dichotomy
    (hmpos : 0 < m) (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    let D := (commutator (pCore 2 (parabolic L S i))).map
      ((Q.q.comp (inclusion (parabolic_le_generated i))).comp
        (pCore 2 (parabolic L S i)).subtype)
    let E := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
    D ⊓ E = omegaOneAmbient E ∨ D ⊓ E = E := by
  have hf : Q.q.comp (inclusion (parabolic_le_generated i)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) i := by
    ext g
    fin_cases i
    · exact (originalMarkedIso_left_apply Q g).symm
    · exact (originalMarkedIso_right_apply Q g).symm
  dsimp only
  rw [hf]
  exact original_positive_perpendicular_derived_dichotomy Q (originalMarkedIso Q) split i j
    m μ hB hmpos hm hij

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
