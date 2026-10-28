module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.ShiftedIntersections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalFrattiniRadical
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalDerivedRadical

/-!
# Shifted-root support on the original core and its literal quotient image

The exact source intersections transport through the full original endpoint
marking. Both the original Frattini image and the positive-parameter derived
image meet the shifted source Suzuki root in precisely its Omega subgroup.
The generated-carrier specialization uses Q.q composed with the original
parabolic inclusion and core subtype; it preserves either endpoint order.

Source: Fong--Seitz I (1973), p.53, the first two shifted-root exclusions.
The positive perpendicular support and near-commutator equality remain open.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits) (i j : Fin 2)
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))
  (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j)
  (hsize : (Nat.card F)^4 < (2^(2*m+1))^6)

include e ν hC μ hB h hm hij hsize in
/-- The exact intersection uses the image of the original Frattini core. -/
theorem original_shifted_frattini_intersection :
    (frattini (pCore 2 (parabolic L S i))).map
        ((endpointMap Q e i).comp (pCore 2 (parabolic L S i)).subtype) ⊓
      rootAt Q split i (Q.simple j*Q.simple i) =
        omegaOneAmbient (rootAt Q split i (Q.simple j*Q.simple i)) := by
  let hV := marked_suzuki_remainder_le_kernel Q split i m μ hB
  have he : (frattini (pCore 2 (parabolic L S i))).map
      ((endpointMap Q e i).comp (pCore 2 (parabolic L S i)).subtype) =
      (frattiniRadicalSection Q split i hV).numerator := by
    apply le_antisymm
    · rintro x ⟨v,hv,rfl⟩
      exact (originalPhiRadicalEquiv Q e split i hV ⟨v,hv⟩).property
    · intro x hx
      obtain ⟨v,hv⟩ := (originalPhiRadicalEquiv Q e split i hV).surjective ⟨x,hx⟩
      exact ⟨v.val,v.property,congrArg Subtype.val hv⟩
  rw [he]
  exact source_shifted_frattini_intersection Q split i j ν T hC m μ hB
    (parabolic_core_selfCentralizing Q e h i) hm hij hsize

include e ν hC μ hB h hm hij hsize in
/-- The positive-parameter derived-core image has exactly the same shifted-root support. -/
theorem original_positive_shifted_derived_intersection (hmpos : 0 < m) :
    (commutator (pCore 2 (parabolic L S i))).map
        ((endpointMap Q e i).comp (pCore 2 (parabolic L S i)).subtype) ⊓
      rootAt Q split i (Q.simple j*Q.simple i) =
        omegaOneAmbient (rootAt Q split i (Q.simple j*Q.simple i)) := by
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
  rw [he]
  exact source_positive_shifted_derived_intersection Q split i j ν T hC m μ hB
    (parabolic_core_selfCentralizing Q e h i) hm hij hsize hmpos

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G F : Type*} [Group G] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) (i j : Fin 2)
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))
  (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j)
  (hsize : (Nat.card F)^4 < (2^(2*m+1))^6)

include ν hC μ hB h hm hij hsize in
/-- The Frattini intersection on the literal Q.q image of the original core. -/
theorem original_shifted_frattini_quotient_intersection :
    (frattini (pCore 2 (parabolic L S i))).map
        ((Q.q.comp (inclusion (parabolic_le_generated i))).comp
          (pCore 2 (parabolic L S i)).subtype) ⊓
      rootAt Q split i (Q.simple j*Q.simple i) =
        omegaOneAmbient (rootAt Q split i (Q.simple j*Q.simple i)) := by
  have hf : Q.q.comp (inclusion (parabolic_le_generated i)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) i := by
    ext g
    fin_cases i
    · exact (originalMarkedIso_left_apply Q g).symm
    · exact (originalMarkedIso_right_apply Q g).symm
  rw [hf]
  exact original_shifted_frattini_intersection Q (originalMarkedIso Q) split i j ν T hC
    m μ hB h hm hij hsize

include ν hC μ hB h hm hij hsize in
/-- The positive derived intersection retains that same literal quotient map. -/
theorem original_positive_shifted_derived_quotient_intersection (hmpos : 0 < m) :
    (commutator (pCore 2 (parabolic L S i))).map
        ((Q.q.comp (inclusion (parabolic_le_generated i))).comp
          (pCore 2 (parabolic L S i)).subtype) ⊓
      rootAt Q split i (Q.simple j*Q.simple i) =
        omegaOneAmbient (rootAt Q split i (Q.simple j*Q.simple i)) := by
  have hf : Q.q.comp (inclusion (parabolic_le_generated i)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) i := by
    ext g
    fin_cases i
    · exact (originalMarkedIso_left_apply Q g).symm
    · exact (originalMarkedIso_right_apply Q g).symm
  rw [hf]
  exact original_positive_shifted_derived_intersection Q (originalMarkedIso Q) split i j ν T hC
    m μ hB h hm hij hsize hmpos

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

