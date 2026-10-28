module
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.RankOne
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.RankOneExclusions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource

/-!
# Actual even rank-one rows of Table B.4.5

The existing cubic recognition constructs the natural or Hermitian PSL₂ action,
and the natural SU₃ and Suzuki actions. The Hermitian isometry and the genuine
projective quotient identify the literal minus orthogonal action used by the
public table. All field parameters, dimensions and separate ratios are retained.
The natural PSL₂ alternative feeds the complete B.4.2 source theorem.

Source: Aschbacher–Smith B.4.5 and K.3.1, K.3.3, K.3.6, pp.87,453–457.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

open OrthogonalFourMinus.FiniteModel in
omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem orthogonal_table {s : ℕ} [NeZero s]
    (M : ChapterK.RankOne.OrthogonalModel s ρ L) : TableB45 ρ L := by
  let : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
  let K : BinaryField := {
    Carrier := fixedField s
    degree := s
    degree_pos := NeZero.pos s
    card_eq := card_fixedField s }
  let F : BinaryField := {
    Carrier := Field s
    degree := 2 * s
    degree_pos := Nat.mul_pos (by decide) (NeZero.pos s)
    card_eq := GaloisField.card 2 (2 * s) (Nat.mul_ne_zero (by decide) (NeZero.ne s)) }
  let : Module (ZMod 2) K.Carrier := K.binaryAlgebra.toModule
  let a : ActionEquiv (ρ.comp L.subtype) (orthogonalFour K) := by
    refine {
      groupEquiv := M.minusGroupEquiv.trans (ClassicalOrthogonal.Minus.minusProjectiveEquiv 2)
      linearEquiv := ?_
      intertwines := ?_ }
    · exact M.minusCoordinates.toLinearEquiv
        (fun c x => ZMod.map_smul M.minusCoordinates.toAddMonoidHom c x)
    · intro g v
      change M.minusCoordinates (ρ g v) =
        ClassicalOrthogonal.Minus.projectiveOmegaNatural _ _
          (ClassicalOrthogonal.Minus.omegaProjectiveEquiv _
          (ClassicalOrthogonal.Minus.quadraticForm_represents_one (F := fixedField s) 2) (M.minusGroupEquiv g))
          (M.minusCoordinates v)
      rw [show ClassicalOrthogonal.Minus.omegaProjectiveEquiv _
          (ClassicalOrthogonal.Minus.quadraticForm_represents_one (F := fixedField s) 2) (M.minusGroupEquiv g) =
        QuotientGroup.mk' _ (M.minusGroupEquiv g) from rfl,
        ClassicalOrthogonal.Minus.projectiveOmegaNatural_mk]
      exact (M.minus_intertwines g v).symm
  exact .orthogonal K F rfl (M.groupEquiv.trans (Theory.PSL2.sl2QuotientEquiv _))
    a M.finrank_eq M.ratio_upper_bounds.1 M.ratio_upper_bounds.2

theorem psl2_case (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {r : ℕ} (hr : 2 ≤ r)
    (he : ClassicalGroup.IsPSL (L ⧸ center L) 2 (2 ^ r)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) ∨
      TableB45 ρ L := by
  obtain ⟨K,hK,hfin,hchar,_,_,_,halt⟩ := h.psl2_case hr he
  rcases halt with ⟨_,_,_,hq,_⟩ | ⟨s,_,_,hs,_,_,M,_⟩
  · exact Or.inl (SourceClassification.psl2_case h
      ((isFFModule_iff_quadraticRatio_le_one ρ).mpr hq.le) hr he)
  · let : NeZero s := ⟨hs.ne'⟩
    exact Or.inr (orthogonal_table M)

open BenderSuzuki.MatrixGroups in
theorem unitary_table (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {n : ℕ} (hn : 2 ≤ n)
    (he : ClassicalGroup.IsPSU (L ⧸ center L) 3 (2 ^ n)) : TableB45 ρ L := by
  classical
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := he
  let : CharP F 2 := Theory.SpecificGroups.UnitaryRootNormalizer.charP_binary (by omega) hcard
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hc := SourceClassification.unitary_central_quotient h J hn hcard hconj e
  obtain ⟨M⟩ := ChapterK.RankOne.UnitaryRecognition.source_unitaryModel_of_centralQuotient
    J hn hcard hconj h hc
  have hcalc := h.unitary_case M hn hcard hconj (Classical.choice (inferInstance : Nonempty (Sylow 2 G)))
  let B : BinaryField := {
    Carrier := F
    degree := 2 * n
    degree_pos := by omega
    card_eq := by rw [hcard, ← pow_mul, Nat.mul_comm n 2] }
  let a : ActionEquiv (ρ.comp L.subtype) (unitaryThree B J) := {
    groupEquiv := M.groupEquiv
    linearEquiv := M.coordinates
    intertwines := M.intertwines }
  exact .unitary B n hn rfl J hconj a hcalc.2.2.1 hcalc.1 hcalc.2.1

open BenderSuzuki.MatrixGroups in
theorem suzuki_table (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {m : ℕ} (hm : 1 ≤ m) (e : L ⧸ center L ≃* SuzukiMatrixGroup m) : TableB45 ρ L := by
  classical
  let M := h.suzukiModel hm e
  have hc := h.suzuki_case_of_quotient hm e (Classical.choice (inferInstance : Nonempty (Sylow 2 G)))
  let a : ActionEquiv (ρ.comp L.subtype)
      (Chapter13.Section08.Components.Suzuki.natural m) := {
    groupEquiv := M.groupEquiv
    linearEquiv := M.coordinates
    intertwines := M.intertwines }
  exact .suzuki m (by omega) a hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.1
end CFSG.Quasithin.ChapterB.SmallRatioClassification
