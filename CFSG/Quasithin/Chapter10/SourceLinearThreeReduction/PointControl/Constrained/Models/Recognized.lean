module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.Containing
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.OriginalQuotients

/-!
# The original quotient and its containing FF actor

Apply the containing-group sieve to the literal reduced orbit action, then
recover the original quotient through its proper full-Sylow local component.
The rank-two Lie-type alternatives use the same binary field on both sides;
the binary linear alternatives force the original quotient to be SL₃(2).
The A₇ alternative retains only its proved containing-group identification.
No original module marking or fixed kernel is replaced by a group label.

This is the group-recognition part of Aschbacher--Smith 10.2.9, printed p.751.
The original-module recognition, the A₇ local-section analysis, and the
remaining action reduction belong to qt-d-10-nona5-point-constrained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open ChapterB.QuasisimpleSource Chapter3.Section02 ChapterB.InternalThompsonAction

/-- The actual original and containing quotient isomorphisms supplied by the local sieve. -/
inductive RecognizedContainingModel (Q A : Type*) [Group Q] [Group A] : Prop
  | linearThree (F : BinaryField) (large : 1 < F.degree)
      (original : Q ≃* SL(2,F.Carrier)) (containing : A ≃* SL(3,F.Carrier))
  | symplecticFour (F : BinaryField) (large : 1 < F.degree)
      (original : Q ≃* SL(2,F.Carrier))
      (containing : A ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)
  | g2 (F : BinaryField) (large : 1 < F.degree)
      (original : Q ≃* SL(2,F.Carrier)) (containing : A ≃* Atlas.G2.Model F.Carrier)
  | alternatingSeven (containing : A ≃* alternatingGroup (Fin 7))
  | binaryLinear (d : ℕ) (degree : d = 4 ∨ d = 5)
      (original : Q ≃* SL(3,ZMod 2)) (containing : A ≃* SL(d,ZMod 2))

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The literal FF action determines its containing group and, outside A₇,
the original two-core quotient through the same local embedding. -/
theorem Context.recognized_containing_model (c : Context D t v I) (a : ActionFacts c) :
    letI := c.reduced.normal
    RecognizedContainingModel (L ⧸ pCore 2 L)
      ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) := by
  let := c.reduced.normal
  cases c.containing_model a with
  | linearThree F hn E =>
    obtain ⟨e⟩ := c.rank_one_quotient_of_linear_three a F.card_eq hn E
    exact .linearThree F hn e E
  | symplecticFour F hn E =>
    obtain ⟨e⟩ := c.rank_one_quotient_of_symplectic_four a F.card_eq hn E
    exact .symplecticFour F hn e E
  | g2 F hn E =>
    have hF : 2 < Nat.card F.Carrier := by
      rw [F.card_eq]
      have := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
      omega
    obtain ⟨e⟩ := c.rank_one_quotient_of_g2 a hF E
    exact .g2 F hn e E
  | alternatingSeven E => exact .alternatingSeven E
  | binaryLinear d hd E =>
    obtain ⟨e⟩ := c.binary_three_quotient_of_binary_containing a hd E
    exact .binaryLinear d hd e E

end CFSG.Quasithin.Chapter10.PointControl.Constrained
