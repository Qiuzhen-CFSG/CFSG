module
public import Theory.Representation.OrthogonalFourPlusMatrix.OuterElementaryRank
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActorDegreesSeven
/-!
# The outer-actor row in the larger-actor degree sieve

In G.11.2(7) the dotted terminal representation is the binary restriction
of the natural four-dimensional split orthogonal module over GF(4).
The larger-actor inequality forces the original elementary actor to have
order at least sixteen. The intrinsic normalizer bound then puts that
actor in the marked Ω₄⁺(4), contradicting the outer-actor clause of the row.

Combining this exclusion with the previously proved sieve leaves row (5).
The concluding disjunction retains the explicit exhaustive-recognition
premise; it does not assert the unconditional source degree alternatives.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
14.3.14, printed p.994, using G.11.2(7), printed p.364
(combined manuscript, 1 March 2004).
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
namespace LargeActorSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (s : LargeActorSource T M Mc F g B v)
include s

/-- Row (7) is impossible: every elementary actor of rank at least four
in the binary determinant normalizer lies in the marked Ω₄⁺(4). -/
theorem not_caseSeven :
    ¬ ChapterG.Section11.CaseSeven F.terminalRepresentation (F.terminalDot (F.X g)) := by
  rintro ⟨hd, hout, e, f, he⟩
  have hm := s.half_degree_le_actor
  have hc : 16 ≤ Nat.card (F.terminalDot (F.X g)) := by
    rw [Nat.card_congr Additive.ofMul, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mpr (show 4 ≤
      finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) by omega)
  let a := e.trans ClassicalOrthogonal.FourPlusMatrix.Binary.orthogonalEquiv.symm
  let E := f.trans ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates
  apply hout
  apply BinaryOffender.elementary_le_marked_determinant_of_card_ge_sixteen
    F.terminalRepresentation s.hypothesis.faithful (generalizedFitting F.TerminalHdot) a E
    (X := F.terminalDot (F.X g)) (hc := hc)
  intro h w
  change ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates
    (f (F.terminalRepresentation h w)) = _
  have hew := he h w
  change f (F.terminalRepresentation h w) = _ at hew
  rw [hew]
  have hh := ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates_projective_equivariant
    (ClassicalOrthogonal.FourPlusMatrix.Binary.orthogonalEquiv.symm (e h)) (f w)
  rw [MulEquiv.apply_symm_apply] at hh
  exact hh

/-- Applying the outer-actor bound to the source sieve leaves only the
split six-space row. Exhaustive recognition remains a source obligation. -/
theorem degree_cases_or_caseFive
    (hc : ChapterG.Section11.Conclusion F.terminalRepresentation B
      (F.terminalDot (F.X g))) :
    ((finrank (ZMod 2) (Additive F.Uhat) = 4 ∧
        2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 ∧
        Nonempty (F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2)))) ∨
      ChapterG.Section11.CaseFive F.terminalRepresentation B := by
  rcases s.degree_cases_or_remaining_five_seven hc with hd | h5 | h7
  · exact Or.inl hd
  · exact Or.inr h5
  · exact (s.not_caseSeven h7).elim
end LargeActorSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
