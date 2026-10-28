module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.AvailableCovers
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.Triality
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.BenderTwoKernel
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.BinaryFour

/-!
# Even-family reductions and completed branches of 1.1.5(3)

Every Bender family has a proved inner marked action. Every rank-two family
except the genuine derived Sp₄(2) overlap does as well, including derived
G₂(2), triality at every positive exponent, large Ree, and the Tits endpoint.
The center-free rank-two case therefore gives the canonical source conclusion.

`AvailableCovers` completes PSL₂(q), q ≥ 8, PSL₃(4), Sp₄(q), q ≥ 4,
G₂(q), q ≥ 4, and PSL₅(2), including the allowed exceptional two-covers.
`BenderTwoKernel` supplies the full Bender source implication from the
universal double-cover Sylow-fixer theorem, using an index-two quotient to
handle every nontrivial central two-kernel. `BinaryFour` completes PSL₄(2):
fixed-point surjectivity contradicts the index-two fixed image in its
nontrivial Schur cover. That earlier Bender rigidity theorem and the
remaining rank-two covering exclusions still require their source proofs
for the unconditional assembly.

Source: Aschbacher--Smith, 1.1.5(3), printed pp.501--503.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
open Chapter15.Section03.Candidates.ComponentStructure ClassificationModels

variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
  {α : MulAut L} {P : Sylow 2 L}

/-- The exact rank-two list has only the permitted derived symplectic overlap
left after the model Sylow-fixer calculations. This is the innerness step,
before the independent central-cover exclusions. -/
theorem MarkedInvolution.rankTwo_inner_or_symplecticDerived
    (d : MarkedInvolution α P) {f : ℕ}
    (h : ChapterA.Section02.IsTheoremCRankTwoModel (L ⧸ center L) f) :
    α ∈ (MulAut.conj (G := L)).range ∨
      Nonempty (L ⧸ center L ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) := by
  cases h with
  | linear hf iso => exact .inl (d.linearThree_inner hf iso)
  | symplectic hf iso => exact .inl (d.symplecticFour_inner hf iso)
  | g2 hf iso => exact .inl (d.g2_inner hf iso)
  | triality hf iso => exact .inl (d.triality_inner hf iso)
  | ree_f4 m hm _ iso => obtain ⟨e⟩ := iso; exact .inl (d.ree_inner hm e)
  | symplectic_derived _ iso => exact .inr iso
  | g2_derived _ iso => obtain ⟨e⟩ := iso; exact .inl (d.g2Derived_inner e)
  | tits _ iso => obtain ⟨e⟩ := iso; exact .inl (d.tits_inner e)

/-- Complete the center-free rank-two case. The remaining equivalence is
exactly the source A₆ overlap, rather than an unproved recognition tag. -/
theorem MarkedInvolution.rankTwo_modelAction_of_center_eq_bot
    (d : MarkedInvolution α P) {f : ℕ}
    (h : ChapterA.Section02.IsTheoremCRankTwoModel (L ⧸ center L) f)
    (hz : center L = ⊥) : ModelAction115 L α ∨
      Nonempty (L ⧸ center L ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) := by
  rcases d.rankTwo_inner_or_symplecticDerived h with hi | he
  · exact .inl (d.lie_of_center_eq_bot (.inr (.inl (rankTwoTheoremC_of_model h))) hi hz)
  · exact .inr he

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
