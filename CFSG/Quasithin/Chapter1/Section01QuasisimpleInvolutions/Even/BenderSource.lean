module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.BenderTwoKernel
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity

/-!
# The complete marked Bender branch of 1.1.5

The proved universal Sylow-centralizer rigidity for central double covers
supplies the remaining premise of the two-kernel reduction. Hence the center
of the original quasisimple group is trivial and its original involution
induces an inner automorphism in the prescribed characteristic-two model.
This includes the small PSL2 and Suzuki parameters and all Hermitian models.

Source: Aschbacher--Smith 1.1.5(3)(a), printed pp.501--502;
GLS4 Chapter 4, Lemma 2.8(c).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
open Chapter15.Section03.Candidates.ComponentStructure ClassificationModels
variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
  {α : MulAut L} {P : Sylow 2 L}

/-- Original marked Bender inputs force the entire center to vanish. -/
theorem MarkedInvolution.bender_source_center_eq_bot
    (d : MarkedInvolution α P) (h : IsBenderModel (L ⧸ center L)) : center L = ⊥ :=
  d.bender_center_eq_bot_of_doubleCoverRigidity h
    (fun _ _ _ _ _ _ hB c hc Q a hfix =>
      BenderSuzuki.ZD.bender_cover_fixingSylow_eq_one hB c hc Q a hfix)

/-- The full Bender source implication, with no cover-rigidity premise. -/
theorem MarkedInvolution.bender_source
    (d : MarkedInvolution α P) (h : IsBenderModel (L ⧸ center L)) : ModelAction115 L α :=
  d.lie_of_center_eq_bot (Or.inl h) (d.bender_inner h) (d.bender_source_center_eq_bot h)

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
