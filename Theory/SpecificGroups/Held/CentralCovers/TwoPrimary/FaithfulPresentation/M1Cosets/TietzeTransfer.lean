module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Certificate
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Initials
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Membership
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.ReducedData
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.SchreierData

import Mathlib.Tactic.FinCases

/-!
# Tietze transfer for the Held M₁ Schreier problem

The selected 49 relations follow from the exact 14,409 initial Schreier
relations in every group. Every one of the 2,062 original generators belongs
to any subgroup containing the 17 surviving values. The three protected
symbols remain arbitrary subgroup elements throughout.

The proof checks the acyclic word-equality certificate for the retained
17-generator Tietze prefix, then follows its signed elimination equations
using ordinary subgroup closure. It uses neither a finite model identification
nor faithfulness of the Held presentation. Source: John Bray's ATLAS
`HeG1-P1.M`, retained in `Held/Model/Source/`; see the descendant source README.
-/

public section

open Theory.GroupTheory.CosetEnumeration
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer

variable {G : Type*} [Group G] (g : Nat → G)

/-- The exact selected short relations, with the surviving original labels. -/
theorem reduced_relators_of_initial
    (hi : ∀ r : Fin 14409, eval g (Schreier.initialRelator r) = 1) :
    ∀ r : Fin 49, eval (fun a : Fin 17 => g (Reduced.originalLabel a))
      (Reduced.relator r) = 1 := by
  have hv := Certificate.valid (Initials.valid hi)
  intro r
  fin_cases r
  · exact (hv 7565 (by decide))
  · exact (hv 7564 (by decide))
  · exact (hv 7563 (by decide))
  · exact (hv 29422 (by decide))
  · exact (hv 6628 (by decide))
  · exact (hv 6181 (by decide))
  · exact (hv 28560 (by decide))
  · exact (hv 28508 (by decide))
  · exact (hv 28492 (by decide))
  · exact (hv 14224 (by decide))
  · exact (hv 12004 (by decide))
  · exact (hv 30999 (by decide))
  · exact (hv 31014 (by decide))
  · exact (hv 28274 (by decide))
  · exact (hv 26850 (by decide))
  · exact (hv 26853 (by decide))
  · exact (hv 29489 (by decide))
  · exact (hv 29387 (by decide))
  · exact (hv 29501 (by decide))
  · exact (hv 29971 (by decide))
  · exact (hv 29400 (by decide))
  · exact (hv 31012 (by decide))
  · exact (hv 30591 (by decide))
  · exact (hv 30009 (by decide))
  · exact (hv 29855 (by decide))
  · exact (hv 29697 (by decide))
  · exact (hv 30258 (by decide))
  · exact (hv 29852 (by decide))
  · exact (hv 29403 (by decide))
  · exact (hv 30393 (by decide))
  · exact (hv 30438 (by decide))
  · exact (hv 30567 (by decide))
  · exact (hv 31015 (by decide))
  · exact (hv 31013 (by decide))
  · exact (hv 30997 (by decide))
  · exact (hv 31016 (by decide))
  · exact (hv 31010 (by decide))
  · exact (hv 30968 (by decide))
  · exact (hv 30977 (by decide))
  · exact (hv 31003 (by decide))
  · exact (hv 30789 (by decide))
  · exact (hv 30860 (by decide))
  · exact (hv 30994 (by decide))
  · exact (hv 31017 (by decide))
  · exact (hv 30472 (by decide))
  · exact (hv 30669 (by decide))
  · exact (hv 31008 (by decide))
  · exact (hv 30984 (by decide))
  · exact (hv 30990 (by decide))

/-- Recover all eliminated symbols in an arbitrary subgroup. -/
theorem generators_mem_of_initial
    (hi : ∀ r : Fin 14409, eval g (Schreier.initialRelator r) = 1)
    (H : Subgroup G)
    (hs : ∀ a : Fin 17, g (Reduced.originalLabel a) ∈ H) :
    ∀ n : Fin 2062, g (n.val + 1) ∈ H :=
  Membership.all_mem H (Certificate.valid (Initials.valid hi)) hs

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer
