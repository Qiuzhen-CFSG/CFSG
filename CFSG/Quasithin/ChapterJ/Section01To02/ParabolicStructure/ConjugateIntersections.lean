module

public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.ConjugateIntersections.Basic
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.ConjugateIntersections.Hyperplane
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.ConjugateIntersections.Orbits
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.ConjugateIntersections.Orders

/-!
# Assembly of the intersection argument in J.2.2(5)

The natural-action stabilizer orbit and Steinberg generation show that
every L-conjugate Uα distinct from U leaves Q. The hyperplane argument
then proves Uα ∩ Q is not contained in HC. The orders 8 and 32 force
the star image to have order two and Uα ∩ HC = V. All maps are the
literal ambient conjugation and Ru2 quotient maps.

This completes the conditional deduction of J.2.2(5), with the actual
dual-natural Q/HC section and its absence of binary rank-one displacements
explicit. The parabolic-structure assembly owner must discharge these
earlier inputs using the quotient-natural and natural-semilinear model
results. No core equality or distinct-conjugate conclusion is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.2(5), printed pp.432–433 (PDF pp.443–444).
-/

public section
namespace CFSG.Quasithin.ChapterJ.ConjugateIntersections
open Subgroup Representation
variable {G : Type*} [Group G] [Finite G]

/-- The intersection conclusions for a conjugate that leaves Q. The orbit
argument supplies this last premise for each conjugate distinct from U. -/
theorem conclusions_of_not_le_Q (d : LocalSetup G)
    (sectionQ : BinaryConjugationSection d.toTypeRuSetup.H d.toTypeRuSetup.Q
      d.toTypeRuSetup.HC (d.ru2.naturalAction.action.dual.comp d.ru2.quotientMap))
    (hNoRank : NoRankOne d) (l : G) (hl : l ∈ d.L)
    (hQ : ¬ conjugateU d l ≤ d.toTypeRuSetup.Q) :
    conjugateU d l ≤ d.toTypeRuSetup.H ∧
      Nat.card (((conjugateU d l).subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap) = 2 ∧
      conjugateU d l ⊓ d.toTypeRuSetup.HC = d.V :=
  ⟨conjugateU_le_H d l hl,
    conclusions_of_strict_intersections d l hl hQ (inf_Q_not_le_HC d sectionQ hNoRank l hl hQ)⟩

end CFSG.Quasithin.ChapterJ.ConjugateIntersections

namespace CFSG.Quasithin.ChapterJ
open Subgroup Representation ConjugateIntersections
variable {G : Type*} [Group G] [Finite G]

/-- J.2.2(5), conditional on the earlier dual-natural section and the model's
absence of binary transvections. Every distinct L-conjugate lies in H, has
star image of order two under the original Ru2 map, and meets HC in V. -/
theorem lemma_J_2_2_five (d : LocalSetup G)
    (sectionQ : BinaryConjugationSection d.toTypeRuSetup.H d.toTypeRuSetup.Q
      d.toTypeRuSetup.HC (d.ru2.naturalAction.action.dual.comp d.ru2.quotientMap))
    (hNoRank : NoRankOne d) (l : G) (hl : l ∈ d.L)
    (hne : conjugateU d l ≠ d.toTypeRuSetup.U) :
    conjugateU d l ≤ d.toTypeRuSetup.H ∧
      Nat.card (((conjugateU d l).subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap) = 2 ∧
      conjugateU d l ⊓ d.toTypeRuSetup.HC = d.V :=
  conclusions_of_not_le_Q d sectionQ hNoRank l hl (conjugateU_not_le_Q d l hl hne)

end CFSG.Quasithin.ChapterJ
