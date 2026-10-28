module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.CoverRigidity

/-!
# The two-copy fixed-kernel branch

Let D = [O₂(J),L] be abelian, with D/C_D(L) identified equivariantly with two
natural binary SL₃(2) modules. The MS3 reduction constructs a faithful FF-action
of J/C_J(D) on D and makes the given projection a commutator-generated cover.
The proved cover-rigidity theorem then forces C_D(L) to be trivial.

This completes the fixed-kernel implication for a supplied natural two-copy
quotient. Existence of that quotient and the full C.1.34 classification are
separate obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.31(MS3),
C.1.34(2),(5), printed pp.135–137, and I.1.5–6, printed p.408.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS

universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}

/-- An abelian binary MS commutator core with natural two-copy fixed quotient
has trivial fixed kernel. The genuine MS3 hypotheses supply the FF-action
needed to exclude every nontrivial covering extension. -/
theorem Input.abelianCore_fixedKernel_eq_one_of_twoCopies
    (h : Input κ L R) (hc : IsMulCommutative (commutatorCore L))
    (q : AbelianCore.NaturalQuotient h 2) :
    Nat.card (coreFixed L) = 1 :=
  h.abelianCore_fixedKernel_eq_one_of_twoCopies_of_coverRigidity hc q
    AbelianCore.DoubleCopy.coverRigidity

end CFSG.Quasithin.ChapterC.BinaryMS
