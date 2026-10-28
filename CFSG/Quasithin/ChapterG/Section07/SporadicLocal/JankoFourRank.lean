module

public import Theory.SpecificGroups.Janko4.Model.TwoRank.Bounds
public import Theory.GroupTheory.PrimeRankCentralCover

/-!
# The J₄ automorphism-rank input to G.7

The actual max1 Sylow and its kernel-action comparison reduce the rank bound
to a finite elementary fixed-mask inequality. The checked certificate in
`Theory.SpecificGroups.Janko4.Model.TwoRank.Finite` discharges that inequality
for the literal eleven-coordinate action. The perfect-cover application
descends through the literal quotient by the whole center; it does not identify
the cover with J₄. Its perfectness also supplies the model perfectness used for
innerness.

Source: Aschbacher–Smith, G.7.3(2), printed pp.347–348 (PDF pp.358–359),
citing Asc82a and GLS98 5.2.10/5.6.1. The independent extraspecial-eleven
construction and degree-110 bound are already in `SporadicLocal.OddSubgroups`.
-/

public section
namespace CFSG.Quasithin.ChapterG.Section07.SporadicLocal
open Subgroup Theory.GroupTheory
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- Conditional J₄ rank input, retaining the finite-action interface for reuse. -/
theorem j4_automorphism_twoRank_le_eleven_of_fixedBound
    [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (h : Janko4.TwoRank.ElementaryFixedBound) :
    primeRank 2 (MulAut Janko4.Model) ≤ 11 :=
  Janko4.TwoRank.automorphism_twoRank_le_eleven_of_fixedBound h

/-- The J₄ automorphism two-rank bound with the finite-action premise discharged. -/
theorem j4_automorphism_twoRank_le_eleven
    [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model] :
    primeRank 2 (MulAut Janko4.Model) ≤ 11 :=
  Janko4.TwoRank.automorphism_twoRank_le_eleven

/-- Application to the source component's actual central quotient. -/
theorem j4_centralQuotient_automorphism_twoRank_le_eleven_of_fixedBound
    {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    [IsSimpleGroup Janko4.Model]
    (h : Janko4.TwoRank.ElementaryFixedBound)
    (e : L ⧸ center L ≃* Janko4.Model) : primeRank 2 (MulAut L) ≤ 11 := by
  let : Group.IsPerfect Janko4.Model := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  have hdesc := automorphism_primeRank_le_quotient_center (E := L) 2
  rw [primeRank_equiv 2 (MulAut.congr e)] at hdesc
  exact hdesc.trans (j4_automorphism_twoRank_le_eleven_of_fixedBound h)

/-- The J₄ bound for an actual perfect central cover. -/
theorem j4_centralQuotient_automorphism_twoRank_le_eleven
    {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    [IsSimpleGroup Janko4.Model]
    (e : L ⧸ center L ≃* Janko4.Model) : primeRank 2 (MulAut L) ≤ 11 := by
  let : Group.IsPerfect Janko4.Model := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  have hdesc := automorphism_primeRank_le_quotient_center (E := L) 2
  rw [primeRank_equiv 2 (MulAut.congr e)] at hdesc
  exact hdesc.trans j4_automorphism_twoRank_le_eleven

end CFSG.Quasithin.ChapterG.Section07.SporadicLocal
