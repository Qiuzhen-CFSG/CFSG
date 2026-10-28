module

public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.MathieuOne.M24
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.MathieuTwo.M22
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Discharging the two Mathieu inputs to Janko-four generation

The native M24 theorem supplies rank-one E-generation directly. For Aut(M22),
the actual inner subgroup is normal, isomorphic to M22 and has trivial
centralizer. Thus the proved faithful-extension theorem supplies rank-two
E-generation for the full automorphism group, including its outer coset.
These are precisely the two inputs to the Janko-four local quotient lifts.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
E.1.14(4)--(5), printed p.214, citing Asc82a Lemma 4.9.
-/

public section
namespace CFSG.Quasithin.ChapterE.JankoFour
open Subgroup Theory.GroupTheory Sporadic.Mathieu

/-- The completed intrinsic rank-one bound for the native Mathieu model. -/
theorem mathieu24_isEGenerated : IsEGenerated 1 M24 :=
  MathieuOne.isEGenerated_of_equiv_m24 (MulEquiv.refl M24)

/-- Apply the faithful-extension theorem to the actual inner subgroup of Aut(M22). -/
theorem autMathieu22_isEGenerated : IsEGenerated 2 (MulAut M22) := by
  let e : M22 ≃* MulAut.innerSubgroup M22 :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot m22_center_eq_bot)
  exact MathieuTwo.m22_extension_isEGenerated (MulAut.innerSubgroup M22)
    (MulAut.centralizer_innerSubgroup_eq_bot m22_center_eq_bot) e.symm
    (default : Sylow 2 (MulAut M22))

end CFSG.Quasithin.ChapterE.JankoFour
