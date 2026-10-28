module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.FullCoreCover
public import Theory.Representation.BinaryCoinvariantCommutator

/-!
# Literal core generation from a detected full cover

The distance-four source cover has kernel exactly the core derived subgroup.
Thus coinvariant generation under any marked subgroup lifts to generation of
the original core by literal subgroup commutators. This is the lift used in
Aschbacher–Smith 15.3.23 and15.3.31, printed pp.1128–1129 and1132.
-/

@[expose] public noncomputable section
open Subgroup Representation

namespace CFSG.Quasithin.ChapterC.BinaryMS.FullCoreDoubleDualCover
variable {A : Type*} [Group A] [Finite A]

/-- Marked full coinvariants generate the actual intrinsic core. -/
theorem core_eq_commutator_of_coinvariants (c : FullCoreDoubleDualCover A)
    (B : Subgroup A)
    (hgen : Coinvariants.ker (c.representation.comp
      (B.map (c.marking.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A)))).subtype) = ⊤) :
    blockU A = ⁅blockU A,B⁆ := by
  apply Representation.subgroup_eq_commutator_of_full_coinvariants (blockU A) B
    (pCore_isPGroup.to_le blockU_le_core)
    (c.marking.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))) c.representation
    c.coreProjection c.coreOnto c.coreKernel _ hgen
  intro a x y hy
  have he : y = blockConjugate A a x := Subtype.ext hy
  rw [he]
  exact c.coreAction a x

end CFSG.Quasithin.ChapterC.BinaryMS.FullCoreDoubleDualCover
