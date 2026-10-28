module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.Defs
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.Natural

/-!
# The marked natural head used in J.2.4

The commutator pairing already identifies Q/HC with the dual of U/Z,
equivariantly for H through its original quotient map to S₅. Transporting
that entire action through the trace-determinant self-duality gives natural
coordinates on Q/HC. On the specified alternating subgroup these coordinates
carry the original natural SL₂(4) action.

This constructs `Outer.NaturalHead` from `LocalSetup`, discharging the
natural-section premise of the central-decomposition proof. The construction
keeps the literal kernel HC, the relative H-normality and the Ru2 marking.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, J.2.2(3)
and its use in J.2.4, printed pp.432–434 (PDF pp.443–445).
-/

public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ
variable {G : Type*} [Group G] [Finite G]

private def naturalDualAction (r : L2FourAction) : L2FourAction where
  action := SL2FourNatural.selfDual.symm.conjRingEquiv.toMonoidHom.comp r.action.dual
  marking := r.marking
  restriction g v := by
    change SL2FourNatural.selfDual.symm
      (r.action.dual (r.marking g) (SL2FourNatural.selfDual v)) = _
    rw [r.selfDual_restriction, SL2FourNatural.selfDual.symm_apply_apply]

/-- The actual H-equivariant natural section Q/HC, with the original
Ru2 quotient map and alternating-group marking. -/
def LocalSetup.fusionNaturalHead (d : LocalSetup G) : Fusion.Outer.NaturalHead d.toTypeRuSetup where
  action := naturalDualAction d.ru2.naturalAction
  sectionData := {
    section_le := d.dualSection.section_le
    kernel_le := d.dualSection.kernel_le
    normalized := d.dualSection.normalized
    coordinates := SL2FourNatural.selfDual.symm.toAddEquiv.toMultiplicative.toMonoidHom.comp
      d.dualSection.coordinates
    onto := SL2FourNatural.selfDual.symm.surjective.comp d.dualSection.onto
    kernel_eq := by
      rw [← d.dualSection.kernel_eq]
      ext q
      change SL2FourNatural.selfDual.symm (d.dualSection.coordinates q).toAdd = 0 ↔
        d.dualSection.coordinates q = 1
      rw [← SL2FourNatural.selfDual.symm.map_zero,
        SL2FourNatural.selfDual.symm.injective.eq_iff]
      rfl
    equivariant h q := by
      change SL2FourNatural.selfDual.symm (d.dualSection.coordinates _).toAdd =
        SL2FourNatural.selfDual.symm (d.ru2.naturalAction.action.dual
          (d.ru2.quotientMap h)
          (SL2FourNatural.selfDual (SL2FourNatural.selfDual.symm
            (d.dualSection.coordinates q).toAdd)))
      rw [SL2FourNatural.selfDual.apply_symm_apply]
      exact congrArg SL2FourNatural.selfDual.symm (d.dualSection.equivariant h q) }

end CFSG.Quasithin.ChapterJ
