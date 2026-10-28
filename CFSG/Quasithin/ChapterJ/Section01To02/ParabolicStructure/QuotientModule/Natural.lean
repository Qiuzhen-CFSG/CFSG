module

public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.Duality
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.Alternating
public import Theory.Representation.SL2FourNaturalOrbits.SelfDual

/-!
# The marked natural K-action on Q/HC

The trace-determinant self-duality of the binary natural SL₂(4) module
transports the H-equivariant commutator dual to natural coordinates for K.
The group map K → SL₂(4) is exactly the original Ru2 quotient map restricted
to K, followed by the inverse of the given alternating-group marking.
It is surjective and has kernel K ∩ Q. The sole earlier-source input Q ≤ K
places the literal section Q/HC inside K; its producer is J.2.2(1).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.2(3), printed p.432 (PDF p.443).
-/

@[expose] public section
open Subgroup Representation
noncomputable section
namespace CFSG.Quasithin.ChapterJ
variable {G : Type*} [Group G] [Finite G]

theorem L2FourAction.selfDual_restriction (r : L2FourAction)
    (g : SL2FourNatural.SL) (f : Module.Dual (ZMod 2) FourSpace) :
    SL2FourNatural.selfDual.symm (r.action.dual (r.marking g) f) =
      SL2FourNatural.action g (SL2FourNatural.selfDual.symm f) := by
  apply SL2FourNatural.selfDual.injective
  rw [SL2FourNatural.selfDual.apply_symm_apply, SL2FourNatural.selfDual_equivariant,
    SL2FourNatural.selfDual.apply_symm_apply]
  apply LinearMap.ext
  intro v
  change f (r.action ((r.marking g : S5)⁻¹) v) = f (SL2FourNatural.action g⁻¹ v)
  rw [show (r.marking g : S5)⁻¹ = r.marking g⁻¹ by simp, r.restriction]

def TypeRuSetup.naturalQuotientMap (d : TypeRuSetup G) : d.K →* SL2FourNatural.SL :=
  d.ru2.naturalAction.marking.symm.toMonoidHom.comp d.alternatingMap

theorem TypeRuSetup.naturalQuotientMap_surjective (d : TypeRuSetup G) :
    Function.Surjective d.naturalQuotientMap :=
  d.ru2.naturalAction.marking.symm.surjective.comp d.alternatingMap_surjective

theorem TypeRuSetup.naturalQuotientMap_kernel (d : TypeRuSetup G) :
    d.naturalQuotientMap.ker = d.Q.subgroupOf d.K := by
  rw [← d.alternatingMap_kernel]
  ext k
  change d.ru2.naturalAction.marking.symm (d.alternatingMap k) = 1 ↔ d.alternatingMap k = 1
  rw [← d.ru2.naturalAction.marking.symm.map_one,
    d.ru2.naturalAction.marking.symm.injective.eq_iff]

theorem TypeRuSetup.naturalQuotientMap_marking (d : TypeRuSetup G) (k : d.K) :
    d.ru2.naturalAction.marking (d.naturalQuotientMap k) = d.alternatingMap k :=
  d.ru2.naturalAction.marking.apply_symm_apply _

/-- The actual natural SL₂(4) module on Q/HC, with the inherited marking. -/
def LocalSetup.naturalQuotientSection (d : LocalSetup G)
    (hQK : d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.K) :
    BinaryConjugationSection d.toTypeRuSetup.K d.toTypeRuSetup.Q d.toTypeRuSetup.HC
      (SL2FourNatural.naturalRepresentation.comp d.toTypeRuSetup.naturalQuotientMap) where
  section_le := hQK
  kernel_le := d.toTypeRuSetup.HC_le_Q
  normalized := d.toTypeRuSetup.K_le_H.trans d.ru2.six.normalized
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
  equivariant k q := by
    change SL2FourNatural.selfDual.symm (d.dualSection.coordinates _).toAdd =
      SL2FourNatural.action (d.toTypeRuSetup.naturalQuotientMap k)
        (SL2FourNatural.selfDual.symm (d.dualSection.coordinates q).toAdd)
    refine (congrArg SL2FourNatural.selfDual.symm
      (d.dualSection.equivariant (inclusion d.toTypeRuSetup.K_le_H k) q)).trans ?_
    change SL2FourNatural.selfDual.symm (d.ru2.naturalAction.action.dual
      (d.toTypeRuSetup.alternatingMap k) _) = _
    rw [← d.toTypeRuSetup.naturalQuotientMap_marking k]
    exact d.ru2.naturalAction.selfDual_restriction _ _

end CFSG.Quasithin.ChapterJ
