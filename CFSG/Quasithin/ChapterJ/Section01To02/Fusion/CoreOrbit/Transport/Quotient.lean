module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.CoreOrbit.Definitions
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.Natural

/-!
# The full quotient orbit in J.2.8

The actual natural section from J.2.2(3) identifies the literal quotient
Q/HC with the sixteen-element natural SL₂(4) module. Surjectivity of the
inherited K/Q marking supplies actual H-conjugators. The restricted
L-intersection action is a separate assertion.

Source: Aschbacher–Smith, J.2.2(3) and J.2.8, printed pp.432,437–438.
-/

public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.Fusion.CoreOrbit
variable {G : Type*} [Group G] [Finite G]

/-- The literal core quotient has sixteen elements. -/
theorem coreQuotient_card (d : LocalSetup G) :
    Nat.card (CoreQuotient d.toTypeRuSetup) = 16 := by
  have h := card_eq_card_quotient_mul_card_subgroup
    (d.toTypeRuSetup.HC.subgroupOf d.toTypeRuSetup.Q)
  rw [Nat.card_congr (subgroupOfEquivOfLe d.toTypeRuSetup.HC_le_Q).toEquiv,
    d.card_HC, d.ru2.card_Q d.card_Z] at h
  change 2048 = Nat.card (CoreQuotient d.toTypeRuSetup) * 128 at h
  omega

/-- Nonzero natural coordinates are precisely the nonidentity literal cosets. -/
theorem coreMap_ne_one_iff (d : TypeRuSetup G) (x : d.Q) :
    coreMap d x ≠ 1 ↔ (x : G) ∉ d.HC := by
  exact not_congr (QuotientGroup.eq_one_iff x)

/-- H transports any nonidentity quotient coordinate to any other. The
explicit Q ≤ K premise is the earlier J.2.2(1) residual containment. -/
theorem quotient_transitive (d : LocalSetup G)
    (hQK : d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.K)
    (x : d.toTypeRuSetup.Q) (hx : (x : G) ∉ d.toTypeRuSetup.HC)
    (a : CoreQuotient d.toTypeRuSetup) (ha : a ≠ 1) :
    ∃ h : d.toTypeRuSetup.H,
      quotientConj d.toTypeRuSetup h (coreMap d.toTypeRuSetup x) = a := by
  let c := d.naturalQuotientSection hQK
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    (d.toTypeRuSetup.HC.subgroupOf d.toTypeRuSetup.Q) a
  have hx0 : (c.coordinates x).toAdd ≠ 0 :=
    fun he => hx ((c.coordinates_eq_one_iff x).mp he)
  have hy0 : (c.coordinates y).toAdd ≠ 0 := by
    intro he
    exact ((coreMap_ne_one_iff d.toTypeRuSetup y).mp ha)
      ((c.coordinates_eq_one_iff y).mp he)
  obtain ⟨g, hg⟩ := SL2FourNatural.transitive_nonzero _ _ hx0 hy0
  obtain ⟨k, hk⟩ := d.toTypeRuSetup.naturalQuotientMap_surjective g
  let h : d.toTypeRuSetup.H := inclusion d.toTypeRuSetup.K_le_H k
  refine ⟨h, ?_⟩
  rw [quotientConj_mk]
  apply c.quotientEquiv.injective
  change c.coordinates (coreConj d.toTypeRuSetup h x) = c.coordinates y
  apply Multiplicative.toAdd.injective
  calc
    _ = SL2FourNatural.action (d.toTypeRuSetup.naturalQuotientMap k)
        (c.coordinates x).toAdd := c.equivariant k x
    _ = (c.coordinates y).toAdd := by rw [hk]; exact hg

end CFSG.Quasithin.ChapterJ.Fusion.CoreOrbit
