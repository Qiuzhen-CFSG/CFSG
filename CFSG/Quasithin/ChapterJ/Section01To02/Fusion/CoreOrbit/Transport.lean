module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.CoreOrbit.Transport.Quotient
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.CoreOrbit.Transport.Pairing
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.CoreEquality
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.CommutatorGeometry.FixedSeed
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.CommutatorGeometry.ParabolicGeometry.Natural
public import Theory.Representation.SL2FourNaturalOrbits.PlaneTransport

/-!
# Parabolic transport for the J.2.8 core orbit

The full H-orbit follows from the natural Q/HC section. For the restricted
orbit, the commutator pairing identifies S ∩ Q with functionals vanishing
on V/Z. A plane-stabilizing matrix lifts to L ∩ H under the original Ru2
marking; equality of functionals gives equality under the exact coreMap.
The natural plane quotient similarly gives transport on U/V, and J.2.3(6)
lifts this to conjugation of elements by the class-two commutator map.

The final two theorems discharge the model-plane calculations using the
actual SL₂(4) stabilizer actions. The earlier Q ≤ K and full commutator
premises are supplied by the J.2.2(1) core equalities and the J.2.3(6)
fixed-seed and propagation proofs. Thus both transport assertions follow
from the genuine LocalSetup, with no additional action or fusion premise.
The conditional adapters are retained for their existing consumers.

Source: Aschbacher–Smith J.2.2–3 and J.2.8, pp.432–434,437–438.
-/

public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.Fusion.CoreOrbit
variable {G : Type*} [Group G] [Finite G]

/-- Apply a genuine plane-annihilator calculation to the literal quotient
and the actual L ∩ H conjugators. -/
theorem quotientTransport_of_plane (d : LocalSetup G)
    (hQK : d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.K)
    (hmodel : ∀ W : Submodule (ZMod 2) FourSpace, Nat.card W = 4 →
      ∀ f k : Module.Dual (ZMod 2) FourSpace, f ≠ 0 → k ≠ 0 →
      (∀ w ∈ W, f w = 0) → (∀ w ∈ W, k w = 0) →
      ∃ g : SL2FourNatural.SL,
        (∀ w ∈ W, SL2FourNatural.action g w ∈ W) ∧
        f.comp (SL2FourNatural.action g⁻¹).toLinearMap = k)
    (s : ConjugateSeed d.toTypeRuSetup) : QuotientTransport d.toTypeRuSetup s := by
  refine ⟨coreQuotient_card d, quotient_transitive d hQK s.w s.outside, ?_⟩
  intro x hxS hxC
  have hwS : (s.w : G) ∈ d.toTypeRuSetup.S :=
    ConjugateIntersections.conjugateU_le_S d s.ell s.ell.property s.mem_conjugate
  obtain ⟨g, hg, hfg⟩ := hmodel (naturalPlane d) (naturalPlane_card d)
    (commutatorCharacter d s.w) (commutatorCharacter d x)
    (fun he => s.outside ((character_eq_zero d s.w).mp he))
    (fun he => hxC ((character_eq_zero d x).mp he))
    ((character_annihilates_plane d s.w).mpr hwS)
    ((character_annihilates_plane d x).mpr hxS)
  obtain ⟨l, hl⟩ := lift_plane_stabilizer d g hg
  refine ⟨l, ?_⟩
  rw [quotientConj_mk]
  apply (character_eq_iff d _ _).mp
  rw [character_conjugate, hl]
  have hr : d.ru2.naturalAction.action
      ((d.ru2.naturalAction.marking g : S5)⁻¹) =
      (SL2FourNatural.action g⁻¹).toLinearMap := by
    apply LinearMap.ext
    intro w
    rw [show ((d.ru2.naturalAction.marking g : S5)⁻¹) =
      d.ru2.naturalAction.marking g⁻¹ by simp]
    exact d.ru2.naturalAction.restriction g⁻¹ w
  rw [hr]
  exact hfg

/-- Apply a genuine plane-quotient calculation and the earlier J.2.3(6)
commutator equality to obtain actual L-conjugation on U minus V. -/
theorem elementaryTransport_of_plane (d : LocalSetup G)
    (hfull : ∀ t : d.toTypeRuSetup.S, (t : G) ∉ d.V →
      ⁅zpowers (t : G), d.toTypeRuSetup.S⁆ = d.V)
    (hmodel : ∀ W : Submodule (ZMod 2) FourSpace, Nat.card W = 4 →
      ∀ a b : FourSpace, a ∉ W → b ∉ W →
      ∃ g : SL2FourNatural.SL,
        (∀ w ∈ W, SL2FourNatural.action g w ∈ W) ∧
        b - SL2FourNatural.action g a ∈ W) :
    ElementaryTransport d.toTypeRuSetup :=
  elementaryTransport_of_quotient d hfull
    (elementary_quotient_of_plane d (hmodel (naturalPlane d) (naturalPlane_card d)))

/-- The literal sixteen-element quotient has the full H-orbit and the
restricted L ∩ H transport required in J.2.8. All earlier-source and
model-action premises are discharged from the genuine local setup. -/
theorem quotientTransport (d : LocalSetup G) (s : ConjugateSeed d.toTypeRuSetup) :
    QuotientTransport d.toTypeRuSetup s :=
  quotientTransport_of_plane d d.Q_le_K SL2FourNatural.plane_annihilator_transitive s

/-- L conjugates any two elements of U minus V. The natural plane quotient
supplies transport modulo V, and the proved J.2.3(6) commutator equality
corrects the remaining V-displacement by an actual element of S. -/
theorem elementaryTransport (d : LocalSetup G) : ElementaryTransport d.toTypeRuSetup := by
  apply elementaryTransport_of_plane d
    (hmodel := SL2FourNatural.plane_quotient_transitive)
  exact SpecialCore.CommutatorGeometry.FixedSeed.full_commutator d
    ((d.Q_sup_S_eq_parabolic_core.trans d.parabolic_core_eq_R₁).symm)
    d.parabolic_core_eq_R₁
    (SpecialCore.CommutatorGeometry.natural_parabolics d.ru1)

end CFSG.Quasithin.ChapterJ.Fusion.CoreOrbit
