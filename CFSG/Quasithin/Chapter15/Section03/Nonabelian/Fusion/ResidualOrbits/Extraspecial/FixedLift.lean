module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial.Outside
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.LocalProduct
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial.FixedLift.Centralizers
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial.FixedLift.Action
public import Theory.Representation.PSL3Two.TransvectionFixedLift

/-!
# Centralizers and the fixed-lift product in 15.3.61

The natural-plus-dual transvection calculation gives the literal fixed
lift order 32 and relative index four. Counting the actual U-action on V
and the extraspecial commutator pairing identifies it with both C_U(V)
and C_U(U ∩ V). Consequently a centralizes the lift, whose intersection
with V is the source hyperplane of order eight.

The square-coordinate identity identifies the fixed lift with the quadratic
transvection preimage. The structural construction lifts two radical vectors
to a commuting E₄ factor and a hyperbolic pair to D₈, giving an actual
E₄ × D₈ equivalence. Ambient multiplication and the hyperplane count then
construct E₈ × D₈. Neither product is inferred from order.

The hypotheses used here are consequences of 15.3.51(4), 15.3.53,
15.3.55, 15.3.58 and 15.3.59: U is extraspecial of order 128 with literal
center Z, U = O₂(H), V is elementary of order 16, Z ≤ V, |U ∩ V| = 8,
and the conjugation action of U on V has image of order four. The supplied
RecognizedAction retains the actual actor quotient and natural/dual action;
a lies in the literal residual K as well as V − U. The square-coordinate
identity is exactly the permitted square_zero premise of MarkedGeometry.
It is the only additional premise of the product construction; its proof
and the complete source assembly remain with their respective owners.
Source: Aschbacher–Smith, combined manuscript (1 March 2004),
the first paragraph proving 15.3.61(2), printed p.1150.
-/

public section

open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial.FixedLift
variable {G : Type*} [Group G] [Finite G] {T Z ZS V : Subgroup G} {t : G}
variable [(Z.subgroupOf (closureU Z ZS)).Normal]
variable [IsExtraspecial 2 (closureU Z ZS)] [IsElementaryAbelian 2 V]

/-- The source's two relative centralizer identities, with the fixed-lift order
proved from the actual inner transvection. -/
theorem eq_centralizers (d : RecognizedAction T Z ZS V t)
    (hU : closureU Z ZS = coreQ Z)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (hZV : Z ≤ V) (hUcard : Nat.card (closureU Z ZS) = 128)
    (hW : Nat.card (closureU Z ZS ⊓ V : Subgroup G) = 8)
    (hUV : closureU Z ZS ≤ normalizer (V : Set G))
    (himage : Nat.card (actionOnV hUV).range = 4)
    (a : centralizerH Z) (haV : (a : G) ∈ V) (haK : (a : G) ∈ residualK Z)
    (haU : (a : G) ∉ closureU Z ZS) (ha : orderOf (a : G) = 2) :
    fixedLift Z ZS a = closureU Z ZS ⊓ centralizer (V : Set G) ∧
      fixedLift Z ZS a = closureU Z ZS ⊓
        centralizer ((closureU Z ZS ⊓ V : Subgroup G) : Set G) :=
  eq_centralizers_of_card a haV hcenter hZV hUcard hW hUV himage
    (card_and_index d hU hcenter hUcard a haK haU ha).1

/-- The chosen outside involution centralizes the entire fixed lift. -/
theorem centralizes (d : RecognizedAction T Z ZS V t)
    (hU : closureU Z ZS = coreQ Z)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (hZV : Z ≤ V) (hUcard : Nat.card (closureU Z ZS) = 128)
    (hW : Nat.card (closureU Z ZS ⊓ V : Subgroup G) = 8)
    (hUV : closureU Z ZS ≤ normalizer (V : Set G))
    (himage : Nat.card (actionOnV hUV).range = 4)
    (a : centralizerH Z) (haV : (a : G) ∈ V) (haK : (a : G) ∈ residualK Z)
    (haU : (a : G) ∉ closureU Z ZS) (ha : orderOf (a : G) = 2) :
    (a : G) ∈ centralizer (fixedLift Z ZS a : Set G) := by
  rw [(eq_centralizers d hU hcenter hZV hUcard hW hUV himage a haV haK haU ha).1]
  intro x hx
  exact (hx.2 a haV).symm

/-- Intersecting the fixed lift with elementary V gives the source hyperplane. -/
theorem intersection_eq (d : RecognizedAction T Z ZS V t)
    (hU : closureU Z ZS = coreQ Z)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (hZV : Z ≤ V) (hUcard : Nat.card (closureU Z ZS) = 128)
    (hW : Nat.card (closureU Z ZS ⊓ V : Subgroup G) = 8)
    (hUV : closureU Z ZS ≤ normalizer (V : Set G))
    (himage : Nat.card (actionOnV hUV).range = 4)
    (a : centralizerH Z) (haV : (a : G) ∈ V) (haK : (a : G) ∈ residualK Z)
    (haU : (a : G) ∉ closureU Z ZS) (ha : orderOf (a : G) = 2) :
    fixedLift Z ZS a ⊓ V = closureU Z ZS ⊓ V := by
  have he := (eq_centralizers d hU hcenter hZV hUcard hW hUV himage a haV haK haU ha).1
  apply le_antisymm (inf_le_inf_right _ (le_closure a))
  intro x hx
  refine ⟨?_, hx.2⟩
  rw [he]
  exact ⟨hx.1, V.le_centralizer hx.2⟩

/-- The actual fixed-lift intersection has index two in V. -/
theorem hyperplane_card (d : RecognizedAction T Z ZS V t)
    (hU : closureU Z ZS = coreQ Z)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (hZV : Z ≤ V) (hUcard : Nat.card (closureU Z ZS) = 128)
    (hW : Nat.card (closureU Z ZS ⊓ V : Subgroup G) = 8) (hV : Nat.card V = 16)
    (hUV : closureU Z ZS ≤ normalizer (V : Set G))
    (himage : Nat.card (actionOnV hUV).range = 4)
    (a : centralizerH Z) (haV : (a : G) ∈ V) (haK : (a : G) ∈ residualK Z)
    (haU : (a : G) ∉ closureU Z ZS) (ha : orderOf (a : G) = 2) :
    Nat.card V = 2 * Nat.card (fixedLift Z ZS a ⊓ V : Subgroup G) := by
  rw [intersection_eq d hU hcenter hZV hUcard hW hUV himage a haV haK haU ha, hW, hV]

/-- The literal fixed lift is E₄ × D₈. Square compatibility supplies the
commuting radical lifts and the dihedral pair in the actual transvection
preimage; the coordinate projection transports their product to U_a. -/
noncomputable def fixedLiftEquiv_of_square_zero (d : RecognizedAction T Z ZS V t)
    (hU : closureU Z ZS = coreQ Z)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (hsquare : ∀ x : closureU Z ZS, (x : G) ^ 2 = 1 ↔
      BinaryNaturalDual.quadratic (d.coordinates (QuotientGroup.mk' _ x)).toAdd = 0)
    (a : centralizerH Z) (haK : (a : G) ∈ residualK Z)
    (haU : (a : G) ∉ closureU Z ZS) (ha : orderOf (a : G) = 2) :
    fixedLift Z ZS a ≃* FixedLiftModel := Classical.choice <| by
  obtain ⟨g, hg, hg2, hactor⟩ := exists_inner_involution d hU a haK haU ha
  have hquad (x : closureU Z ZS) : x ^ 2 = 1 ↔
      BinaryNaturalDual.quadratic (coordinateProjection d x).toAdd = 0 := by
    exact (show x ^ 2 = 1 ↔ (x : G) ^ 2 = 1 from
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩).trans (hsquare x)
  obtain ⟨e⟩ := BinaryLinearThree.TransvectionFixedLift.nonempty_equiv_preimage
    (coordinateProjection d) (coordinateProjection_surjective d)
    (coordinateProjection_ker d hcenter) hquad g hg hg2
  exact ⟨(equiv_coordinatePreimage d a g hactor).trans e⟩

/-- Multiplication constructs the actual E₈ × D₈ product once the fixed lift
has been recognized. The constructor below discharges this explicit E₄ × D₈
premise using square compatibility. -/
noncomputable def localProductEquiv_of_fixedLiftEquiv (d : RecognizedAction T Z ZS V t)
    (hU : closureU Z ZS = coreQ Z)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (hZV : Z ≤ V) (hUcard : Nat.card (closureU Z ZS) = 128)
    (hW : Nat.card (closureU Z ZS ⊓ V : Subgroup G) = 8) (hV : Nat.card V = 16)
    (hUV : closureU Z ZS ≤ normalizer (V : Set G))
    (himage : Nat.card (actionOnV hUV).range = 4)
    (a : centralizerH Z) (haV : (a : G) ∈ V) (haK : (a : G) ∈ residualK Z)
    (haU : (a : G) ∉ closureU Z ZS) (ha : orderOf (a : G) = 2)
    (eA : fixedLift Z ZS a ≃* FixedLiftModel) :
    (fixedLift Z ZS a ⊔ V : Subgroup G) ≃* CentralProductModel :=
  localProductEquiv_of_hyperplane (fixedLift Z ZS a) V a ha
    (fun h => haU (le_closure a h)) haV
    (centralizes d hU hcenter hZV hUcard hW hUV himage a haV haK haU ha)
    (hyperplane_card d hU hcenter hZV hUcard hW hV hUV himage a haV haK haU ha) eA

/-- The actual local product U_a V is E₈ × D₈, conditional only on the earlier
source geometry and the permitted square-coordinate identity. Both the fixed
lift recognition and the hyperplane generation are proved, not assumed. -/
noncomputable def localProductEquiv_of_square_zero (d : RecognizedAction T Z ZS V t)
    (hU : closureU Z ZS = coreQ Z)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (hZV : Z ≤ V) (hUcard : Nat.card (closureU Z ZS) = 128)
    (hW : Nat.card (closureU Z ZS ⊓ V : Subgroup G) = 8) (hV : Nat.card V = 16)
    (hUV : closureU Z ZS ≤ normalizer (V : Set G))
    (himage : Nat.card (actionOnV hUV).range = 4)
    (hsquare : ∀ x : closureU Z ZS, (x : G) ^ 2 = 1 ↔
      BinaryNaturalDual.quadratic (d.coordinates (QuotientGroup.mk' _ x)).toAdd = 0)
    (a : centralizerH Z) (haV : (a : G) ∈ V) (haK : (a : G) ∈ residualK Z)
    (haU : (a : G) ∉ closureU Z ZS) (ha : orderOf (a : G) = 2) :
    (fixedLift Z ZS a ⊔ V : Subgroup G) ≃* CentralProductModel :=
  localProductEquiv_of_fixedLiftEquiv d hU hcenter hZV hUcard hW hV hUV himage
    a haV haK haU ha (fixedLiftEquiv_of_square_zero d hU hcenter hsquare a haK haU ha)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial.FixedLift
