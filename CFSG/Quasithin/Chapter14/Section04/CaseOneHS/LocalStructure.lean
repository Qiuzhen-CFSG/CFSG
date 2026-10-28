module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Action
public import Theory.GroupTheory.QuaternionCentralProductCyclicFour

/-!
# Constructing the HS local structure from the source action

Natural F₄² coordinates compute |U/Z(U)| = 16 and the action kernel.
A cyclic center of order four then gives |U| = 64. The source closure
theorem identifies Φ(U) with the marked point of order two, allowing the
lower-layer factor theorem to construct the actual (Q₈ * Q₈) * C₄ factors.
Thus the action output supplies LocalStructure once Z(I₂) = 1 is proved.

This is conditional assembly, not a proof of the missing 14.3.31--32 source
arguments. Centerlessness and ActionStructure remain to be established
from the selected counterexample; their final discharge stays with the
local-structure task. The parent HS source assembly additionally owns
14.3.33 and the application of the independent I.4.8 recognition theorem.

Source: Aschbacher--Smith, 14.3.31--32, printed pp.1002--1004; the Frattini
input is the original 12.8.4 as supplied by CaseOneGeometry.source_closure.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- The center and its natural quotient give the order of the actual U. -/
theorem ActionStructure.card (F : InvariantFlag T V 3) (a : ActionStructure F) :
    Nat.card F.U = 64 := by
  rw [(center F.U).card_eq_card_quotient_mul_card_subgroup,
    a.natural.card_uhat F, a.center_card]

omit [Finite G] in
/-- The literal marked point, included in U, has order two. -/
theorem frattini_card_of_point (F : InvariantFlag T V 3)
    (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U) :
    Nat.card (frattini F.U) = 2 := by
  have hp : F.Vi 1 ≤ F.U := (F.le_seed 1).trans (le_conjugateSpanBy V F.H)
  rw [hphi, Nat.card_congr (subgroupOfEquivOfLe hp).toEquiv]
  simpa using F.card 1 (by decide)

/-- Construct embedded central-product factors from the source Frattini equality. -/
theorem ActionStructure.coreShape (F : InvariantFlag T V 3) (a : ActionStructure F)
    (hp : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U) :
    HigmanSims.CoreShape F.U := by
  let := a.center_cyclic
  exact exists_quaternionCentralProduct_cyclicFour hp (a.card F) a.center_card
    (frattini_card_of_point F hphi)

/-- Supply the kernel and central-product fields using the original source data.
The two remaining source obligations are explicit premises, not asserted results. -/
theorem localStructure_of_centerless_action (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hcenterless : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (action : ActionStructure F) :
    LocalStructure L F := by
  obtain ⟨hp, hphi, _⟩ :=
    CaseOneGeometry.source_closure d earlier hq chosen structural alternatives F hne
  exact {
    centerless := hcenterless
    core_shape := action.coreShape F hp hphi
    natural := action.natural
    kernel := action.natural.kernel F
    component := action.component }
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
