module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.Center
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.SmallCenter

/-!
# From the faithful natural row to the original two-core quotient

The earlier natural row identifies H/C_H(U-hat) with the semilinear SL2(4)
model and intertwines its literal action. It does not yet identify this
kernel with O2(H). The model has elementary two-rank two and U-hat has
order sixteen. The original parabolic count, after centerlessness, forces
the tilded center to have order two. The small-center kernel argument then
supplies the missing kernel equality and transports the same coordinates
through H/O2(H). SourceAction applies them to the original LocalStructure.

This proves the passage from 14.3.23(2)(ii) to the action used by 14.3.32.
Selection of that row remains with qt-d-hs-action-source. No isomorphism
or equivariance is inferred from an unconnected family name.

Source: Aschbacher--Smith, 14.3.23(2)(ii), 14.3.32(1,3), pp.1000,1003--1004.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The natural row is first an identification of the faithful action image;
the two-core is not built into this earlier conclusion. -/
@[expose] def DottedNaturalCoordinates (F : InvariantFlag T V 3) : Prop :=
  ∃ (e : Hdot F F.uhatAction ≃*
        Representation.SL2FourNatural.SemilinearNormalizer.specialField)
    (c : F.Uhat ≃* Multiplicative Representation.SL2FourNatural.V),
    ∀ (h : F.H) (x : F.Uhat),
      (c (F.uhatAction h x)).toAdd =
        (e (QuotientGroup.mk' F.uhatAction.ker h)).val (c x).toAdd

/-- Convert the actual natural action row into the published coordinates on
H/O₂(H), deriving the kernel equality from the source order calculation. -/
theorem source_naturalCoordinates_of_dotted (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hc : DottedNaturalCoordinates F) : NaturalCoordinates F := by
  obtain ⟨e, c, he⟩ := hc
  have hcard : Nat.card F.Uhat = 16 := by
    rw [Nat.card_congr c.toEquiv]
    change Nat.card Representation.SL2FourNatural.V = 16
    rw [Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_vector]
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨β, _, b, _, hcuts, _, _⟩ := F.exists_marked_naturalFlag L chosen.normalizes h.full_L_action
  obtain ⟨g, hgP, hgH, _⟩ := SetupFlagGeometry.exists_adjacent_lift F (by decide)
    chosen.normalizes (show (T : Subgroup G) ≤ normalizer (V : Set G) from F.last ▸ F.invariant 3)
    (h.binarySeedAction_surjective F) β b hcuts
  let := source_actor_elementary d earlier hq chosen structural alternatives F hne g hgP hgH
  have hr : primeRank 2 (Hdot F F.uhatAction) ≤ 2 := by
    rw [primeRank_equiv 2 (e.trans Representation.SL2FourNatural.SemilinearNormalizer.symmetricFiveEquiv)]
    exact Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two
  have hX : Nat.card (dotImage F F.uhatAction (F.X g)) ≤ 4 :=
    (primeRank_le_iff_elementary_card_le (Hdot F F.uhatAction)).mp hr _ inferInstance
  have ht := (source_four_dimensional_orders d earlier hq chosen structural alternatives F hne hZ hI
    hcard g hgP hgH hX).2.2.2
  have hk := source_small_center_kernel d earlier hq chosen structural alternatives F ht.le
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans e, c, ?_⟩
  intro a x
  exact he a x

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
