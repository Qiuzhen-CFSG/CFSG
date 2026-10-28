module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six.Complement.FixedPreimage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six.Complement.RadiusNatural
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six.Complement.FixedComparison

/-!
# The complementary case of the six-step critical path

The radius commutator lies in the starting natural group and in the middle
fixed preimage. Their intersection is the first middle edge plane. When
the radius group is outside the middle Z-layer, this bound proves predecessor
movement and identifies its commutator with both middle edge planes.

The compatible opposite actions then give the fixed cover modulo the actual
middle B. Together with the predecessor bound, this supplies the existing
involution contradiction. All intermediate containment, movement and equal-edge
premises are discharged here. The path keeps first = 1, middle = 2,
choice.t = 3, p.c = 4 and last = 5. The independent contained branch and
the final b ≠ 6 assembly belong to the parent module.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(5), pp.884--885.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.Complement
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    {geometry : MS93.Geometry R} {p : Counterexample geometry}

/-- In the complementary case the radius commutator is both middle edge
planes, with the initial radius estimate proved from the supplied actions. -/
theorem radius_commutator_eq_edges (source : LocalSource L R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (choice : CentralizerChoice p) (path : Selection.SixPath p)
    (hout : ¬ radiusCommutator p.a p.a' ≤ Z R path.middle) :
    ⁅radiusCommutator p.a p.a', Q R path.middle⁆ = edgeDisplacement path.middle choice.t ∧
      edgeDisplacement path.middle choice.t = edgeDisplacement path.middle path.first :=
  radius_commutator_eq_edges_of_bound source modules initial facts bad choice path hout
    (radius_commutator_le_first_edge source modules initial facts bad path)

/-- The fixed cover on printed p.884, using the actual opposite coordinates
after discharging predecessor movement and equality of the edge planes. -/
theorem fixed_cover (source : LocalSource L R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (choice : CentralizerChoice p) (path : Selection.SixPath p)
    (hout : ¬ radiusCommutator p.a p.a' ≤ Z R path.middle) :
    Z R p.a ≤ Z R p.c ⊔ B R path.middle (geometry.Z_normal path.middle) := by
  obtain ⟨ip⟩ := initial p
  have hbound := radius_commutator_le_first_edge source modules initial facts bad path
  exact fixed_cover_of_movement_and_equal_edges source modules initial facts bad choice path
    (predecessor_moving_of_bound source modules facts ip path hout hbound)
    (radius_commutator_eq_edges source modules initial facts bad choice path hout).2

/-- The predecessor displacement lies in the first middle edge plane,
as required in the product-commutator bound on printed p.885. -/
theorem predecessor_bound (source : LocalSource L R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (choice : CentralizerChoice p) (path : Selection.SixPath p)
    (hout : ¬ radiusCommutator p.a p.a' ≤ Z R path.middle) :
    ⁅Z R p.c, Q R path.middle⁆ ≤ edgeDisplacement path.middle path.first :=
  predecessor_bound_of_radius_bound source modules initial facts bad choice path hout
    (radius_commutator_le_first_edge source modules initial facts bad path)

/-- The complete complementary branch of (4.3.2)(5). The fixed cover and
both commutator bounds have been proved; no movement or displacement premise
remains for the parent b ≠ 6 assembly. -/
theorem false_of_not_le_middle_Z (source : LocalSource L R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (choice : CentralizerChoice p) (path : Selection.SixPath p)
    (hout : ¬ radiusCommutator p.a p.a' ≤ Z R path.middle) : False :=
  path.false_of_cover_and_predecessor_bound source modules initial facts bad
    (fixed_cover source modules initial facts bad choice path hout)
    (predecessor_bound source modules initial facts bad choice path hout)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.Complement
