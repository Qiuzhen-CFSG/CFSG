module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six.Preliminaries
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six.Direct
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six.Complement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Stages

/-!
# The six-step case of the selected critical path

For the original critical pair and its selected centralizer path, b = 6
gives actual vertices at positions 1, 2 and 5. Split according to whether
R₀ lies in the middle Z-layer. The contained branch constructs the native
seed, applies (1.7)(ii), and contradicts criticality through middle-vertex
generation. The complementary branch proves the fixed cover and both
commutator bounds, giving the involution contradiction. Both branches retain
the same selected path and discharge every additional local premise.

The resulting exclusion plugs into the existing selection assembly, where
the initial bound b >= 6 gives b > 6. Existence of the centralizer choice
remains the independent step-(4) input to that assembly.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(5), pp.884--885.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    {geometry : MS93.Geometry R}

/-- Source (4.3.2)(5): the selected critical path cannot have length six.
The assumption b = 6 supplies the distance bounds needed in both branches. -/
theorem b_ne_six (source : LocalSource L R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (choice : CentralizerChoice p) : geometry.b R ≠ 6 := by
  intro h6
  let path := sixPath p h6
  by_cases hcontained : radiusCommutator p.a p.a' ≤ Z R path.middle
  · exact Six.Direct.false_of_radius_le_middle_Z source modules initial facts bad
      choice path hcontained
  · exact Six.Complement.false_of_not_le_middle_Z source modules initial facts bad
      choice path hcontained

/-- Discharge the exclusion stage of the existing selection assembly.
Only the independent centralizer-choice existence from source (4) remains. -/
theorem exists_centralizerChoice_of_selection (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (selection : ∃ q : Counterexample geometry, Nonempty (CentralizerChoice q)) :
    ∃ q : Counterexample geometry, 6 < geometry.b R ∧ Nonempty (CentralizerChoice q) :=
  exists_centralizerChoice_of_stages hb initial p bad selection
    (b_ne_six source modules initial facts)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection
