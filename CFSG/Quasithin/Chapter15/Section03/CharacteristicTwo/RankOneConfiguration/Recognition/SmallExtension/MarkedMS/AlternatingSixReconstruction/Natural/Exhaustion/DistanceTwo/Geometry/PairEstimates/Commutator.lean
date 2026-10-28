module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates.Data
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The paired commutator is abelian before its exponent is known

Both orbit-derived subgroups lie in the central edge layer. The paired
commutator lies in both orbits, so two cyclic triple commutators vanish.
The three-subgroups lemma makes the paired commutator abelian. Consequently
only the squares of its literal generators remain for the source calculation;
closure then gives elementary abelianness. No Frattini disjointness or
natural subgroup complement is used.

Source: MS93 (3.6), the paired calculation on printed p.871.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} {geo : Geometry R}
namespace EarlyPair
variable (o : EarlyPair R geo)

/-- Common central attachments do not prevent the paired commutator itself
from being abelian. They may still obstruct exponent two. -/
theorem commutator_commutative (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hl : LocalCalculations R geo) :
    IsMulCommutative (⁅criticalOrbit R o.c o.b,o.opposite⁆ : Subgroup (FreeAmalgam R)) := by
  let A := criticalOrbit R o.c o.b
  let B := o.opposite
  let D := ⁅A,B⁆
  have hAQ : A ≤ Q R (alpha R) := by
    rw [Q_alpha R hp hQR]
    exact map_mono o.orbit_le_core
  have hAG : A ≤ stabilizer R o.c :=
    hAQ.trans (DistanceTwo.NaturalCore.Q_le_endpoint_stabilizer o.adjacent_left o.adjacent_right)
  have hBG : B ≤ stabilizer R (alpha R) :=
    (o.opposite_le.trans
      (Q_le_adjacent_h R (DistanceTwo.NaturalCore.edge_color o.adjacent_left)
        o.adjacent_right)).trans (fun _ hx => hx.2 _ (adjacent_symm R o.adjacent_left))
  have hDA : D ≤ A := le_normalizer_iff_commutator_le_left.mp
    (hBG.trans (criticalOrbit_normalized o.c o.b))
  have hDB : D ≤ B := le_normalizer_iff_commutator_le_right.mp
    (hAG.trans o.opposite_normalized)
  have hAA : ⁅A,A⁆ ≤ Z R o.b :=
    (commutator_mono hAQ le_rfl).trans
      (hl.commutator_edge o.c o.b o.critical o.adjacent_left o.adjacent_right)
  have hBB : ⁅B,B⁆ ≤ Z R o.b :=
    (commutator_mono o.opposite_le le_rfl).trans o.opposite_commutator
  have hc0 := critical_endpoint_color R (alpha R) rfl _ o.critical
  have hcol := DistanceTwo.NaturalCore.edge_color o.adjacent_left
  have hZa : Z R o.b ≤ Z R (alpha R) := by
    simp only [Z,show color R (alpha R) = false from rfl,hcol,
      Bool.true_eq_false,if_true,if_false]
    exact le_iSup_of_le o.b (le_iSup_of_le o.adjacent_left le_rfl)
  have hZc : Z R o.b ≤ Z R o.c := by
    simp only [Z,hc0,hcol,Bool.true_eq_false,if_true,if_false]
    exact le_iSup_of_le o.b (le_iSup_of_le o.adjacent_right le_rfl)
  have hZA : ⁅Z R o.b,A⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono hZa hAQ).trans_eq (Z_centralizes_Q R (alpha R) rfl))
  have hZB : ⁅Z R o.b,B⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono hZc o.opposite_le).trans_eq (Z_centralizes_Q R o.c hc0))
  have h1 : ⁅⁅D,A⁆,B⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono ((commutator_mono hDA le_rfl).trans hAA) le_rfl).trans_eq hZB)
  have h2 : ⁅⁅B,D⁆,A⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono ((commutator_mono le_rfl hDB).trans hBB) le_rfl).trans_eq hZA)
  exact commutator_self_eq_bot_iff.mp (commutator_commutator_eq_bot_of_rotate h2 h1)

/-- The source square calculation on actual commutator generators suffices
for the exact elementary-commutator field. -/
theorem elementary_commutator_of_squares (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hl : LocalCalculations R geo)
    (hs : ∀ a ∈ criticalOrbit R o.c o.b, ∀ b ∈ o.opposite, ⁅a,b⁆ ^ 2 = 1) :
    IsElementaryAbelian 2 (⁅criticalOrbit R o.c o.b,o.opposite⁆ : Subgroup (FreeAmalgam R)) := by
  let := o.commutator_commutative hp hQR hl
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro x ⟨a,ha,b,hb,rfl⟩
  exact hs a ha b hb

end EarlyPair
end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
