module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.FullNormalizer.QuaternionExchange.MarkedRootGeometry.RootAndFourGroups
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.FullNormalizer.QuaternionExchange.MarkedRootGeometry.PermutationContract
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.FullNormalizer.QuaternionExchange.MarkedRootGeometry.PermutationGeometry
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.SymmetricSix.LocalGluing.FixedLineCompatibility.SquareRoots

/-!
# Assembly of the marked root geometry

The cubic fixed line has order two, so it supplies the pivot b. The root
calculation constructs w and proves both literal even-fusion identities.
The marked permutation calculation supplies the cycle type and centralizer
generation. The final theorem discharges square-root containment using the
normal quaternion factors and applies the permutation calculation in the
given marked S₆. It constructs all fields of the marked root geometry from
the stated source inputs, for either allowed choice of the inverter u.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemmas 4.6 and 4.8, pp.40–41.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.QuaternionExchange

open Subgroup LocalGluing

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h}

/-- The actual root and even-four calculations assemble with the two
independent earlier-source and marked-permutation inputs. -/
public theorem nonempty_markedGeometry_of_square_roots_and_permutation_geometry
    (d : FusionEightData z) (s : SymmetricSixData h a)
    (roots : ∀ v : G, v ^ 2 = z → v ∈ coreInG z)
    (permutation : ∀ b : G, b ∈ s.evenFusion z → b ≠ 1 →
      PivotPermutationGeometry s b) : Nonempty (MarkedGeometry s) := by
  have p := (cubicFourData_pair h d s.commutingCubicData).1
  obtain ⟨b,hb1,_⟩ := (Nat.card_eq_two_iff' (1 : fixedLine z s.u (cubicInG h))).mp
    p.line_card
  have hb : (b : G) ∈ fixedLine z s.u (cubicInG h) := b.property
  have hbne : (b : G) ≠ 1 := fun he => hb1 (Subtype.ext he)
  have hbEven : (b : G) ∈ s.evenFusion z :=
    ⟨p.moved_le hb.1,movedFour_le_markedAlternating s hb.1⟩
  obtain ⟨r,hr,hrz⟩ := root_and_even_z_of_square_roots d roots s b hb hbne
  have hp := permutation b hbEven hbne
  have hrt := evenFusion_pivot_eq_of_square_roots d roots s b hb hbne
  rw [← hr] at hp hrt
  exact ⟨{
    toRootData := r
    t_mem := hp.t_mem
    t_cycleType := hp.t_cycleType
    even_z := hrz
    even_t := hrt
    generated := hp.generated }⟩

/-- The marked root geometry of source 4.6 and 4.8, including both literal
even fusion four-groups and generation by the two marked centralizers.
Normality of the quaternion factors supplies square-root containment;
the given symmetric-six marking supplies the pivot permutation geometry. -/
public theorem nonempty_markedGeometry (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (d : FusionEightData z)
    (a : SourceGeometry h) (s : SymmetricSixData h a) : Nonempty (MarkedGeometry s) := by
  exact nonempty_markedGeometry_of_square_roots_and_permutation_geometry d s
    (square_root_mem_coreInG h hn a) (pivotPermutationGeometry s d)

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.QuaternionExchange
