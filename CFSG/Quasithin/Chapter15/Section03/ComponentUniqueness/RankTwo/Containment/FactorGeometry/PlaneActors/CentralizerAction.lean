module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.Geometry
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.ActorData
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.CentralizerAction.Quotient
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.CentralizerAction.Properness
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.CentralizerAction.PlaneImage
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# The complementary actor in CaseTwo

The rank-two quotient constructs an S-invariant complementary residual
to O²(C_{Y₊}(V₂)). Since Y₊ centralizes V₁, this left residual centralizes
all of V. Removing it from the generating pair preserves the displacement
of V and V₂. The full residual image excludes Y₊ = Y.

The literal cubic coordinate calculation from the compatible action and
15.3.7 proves that the left actor has three-part three and that Y₊ generates
V₂ by commutators with both V and V₂. Combining these facts with the
quotient construction gives the CaseTwo actor pair. The original
conditional helper is retained; `caseTwo_planeActors` discharges all three
of its action premises. Neither V ≤ M nor the additional core equality
in 15.3.36(2) is needed for this construction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.7,
15.3.10(2), 15.3.36, and 15.3.39–40, printed pp.1122–1123, 1135,
and 1137–1138.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
variable {G : Type*} [Group G] [Finite G]

/-- The remaining action calculation supplies three numerical and displacement
facts. The invariant complementary actor is constructed here, not assumed. -/
theorem caseTwo_planeActors_of_action {M Mc V Yplus : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M)
    (hcase : CaseTwo M (residualY M Mc) (planeStabilizer T (d.plane 1))
      (d.plane 1) Yplus)
    (h9 : Nat.card (Yplus ⧸ pCore 2 Yplus) = 9)
    (hshadow : RankTwoShadow Yplus (planeStabilizer T (d.plane 1)))
    (hleft : 3 ^ (Nat.card (centralizingFactor Yplus
      (d.plane (Multiplicative.ofAdd (1 : ZMod 2))))).factorization 3 = 3)
    (hplane : ⁅V, Yplus⁆ = d.plane (Multiplicative.ofAdd (1 : ZMod 2)))
    (hself : ⁅d.plane (Multiplicative.ofAdd (1 : ZMod 2)), Yplus⁆ =
      d.plane (Multiplicative.ofAdd (1 : ZMod 2)))
    (h7 : d.image (residualY M Mc) =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    Nonempty (PlaneActorPair M (residualY M Mc) Yplus (planeStabilizer T (d.plane 1))
      V (d.plane 1) (d.plane (Multiplicative.ofAdd (1 : ZMod 2)))) := by
  have hproper := caseTwo_ne_residualY_of_full_image d 1 hcase h7
  have hchoice : Hypothesis15310 M (residualY M Mc) (planeStabilizer T (d.plane 1))
      (d.plane 1) Yplus := Or.inr hcase
  have hYM : Yplus ≤ M := (yplus_le_residualY_of_choice hchoice).trans
    (Chapter14.SourcePreliminaries.sourceResidual_le M Mc)
  have hp := yplus_perfect_of_choice hchoice
  have hs := planeStabilizer_normalizes_yplus d T hTM 1 hchoice
  have hyv := perfect_normalizes_planes d hYM hp (Multiplicative.ofAdd (1 : ZMod 2))
  have hsv := planeStabilizer_normalizes_planes d T hTM 1 (Multiplicative.ofAdd (1 : ZMod 2))
  obtain ⟨han,has⟩ := plane_left_actor_normal_invariant hyv hs hsv
  obtain ⟨B,hBY,hBn,hBS,hBp,hB3,hgen⟩ := rankTwoShadow_residual_complement hp h9
    (T.isPGroup'.to_le inf_le_left) hs hshadow (centralizingFactor_le_left _ _) han has
    (centralizingFactor_isPPerfect _ _) hleft
  have hC1 : Yplus ≤ centralizer (d.plane 1 : Set G) := by
    rw [hcase.2]
    exact (map_subtype_le _).trans inf_le_right
  have hAC : centralizingFactor Yplus (d.plane (Multiplicative.ofAdd (1 : ZMod 2))) ≤
      centralizer (V : Set G) := by
    apply le_centralizer_iff.mpr
    apply (natural_planes_sup d (i := 1) (j := Multiplicative.ofAdd (1 : ZMod 2)) (by decide)).ge.trans
    exact sup_le
      (le_centralizer_iff.mp ((centralizingFactor_le_left _ _).trans hC1))
      (le_centralizer_iff.mp (centralizingFactor_le _ _))
  exact ⟨{
    right := B
    right_le := le_inf hBY (le_inf (hBY.trans hYM) (hBY.trans hC1))
    right_normal := hBn
    right_invariant := hBS
    right_perfect := hBp
    right_three_part := hB3
    left_three_part := hleft
    generate := hgen
    plane := (commutator_eq_of_centralizing_sup hgen.symm hAC
      (hBY.trans (hYM.trans d.normalizes))).trans hplane
    plane_self := (commutator_eq_of_centralizing_sup hgen.symm
      (centralizingFactor_le _ _) (hBY.trans hyv)).trans hself
    other_plane := fun h => (hproper h).elim }⟩
/-- Construct both residual plane actors in CaseTwo from the actual natural
action, full residual image, order-nine two-core quotient and rank-two shadow.
The centralizer line and its invariant complementary residual are proved,
with no assumed actor or factor identification. -/
theorem caseTwo_planeActors {M Mc V Yplus : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M)
    (hcase : CaseTwo M (residualY M Mc) (planeStabilizer T (d.plane 1))
      (d.plane 1) Yplus)
    (h9 : Nat.card (Yplus ⧸ pCore 2 Yplus) = 9)
    (hshadow : RankTwoShadow Yplus (planeStabilizer T (d.plane 1)))
    (h7 : d.image (residualY M Mc) =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    Nonempty (PlaneActorPair M (residualY M Mc) Yplus (planeStabilizer T (d.plane 1))
      V (d.plane 1) (d.plane (Multiplicative.ofAdd (1 : ZMod 2)))) := by
  obtain ⟨hleft, hplane, hself⟩ := caseTwo_action_of_full_image d
    (i := 1) (j := Multiplicative.ofAdd (1 : ZMod 2)) (by decide) hcase h7 h9
  exact caseTwo_planeActors_of_action d T hTM hcase h9 hshadow hleft hplane hself h7

end CFSG.Quasithin.Chapter15.Section03.RankTwo
