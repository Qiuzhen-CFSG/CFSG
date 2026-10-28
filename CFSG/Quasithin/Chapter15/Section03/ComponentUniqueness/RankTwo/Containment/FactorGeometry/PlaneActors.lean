module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.Geometry
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.FullAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.CentralizerAction
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.Statements

/-!
# The two residual plane actors

The genuine natural action and the source choice in 15.3.10 supply all the
plane normalization and nontriviality premises used by OrbitEquality. They
also supply the containment, relative normality, invariance and
two-perfectness of Y₁ = O²(C_{Y₊}(V₂)).

The full residual image from 15.3.7 and the actual order-nine two-core
quotient construct the actors in both cases of 15.3.10. When Y₊ = Y,
the two residual centralizers are the actors. In CaseTwo, the rank-two
shadow in 15.3.36 supplies an invariant complementary line, whose lifted
two-residual is the right actor. Both three-parts and all the required
commutator identities follow from the compatible natural action.

The final adapter accepts the genuine first alternative of 15.3.11(5),
including both conclusions of 15.3.36. Only its rank-two shadow is needed
for actor selection. The order-nine quotient remains an explicit input:
the parent supplies it from 15.3.12(2) in the strict-orbit branch and from
the corrected three-part version of 15.3.37 in the noncontainment branch.
Neither source containment nor any identification with component factors
is assumed or asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.7,
15.3.10–12, 15.3.36 and 15.3.39–40, printed pp.1122–1125 and 1135–1138.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
variable {G : Type*} [Group G] [Finite G]

/-- The five plane premises of the OrbitEquality argument, proved with the
actual S = N_T(V₁) and the source definition of Y. Either coordinate plane
can be used as V₂. No actor-existence premise is needed for these facts. -/
theorem source_orbit_plane_facts {M Mc V Yplus : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M)
    (i j : OrthogonalPlaneIndex)
    (hchoice : Hypothesis15310 M (residualY M Mc) (planeStabilizer T (d.plane i))
      (d.plane i) Yplus) :
    planeStabilizer T (d.plane i) ≤ normalizer (Yplus : Set G) ∧
      planeStabilizer T (d.plane i) ≤ normalizer (d.plane j : Set G) ∧
      Yplus ≤ normalizer (d.plane j : Set G) ∧
      V ≤ planeStabilizer T (d.plane i) ∧ d.plane j ≠ ⊥ := by
  have hYM : Yplus ≤ M := (yplus_le_residualY_of_choice hchoice).trans
    (Chapter14.SourcePreliminaries.sourceResidual_le M Mc)
  exact ⟨planeStabilizer_normalizes_yplus d T hTM i hchoice,
    planeStabilizer_normalizes_planes d T hTM i j,
    perfect_normalizes_planes d hYM (yplus_perfect_of_choice hchoice) j,
    d.le_planeStabilizer T hTM hVM i, natural_plane_ne_bot d j⟩

/-- The left actor has the required containment, relative normality,
S-invariance and two-perfectness before the quotient splitting is made. -/
theorem source_left_actor_facts {M Mc V Yplus : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (i j : OrthogonalPlaneIndex)
    (hchoice : Hypothesis15310 M (residualY M Mc) (planeStabilizer T (d.plane i))
      (d.plane i) Yplus) :
    centralizingFactor Yplus (d.plane j) ≤
        Yplus ⊓ (M ⊓ centralizer (d.plane j : Set G)) ∧
      ((centralizingFactor Yplus (d.plane j)).subgroupOf Yplus).Normal ∧
      planeStabilizer T (d.plane i) ≤
        normalizer (centralizingFactor Yplus (d.plane j) : Set G) ∧
      IsPPerfect 2 (centralizingFactor Yplus (d.plane j)) := by
  have hYM : Yplus ≤ M := (yplus_le_residualY_of_choice hchoice).trans
    (Chapter14.SourcePreliminaries.sourceResidual_le M Mc)
  have hYV := perfect_normalizes_planes d hYM (yplus_perfect_of_choice hchoice) j
  obtain ⟨hn, hi⟩ := plane_left_actor_normal_invariant hYV
    (planeStabilizer_normalizes_yplus d T hTM i hchoice)
    (planeStabilizer_normalizes_planes d T hTM i j)
  exact ⟨le_inf (centralizingFactor_le_left _ _)
    (le_inf ((centralizingFactor_le_left _ _).trans hYM) (centralizingFactor_le _ _)),
    hn, hi, centralizingFactor_isPPerfect _ _⟩

/-- Construct the two plane actors for either source choice of Y₊. The
planes, stabilizer and original residual Y are the literal source objects.
The rank-two shadow is needed only in CaseTwo; the order-nine quotient
always refers to Y₊ itself. -/
theorem source_planeActorPair {M Mc V Yplus : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M)
    (hchoice : Hypothesis15310 M (residualY M Mc) (planeStabilizer T (d.plane 1))
      (d.plane 1) Yplus)
    (h7 : d.image (residualY M Mc) =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h9 : Nat.card (Yplus ⧸ pCore 2 Yplus) = 9)
    (h36 : RankTwoShadow Yplus (planeStabilizer T (d.plane 1))) :
    Nonempty (PlaneActorPair M (residualY M Mc) Yplus
      (planeStabilizer T (d.plane 1)) V (d.plane 1)
      (d.plane (Multiplicative.ofAdd (1 : ZMod 2)))) := by
  rcases hchoice with h | h
  · subst Yplus
    obtain ⟨a, _⟩ := planeActorPair_of_fullAction d T hTM hVM h7 h9
    exact ⟨a⟩
  · exact caseTwo_planeActors d T hTM h h9 h36 h7

/-- The actor construction with explicitly identified source subgroups.
The equalities prevent replacing either plane by an unrelated four-group
or S by an arbitrary subgroup of T. -/
theorem source_planeActorPair_of_identifications {M Mc Y Yplus S V V₁ V₂ : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M)
    (hY : Y = residualY M Mc) (hV₁ : V₁ = d.plane 1)
    (hV₂ : V₂ = d.plane (Multiplicative.ofAdd (1 : ZMod 2)))
    (hS : S = planeStabilizer T V₁)
    (hchoice : Hypothesis15310 M Y S V₁ Yplus)
    (h7 : d.image Y = Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h9 : Nat.card (Yplus ⧸ pCore 2 Yplus) = 9)
    (h36 : RankTwoShadow Yplus S) :
    Nonempty (PlaneActorPair M Y Yplus S V V₁ V₂) := by
  subst Y V₁ V₂ S
  exact source_planeActorPair d T hTM hVM hchoice h7 h9 h36

/-- Apply the construction to the genuine source local data and the first
alternative of 15.3.11(5). That earlier conclusion retains the actual
Frattini denominator and core equality of 15.3.36; actor existence is
proved by the two branch constructions, not included in the input. -/
theorem source_planeActorPair_of_rankTwoCase (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G)
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h11 : OutsideStructure.RankTwoCase d I)
    (h9 : Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9) :
    Nonempty (PlaneActorPair d.M d.Y d.Yplus d.S d.V d.V₁ d.V₂) := by
  apply source_planeActorPair d.action d.T d.sylow_le
    (localModule_le d.T d.sylow_le) d.choice h7 h9
  exact h11.2.1

end CFSG.Quasithin.Chapter15.Section03.RankTwo
