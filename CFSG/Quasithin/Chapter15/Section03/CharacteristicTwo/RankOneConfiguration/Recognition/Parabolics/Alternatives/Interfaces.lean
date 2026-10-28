module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Marking
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.Setup
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.QuasisimpleModels
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.Defs
public import Theory.SpecificGroups.SymplecticFour.Flag
public import Theory.AtlasPort.LinearGroups.G2.LieParabolicSetup

/-!
# The marked output of the rank-one parabolic classification

The three alternatives specify an actual PSL₂ Borel, one of the two
standard minimal parabolics of L₃(2), Sp₄(2)′ or G₂(2)′, or an eight-point
permutation marking. Diagram triviality means that conjugation preserves
each of the two component-conjugacy classes of standard parabolics.
The small symplectic and G₂ carriers are literally the derived subgroups.

The eight-point output retains a simultaneous comparison of the even
pair stabilizer with the middle-node Lie parabolic and the even four-point
stabilizer with the end-node parabolic. Their intersection is the Borel,
as proved below, and the actual Sylow image is marked by the full flag
stabilizer. OuterMiddleNodeData is an intermediate geometric output;
it does not assume an S₈ equivalence or a permutation marking.

These are output definitions, not existence assertions. The complete
source theorem still requires the model classification, parabolic sieve,
and marked exceptional-isomorphism construction. FFComponentModel reuses
the existing complete group list with actual isomorphisms and the genuine
central-quotient convention for the triple cover of A₆.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.5–6,
printed pp.104–105, and 15.3.28–32, pp.1131–1133 (PDF pp.1148–1150).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics
open BinaryLinear.InvariantNodeActions (Basis minimalParabolic cutStabilizer mem_cutStabilizer)
open BinaryLinear.OuterCyclic (LinearGroup slEquivLinear)
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals

/-- The existing finite binary field convention, including its positive degree and actual cardinality. -/
abbrev ClassificationField :=
  CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.BinaryField

/-- The full earlier FF group list; this abbreviation asserts no classification. -/
abbrev FFComponentModel (H : Type*) [Group H] : Prop :=
  CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.QuasisimpleModel H

/-- The two binary A₂ minimal parabolics in the actual special linear carrier. -/
noncomputable def linearThreeParabolic (i : Fin 2) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
  (minimalParabolic (Pi.basisFun (ZMod 2) (Fin 3)) i).comap (slEquivLinear 3).toMonoidHom

/-- The point and plane parabolics restricted to the genuine Sp₄(2) derived subgroup. -/
noncomputable def symplecticDerivedParabolic (i : Fin 2) :
    Subgroup (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) :=
  (if i = 0 then Theory.SpecificGroups.SymplecticFour.pointParabolic
    else Theory.SpecificGroups.SymplecticFour.planeParabolic).subgroupOf _

/-- The two root parabolics restricted to the genuine G₂(2) derived subgroup. -/
def g2DerivedParabolic (i : Fin 2) :
    Subgroup (commutator (Atlas.G2.Model (ZMod 2))) :=
  (if i = 0 then Atlas.G2.LieParabolicSetup.parabolic₁
    else Atlas.G2.LieParabolicSetup.parabolic₂).subgroupOf _

variable {G : Type*} [Group G]

/-- Embed a model subgroup through the chosen component equivalence and its actual star inclusion. -/
def modelSubgroup (d : LocalData G) (I L : Subgroup G)
    {H : Type*} [Group H] (e : d.starImage I L ≃* H) (P : Subgroup H) :
    Subgroup (d.Star I) :=
  P.map ((d.starImage I L).subtype.comp e.symm.toMonoidHom)

/-- A marked minimal parabolic, with trivial S-action on both labeled parabolic types. -/
structure RankTwoParabolicMarking (d : LocalData G) (I L : Subgroup G)
    (H : Type*) [Group H] (parabolic : Fin 2 → Subgroup H) where
  equiv : d.starImage I L ≃* H
  node : Fin 2
  intersection : ((d.starImage I (d.M ⊓ L)).subgroupOf (d.starImage I L)).map
    equiv.toMonoidHom = parabolic node
  diagram : ∀ s ∈ d.starImage I d.S, ∀ i : Fin 2, ∃ l : H,
    (modelSubgroup d I L equiv (parabolic i)).map (MulAut.conj s).toMonoidHom =
      (modelSubgroup d I L equiv (parabolic i)).map
        (MulAut.conj ((equiv.symm l : d.starImage I L) : d.Star I)).toMonoidHom

/-- The three small alternatives, preserving their actual carriers and derived-group conventions. -/
inductive SmallParabolicMarking (d : LocalData G) (I L : Subgroup G) : Prop
  | linearThree (marking : RankTwoParabolicMarking d I L
      (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) linearThreeParabolic)
  | symplecticDerived (marking : RankTwoParabolicMarking d I L
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) symplecticDerivedParabolic)
  | g2Derived (marking : RankTwoParabolicMarking d I L
      (commutator (Atlas.G2.Model (ZMod 2))) g2DerivedParabolic)

/-- The intrinsic outer A₃ middle-parabolic data to be converted into a marked S₈ action. -/
structure OuterMiddleNodeData (d : LocalData G) (I L : Subgroup G) where
  linear : d.starImage I L ≃* LinearGroup 4
  basis : Basis 3
  intersection : ((d.starImage I (d.M ⊓ L)).subgroupOf (d.starImage I L)).map
    linear.toMonoidHom = minimalParabolic basis 1
  selfCentralizing : centralizer (d.starImage I L : Set (d.Star I)) = ⊥
  outer : ¬ d.starImage I d.S ≤ d.starImage I L

/-- A simultaneous Lie interpretation of the two literal eight-point partition stabilizers. -/
structure EightFlagComparison where
  equiv : alternatingGroup (Fin 8) ≃* LinearGroup 4
  basis : Basis 3
  middle : (pairStabilizer.subgroupOf (alternatingGroup (Fin 8))).map equiv.toMonoidHom =
    minimalParabolic basis 1
  ends : (fourStabilizer.subgroupOf (alternatingGroup (Fin 8))).map equiv.toMonoidHom =
    cutStabilizer basis {1}

/-- The simultaneous middle/end marking also identifies their intersection with the full Lie flag. -/
theorem EightFlagComparison.borel (c : EightFlagComparison) :
    (flagStabilizer.subgroupOf (alternatingGroup (Fin 8))).map c.equiv.toMonoidHom =
      cutStabilizer c.basis Set.univ := by
  have he : flagStabilizer.subgroupOf (alternatingGroup (Fin 8)) =
      pairStabilizer.subgroupOf (alternatingGroup (Fin 8)) ⊓
        fourStabilizer.subgroupOf (alternatingGroup (Fin 8)) := rfl
  rw [he, map_inf _ _ _ c.equiv.injective, c.middle, c.ends]
  ext g
  simp only [mem_inf, minimalParabolic, mem_cutStabilizer]
  constructor
  · rintro ⟨h, h'⟩ i _
    by_cases hi : i = 1
    · exact h' i hi
    · exact h i hi
  · intro h
    exact ⟨fun i _ => h i (Set.mem_univ i), fun i _ => h i (Set.mem_univ i)⟩

/-- The full third alternative, including the common Sylow flag needed by 15.3.32. -/
structure MiddleNodeFlagMarking (d : LocalData G) (I L : Subgroup G)
    extends MiddleNodePermutationMarking d I L where
  comparison : EightFlagComparison
  sylow : (d.starImage I d.S).map equiv.toMonoidHom = flagStabilizer

/-- The Lie-geometric alternatives before constructing the eight-point permutation marking. -/
inductive LieParabolicAlternative (d : LocalData G) (I : Subgroup G)
    (c : ComponentWitness d I) : Prop
  | linearTwo (F : ClassificationField)
      (marking : LinearTwo.BorelIdentification d I c F.degree F.Carrier)
  | small (marking : SmallParabolicMarking d I c.L)
  | middle (marking : OuterMiddleNodeData d I c.L)

/-- The exhaustive output specification of 15.3.28; existence remains the assembly target. -/
inductive MarkedAlternative (d : LocalData G) (I : Subgroup G)
    (c : ComponentWitness d I) : Prop
  | linearTwo (F : ClassificationField)
      (marking : LinearTwo.BorelIdentification d I c F.degree F.Carrier)
  | small (marking : SmallParabolicMarking d I c.L)
  | middle (marking : MiddleNodeFlagMarking d I c.L)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics
