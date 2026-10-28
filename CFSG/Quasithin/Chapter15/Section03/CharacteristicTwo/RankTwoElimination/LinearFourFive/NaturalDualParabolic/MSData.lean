module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Head

/-!
# The remaining MS-pair construction for the point parabolic

The group in C.1.34 is J = O²(P)S, with its actual two-residual component
and the original S. The output interface below retains its full binary MS
hypotheses, the Sylow marking, and the comparison of [O₂(J),O²(P)] with
the actual Q_P = [O₂(P),P]. These are construction targets, not assumptions
of a completed source theorem. The classification consumer may take this
output explicitly while the ambient construction is proved independently.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
C.1.31–34, printed pp.135–137; 15.3.24, printed pp.1129–1130.
-/

@[expose] public section

open Subgroup BinaryLinear.OuterCyclic

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic

universe u
variable {G : Type u} [Group G] {d : LocalData G} {L : Subgroup G}

/-- The MS ambient group uses the two-residual, not the two-core. -/
noncomputable def residualOvergroup (h : NaturalDual d L) (x : Space 4) : Subgroup G :=
  Stellmacher.twoResidualAmbient (point h x) ⊔ d.S

/-- The literal component to be proved a C-component in the MS ambient group. -/
noncomputable def residualComponent (h : NaturalDual d L) (x : Space 4) :
    Subgroup (residualOvergroup h x) :=
  (Stellmacher.twoResidualAmbient (point h x)).subgroupOf (residualOvergroup h x)

/-- The original two-subgroup, transported to the MS ambient group. -/
noncomputable def sylowPart (h : NaturalDual d L) (x : Space 4) :
    Subgroup (residualOvergroup h x) := d.S.subgroupOf (residualOvergroup h x)

/-- An output of the ambient construction. In particular, the characteristic
condition must be proved using the transferred action premise of 15.3.11(12). -/
structure MSData (κ : GroupClass.{u}) (h : NaturalDual d L) (x : Space 4) where
  input : ChapterC.BinaryMS.Input κ (residualComponent h x) (sylowPart h x)
  sylow : Chapter1.IsSylowIn 2 d.S (residualOvergroup h x)
  overgroup_eq : residualOvergroup h x = point h x ⊔ d.S
  core_eq : (ChapterC.BinaryMS.commutatorCore (residualComponent h x)).map
      (residualOvergroup h x).subtype = coreCommutator (point h x)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic

end
