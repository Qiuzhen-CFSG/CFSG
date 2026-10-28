module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RankOneFourNormalizer.Checks
public import Mathlib.GroupTheory.Perm.Support

/-!
# Elementary sixteens in the Hall–Janko Sylow: finite checks

Outside the distinguished four-group, an involution in the fixed Sylow has
either four or sixteen commuting involutions. In the latter case these lie
in the radical and include the distinguished four-group. Among involutions
in the radical, exactly that four-group has a fixed point in the native
degree-100 action.

The checks use the existing 128-element enumeration and the unchanged ATLAS
J2G1-p100B0 tables. They support the J₂ inspection in Aschbacher–Smith,
13.5.15, printed p.921. No external enumeration is accepted as a proof.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ElementarySixteenFusion.Checks
open ExceptionalParabolics.PairNormalizer.SylowData
open GeneratorPair.SecondOrbitCertificate

def fourIndices : Finset (Fin 128) := {0, 5, 6, 26}

def involutionIndex (i : Fin 128) : Prop :=
  (sTable i * sTable i) 0 = 0 ∧ (sTable i * sTable i) 1 = 1

instance (i : Fin 128) : Decidable (involutionIndex i) := inferInstanceAs
  (Decidable ((sTable i * sTable i) 0 = 0 ∧ (sTable i * sTable i) 1 = 1))

def commutingInvolutions (i : Fin 128) : Finset (Fin 128) :=
  Finset.univ.filter fun j => involutionIndex j ∧
    (sTable i * sTable j) 0 = (sTable j * sTable i) 0 ∧
    (sTable i * sTable j) 1 = (sTable j * sTable i) 1

set_option maxRecDepth 100000 in
theorem commuting_involutions_check : ∀ i : Fin 128,
    involutionIndex i → i ∉ fourIndices →
      (commutingInvolutions i).card = 4 ∨
        (commutingInvolutions i).card = 16 ∧
        fourIndices ⊆ commutingInvolutions i ∧
        ∀ j ∈ commutingInvolutions i, j.val < 64 := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
theorem fixed_point_check : ∀ i : Fin 128,
    i.val < 64 → involutionIndex i →
      ((sTable i).support.card < 100 ↔ i ∈ fourIndices) := by
  apply allFin
  decide +kernel

end Sporadic.LeechRelated.J2.ElementarySixteenFusion.Checks
