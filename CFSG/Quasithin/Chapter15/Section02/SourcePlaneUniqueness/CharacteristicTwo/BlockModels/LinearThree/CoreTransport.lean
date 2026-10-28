module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.LinearThree.Constituent
public import Theory.GroupTheory.PResidual.RelativeCoreCommutator

/-!
# The same intrinsic MS core for both source radicals

The original pair uses R, whereas the parabolic construction uses QI.
For the same perfect subnormal component, both commutator cores equal
[O₂(X),X]. These literal subgroup equalities transport every module section,
center and Frattini subgroup without identifying R with QI or transporting
radical-dependent centralizer inequalities.

The actual C.2.7 application is in LinearThree.OriginalSource. The final
non-block elimination is in LinearThree.NonblockExclusion.
Source: Aschbacher--Smith C.1.34 and preliminary 15.2.23, pp.136--137,1115.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The MS commutator core is intrinsic to its perfect subnormal component. -/
theorem linearThreeMS_core_eq_intrinsic {X R : Subgroup G} {n : ℕ} {F : Type}
    [Field F] [Finite F] (hms : LinearThreeMSPair KnownSimple.IsKnownSimple X R n F) :
    msQ X R = ⁅X.pCoreIn 2,X⁆ := by
  let a := subgroupOfEquivOfLe (show X ≤ X ⊔ R from le_sup_left)
  let : Group.IsPerfect (X.subgroupOf (X ⊔ R)) := hms.component.2.perfect
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
    (f := a.toMonoidHom) a.surjective
  have hp : IsPPerfect 2 X := by
    intro N hn ht
    let := hn
    let := ht.isNilpotent
    exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)
  exact commutator_pCoreIn_eq_intrinsic_of_subnormal X (X ⊔ R) le_sup_left
    hms.component.2.subnormal hp

namespace PlaneUniquenessPreceding
open Section01 Section03 ChapterA.Section04 ChapterA.Section05To06
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The QI extension has the same intrinsic core, even for an exchanged constituent. -/
theorem plane_component_core_eq_intrinsic
    (hI : PlaneEscapes Mc ZS I) {X : Subgroup G}
    (hX : X ∈ Chapter1.cComponentsIn I) :
    msQ X (planeParabolicCore T H ZS) = ⁅X.pCoreIn 2,X⁆ := by
  let a := subgroupOfEquivOfLe hX.1
  let : Group.IsPerfect (X.subgroupOf I) := hX.2.perfect
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
    (f := a.toMonoidHom) a.surjective
  have hp : IsPPerfect 2 X := by
    intro N hn ht
    let := hn
    let := ht.isNilpotent
    exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)
  have hJI : X ⊔ planeParabolicCore T H ZS ≤ I := sup_le hX.1
    ((pCoreIn_le 2 _).trans ((d.residual_sup_planeSylow_le hI).trans inf_le_right))
  exact commutator_pCoreIn_eq_intrinsic_of_subnormal X _ le_sup_left
    (hX.2.subnormal.comap (inclusion hJI)) hp

/-- Compare the original radical with QI by equality of the actual commutator subgroups. -/
theorem plane_component_msCore_eq
    (hI : PlaneEscapes Mc ZS I) {X R : Subgroup G}
    (hX : X ∈ Chapter1.cComponentsIn I) {n : ℕ} {F : Type} [Field F] [Finite F]
    (hms : LinearThreeMSPair KnownSimple.IsKnownSimple X R n F) :
    msQ X R = msQ X (planeParabolicCore T H ZS) :=
  (linearThreeMS_core_eq_intrinsic hms).trans
    (d.plane_component_core_eq_intrinsic hI hX).symm

end PlaneUniquenessPreceding
end CFSG.Quasithin.Chapter15.Section02
