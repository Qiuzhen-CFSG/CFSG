module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.PlaneCentralizer
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure
public import Theory.SpecificGroups.SymmetricFive.CentralSylowInvolution

/-!
# The marked symmetric-five exclusion in 14.3.31

The shifted involution has alternating displacement with image the original
binary seed plane. Uniqueness of such a displacement makes it commute with
every element preserving that plane, in particular the original Sylow and
L1. In S5 an involution centralizing a full Sylow has a two-group centralizer.
Thus the two-perfect L1 has trivial image, contrary to its actual natural
cubic action on V/V1. The proof retains H/C_H(U-hat), with no two-core
identification and no use of the later natural conclusion in 14.3.32.

The marked plane is essential: the literal semilinear natural S5 model has
an outer Frobenius involution with alternating displacement. The printed
unqualified involution-type exclusion is replaced here by the stronger
source geometry already available in 14.3.30.

The 14.3.25 seed exclusion remains explicit and belongs to this centerlessness
owner. The earlier S5 alternative is supplied by qt-d-hs-action-source.
The other action alternatives, both seed exclusions, the Thompson argument
and the Goldschmidt contradiction remain open. The final local-structure
application retains ActionStructure as an independent premise; its discharge
and the complete source assembly stay with qt-d-hs-local-structure.

Source: Aschbacher--Smith, 12.8.5, 14.3.30--31, printed pp.850,1002--1003.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The S5 branch of 14.3.31 is impossible for the actual shifted involution.
The argument uses the marked moved plane, not a blanket assertion about the
involution types of the natural S5 module. -/
theorem source_centerless_of_symmetricFive (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (he : Nonempty ((F.H ⧸ F.uhatAction.ker) ≃* Equiv.Perm (Fin 5))) :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ := by
  by_contra hI
  obtain ⟨e⟩ := he
  obtain ⟨a, ha, P, hPC, hnot⟩ := source_involution_large_centralizer d earlier hq chosen
    structural alternatives F hne hseed hI e
  exact hnot (Theory.SpecificGroups.SymmetricFive.involution_centralizer_isTwoGroup_of_sylow
    P a ha hPC)

/-- Apply the proved S5 branch to the literal local-structure assembly.
The seed exclusion and the independently constructed action remain explicit. -/
theorem localStructure_of_seed_symmetricFive_action (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (he : Nonempty ((F.H ⧸ F.uhatAction.ker) ≃* Equiv.Perm (Fin 5)))
    (action : ActionStructure F) : LocalStructure L F :=
  localStructure_of_centerless_action d earlier hq chosen structural alternatives F hne
    (source_centerless_of_symmetricFive d earlier hq chosen structural alternatives F hne hseed he)
    action

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
