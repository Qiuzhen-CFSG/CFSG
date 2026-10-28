module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.PlaneCentralizer
public import Theory.SpecificGroups.AlternatingSix.GoldenClassGeometry

/-!
# Excluding the alternating-six action row in 14.3.31

Every involution centralizer in the actual A6 has order eight. The shifted
involution supplied by the original flag would instead centralize the
nontrivial two-perfect point-residual image. Applying the marked-plane
construction gives a contradiction directly on H/C_H(U-hat).

This closes the A6 row conditional on the preceding seed exclusion, which
remains with qt-d-hs-centerless-source. The S6 and G2(2) rows and the
solvable Goldschmidt branch remain open; no A6 quotient is inferred from
an unconnected family label. Earlier action rows retain their producer
qt-d-hs-action-source, and final local assembly stays with
qt-d-hs-local-structure.

Source: Aschbacher--Smith, 14.3.23(2)(iii), 14.3.30--31, pp.1000,1002--1003.
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

/-- The A6 row is incompatible with the original shifted-center geometry. -/
theorem source_centerless_of_alternatingSix (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (he : Nonempty ((F.H ⧸ F.uhatAction.ker) ≃* alternatingGroup (Fin 6))) :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ := by
  by_contra hI
  obtain ⟨e⟩ := he
  obtain ⟨a, ha, _, _, hnot⟩ := source_involution_large_centralizer d earlier hq chosen
    structural alternatives F hne hseed hI e
  exact hnot (IsPGroup.of_card (n := 3) (AlternatingSix.GoldenClassGeometry.centralizer_two a ha))

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
