module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionFixedFreeRows
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionFixedFreeOrbits
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionAssembly
public import Theory.Representation.SL5ExteriorSquare.OrbitSizeSeparation
public import Theory.Representation.BinaryPermutation.OrbitSizeSeparation
public import Theory.Representation.HexacodeAction.OrbitSizeSeparation

/-!
# The fixed-free branch of original 12.2.16

For each of the seven actual module alternatives of 12.2.2, the original
chosen subgroup V is globally TI when C_V(L)=1. The natural linear and
A₇ four-space rows use their existing fusion proofs. The four-dimensional
SL₃ row is impossible. Nonzero transitivity settles A₆ and derived G₂(2);
orbit-size separation settles rank-ten SL₅, natural A₅/A₇/A₈, and the
faithful irreducible triple-A₆ six-space.

The structural prefix and seven-row classification remain the permitted
earlier-source inputs. Every orbit premise is discharged here. The final
theorem supplies the fixedFree argument of the existing fusion assembly;
its reducible and final A₈ inputs remain with that assembly's owners.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
12.2.2(3), printed p.795, and 12.2.16, pp.799–800.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

theorem globalTI_of_quotient_orbit_separation
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V)
    (hsep : OrbitCardSeparates D.quotientAction) : IsTISubgroup V := by
  apply globalTI_of_chosen_orbit_separation h D structural hnone
  exact hsep.of_intertwining (QuotientGroup.mk' (pCore 2 L))
    (QuotientGroup.mk'_surjective _) (LinearEquiv.refl _ _) (fun _ _ => rfl)

theorem globalTI_of_fixedFree_alternating_orbits
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) {n : ℕ}
    (a : letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulCentralAction (alternatingNatural n))
    (hsep : OrbitCardSeparates (alternatingNatural n)) : IsTISubgroup V := by
  let := D.actionCentralizer_normal
  apply globalTI_of_chosen_orbit_separation h D structural hnone
  let f := a.groupEquiv.toMonoidHom.comp
    (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L))
  exact hsep.of_intertwining f
    (a.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _))
    ((fixedFreeQuotientEquiv D hc).trans a.linearEquiv) (by
      intro l v
      change a.linearEquiv (fixedFreeQuotientEquiv D hc (D.chosenAction l v)) = _
      rw [fixedFreeQuotientEquiv_action]
      exact a.intertwines (QuotientGroup.mk' _ l) _)

/-- Original 12.2.16 in every fixed-free row, with no global-fusion premise. -/
theorem globalTI_of_fixedFree_module_alternatives
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V)
    (rows : ModuleAlternatives1222 D)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    IsTISubgroup V := by
  cases rows with
  | linear n _ a =>
      exact globalTI_of_natural h D structural hnone (D.conjugationModel_of_quotientAction a)
  | linearThreeExtension e hd _ =>
      exact (not_linear_three_four_fixedFree D hc e hd).elim
  | linearFiveExterior e hd hi =>
      let := hi
      exact globalTI_of_quotient_orbit_separation h D structural hnone
        (SL5ExteriorSquare.marked_irreducible_ten_orbitCardSeparates D.quotientAction e hd)
  | alternating n hn hu a =>
      by_cases he : n = 6
      · subst n
        exact globalTI_of_alternating_six_fixedFree h D structural hnone hc a
      · have hn : n = 5 ∨ n = 7 ∨ n = 8 := by omega
        apply globalTI_of_fixedFree_alternating_orbits h D structural hnone hc a
        rcases hn with rfl | rfl | rfl
        · exact BinaryPermutation.five_natural_orbitCardSeparates
        · exact BinaryPermutation.seven_natural_orbitCardSeparates
        · exact BinaryPermutation.eight_natural_orbitCardSeparates
  | alternatingSevenFour e hd =>
      let := D.actionCentralizer_normal
      exact globalTI_of_alternating_seven_four h D structural hnone e hd
  | g2 a => exact globalTI_of_g2_fixedFree h D structural hnone hc a
  | tripleSix e hd hf hi =>
      exact globalTI_of_quotient_orbit_separation h D structural hnone
        (Hexacode.marked_irreducible_six_orbitCardSeparates D.quotientAction e hf hi hd)

/-- Application to the existing original 12.2.16 assembly. -/
theorem globalTI_of_module_alternatives_and_reducible
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V)
    (rows : ModuleAlternatives1222 D)
    (reducible : V ⊓ centralizer (L : Set G) ≠ ⊥ →
      IsTISubgroup V ∨ Nonempty (AlternatingEightFusion T L V))
    (eight : ∀ C : AlternatingEightFusion T L V, omegaCenterIn C.pointSylow ≤ V) :
    IsTISubgroup V := by
  apply globalTI_of_row_reductions h D structural hnone
    (fun hc => globalTI_of_fixedFree_module_alternatives h D structural hnone rows hc)
    reducible eight

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
