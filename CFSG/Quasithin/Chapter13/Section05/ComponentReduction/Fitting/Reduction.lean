module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.PrimeReduction
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.Supercritical
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.Actors
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Selection

/-!
# Reduction of 13.5.20 to the remaining elementary-nine action

Failure of V* ≤ C(F(H*)) supplies a moved prime core. The S₃ pair
conclusion of F.9.5 restricts that prime to three. The literal 13.5.19
normalizer and core facts feed the Thompson argument, and the
supercritical classification plus the cubic rank construction leave a
normal E₉ inside H*. Its V* action is nontrivial, as is the action of
O₂(Y*).

The theorem retains the full SQTK input, the earlier local residual facts,
and the specialized conjugate-pair consequence of F.9.5. The faithful
binary action on the nonabelian U_H/V₁ and its rank-two moved space are
constructed in SourceAction. The normal-nine representation obstruction is
proved in NineObstruction. Conclusion assembles these deductions into
Fitting centralization and the component-selection application.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.20, printed p.923 (PDF p.940).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting
open Section08.Source
variable {G : Type*} [Group G] [Finite G]

/-- The remaining obstruction to 13.5.20 is a literal normal nine-group.
The hypotheses on Y are its earlier residual/quotient/normalization facts;
the normalizer equalities are precisely 13.5.19. The pair input is the
S₃ clause of F.9.5(6.i), specialized to the actual quotient conjugates.
No Fitting-centralization or representation-obstruction premise is used. -/
theorem normal_nine_of_fitting_failure
    (K : GroupClass) (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    (hSQTK : IsSQTK K D.H)
    (hindex : D.Vplus.relIndex D.V = 2) (hu : ¬ IsMulCommutative D.UH)
    (Y : Subgroup G) (hYH : Y ≤ D.H) (hY : IsPPerfect 2 Y)
    (hYquot : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hYV : Y ≤ normalizer (D.V : Set G))
    (himage : starImage D.H (D.H ⊓ normalizer (Y : Set G)) =
      normalizer (starImage D.H Y : Set (Hstar D.H)))
    (hcore : D.V ≤ (D.H ⊓ normalizer (Y : Set G)).pCoreIn 2)
    (hpairs : ∀ x : Hstar D.H,
      ¬ IsPGroup 2 (starImage D.H D.V ⊔
        (starImage D.H D.V).map (MulAut.conj x).toMonoidHom : Subgroup (Hstar D.H)) →
      Nat.card (starImage D.H D.V ⊔
        (starImage D.H D.V).map (MulAut.conj x).toMonoidHom : Subgroup (Hstar D.H)) = 6)
    (hfit : ¬ starImage D.H D.V ≤
      centralizer (fittingSubgroup (Hstar D.H) : Set (Hstar D.H))) :
    ∃ P : Subgroup (Hstar D.H), P.Normal ∧ P ≤ pCore 3 (Hstar D.H) ∧
      IsElementaryAbelian 3 P ∧ Nat.card P = 9 ∧
      ⁅P, starImage D.H D.V⁆ ≠ ⊥ ∧
      ¬ (starImage D.H Y).pCoreIn 2 ≤ centralizer (P : Set (Hstar D.H)) := by
  apply exists_normal_nine_of_moved_threeCore D.H Y D.V (star_threeRank_le K D.H hSQTK)
    himage hcore h.elementary.isPGroup (star_twoPerfect D.H Y hYH hY)
    (star_cubic_quotient D.H Y hYH hYquot) (star_centralizes_V D h hindex hu Y hYV)
  exact threeCore_moved_of_fitting_not_centralized (starImage D.H D.V)
    (LocalGeometry.star_V_card_two h hindex hu) (pCore_quotient_pCore_eq_bot 2) hpairs hfit

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting
end
