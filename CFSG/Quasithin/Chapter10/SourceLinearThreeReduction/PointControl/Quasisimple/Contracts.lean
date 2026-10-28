module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Preparation
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even

/-!
# Two independent inspections of the quasisimple containing component

The rank-two inspection must produce common centralization or an actual
symplectic parabolic marking. The complementary Theorem C carriers must
produce common centralization. These are outstanding source obligations,
not theorem certificates. Their proofs must retain the original module,
quotient and local embedding and every module row not separately excluded.

The symplectic endpoint is proved separately, and `Source` retains final
assembly until both inspections are discharged.
Source: Aschbacher--Smith, A.3.12 and 10.1.1,10.2.9, pp.47--48,741,750--751.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple
open Chapter3.Section02 Theory.SpecificGroups.SymplecticFour
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- A marked embedding of the actual smaller subgroup in the containing
central quotient, with both possible maximal parabolic residuals. -/
def SymplecticMarking (L I : Subgroup G) : Prop :=
  ∃ (F : Type u) (_ : Field F) (_ : Finite F) (n : ℕ),
    Nat.card F = 2 ^ n ∧ 1 < n ∧
    ∃ eI : (I ⧸ center I) ≃* Sp F,
      (L.subgroupOf I).map
        (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) = pointLocal ∨
      (L.subgroupOf I).map
        (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) = planeLocal

/-- The actual rank-two carrier inspection. Module and embedding recognition
are conclusions to prove, never extra assumptions on the fixed setup. -/
def RankTwoInspectionAt (T : Sylow 2 G) : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    D.IsMinimalFullModule →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
    ∀ (t v : G) (I : Subgroup G), EscapingComponent D t v I → IsQuasisimple I →
    (∃ n, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) n) →
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (I : Set G) ∨
      SymplecticMarking L I

/-- The complementary carrier inspection retains the full Theorem C
catalogue; exclusion of a rank-two carrier is the only case split. -/
def OtherInspectionAt (T : Sylow 2 G) : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    D.IsMinimalFullModule →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
    ∀ (t v : G) (I : Subgroup G), EscapingComponent D t v I → IsQuasisimple I →
    ChapterA.Section02.IsTheoremCModel (I ⧸ center I) →
    (¬ ∃ n, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) n) →
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (I : Set G)

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple
