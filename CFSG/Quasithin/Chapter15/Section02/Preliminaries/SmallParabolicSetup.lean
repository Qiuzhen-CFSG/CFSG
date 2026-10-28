module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenSetup
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaUniqueness
public import Theory.GroupTheory.Fitting.Subgroup
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonFixed
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.NaturalAction

/-!
# Literal interfaces for the small chosen parabolics

The four action rows retain the full conjugation image, the embedded Fitting
subgroup of its J-hat, and the image of the original Sylow subgroup. The residual
and rank-one witness use the original Y and Rc of 15.2.3 and 15.2.6. These are
conclusion interfaces, not assumed source theorems.

Source: Aschbacher--Smith 15.2.1 and 15.2.3--8, printed pp.1104--1110.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The four whole-action alternatives of original 15.2.1. The Omega row retains
its natural coordinates; the Fitting equality in the last row uses the embedded
Fitting subgroup of the literal J-hat, and the Sylow image is the original T. -/
def SmallActionAlternatives (T : Sylow 2 G) (M V : Subgroup G)
    [IsElementaryAbelian 2 V] (hn : M ≤ normalizer (V : Set G)) : Prop :=
  let ρ := imageRepresentation M V hn
  let D := internalActionImage M V hn
  let K := Jhat ρ
  let S := ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict
  (K = ⊤ ∧ Nonempty (D ≃* Equiv.Perm (Fin 3))) ∨
    (Nonempty (K ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty (D ≃* (Equiv.Perm (Fin 3) × Multiplicative (ZMod 3)))) ∨
    SourceCases.Omega ρ ∨
    (Nonempty (K ≃* DihedralGroup 5) ∧
      (Nonempty (S ≃* Multiplicative (ZMod 2)) ∨
        Nonempty (S ≃* Multiplicative (ZMod 4))) ∧
      (fittingSubgroup D = (fittingSubgroup K).map K.subtype ∨
        Nonempty (fittingSubgroup D ≃* Multiplicative (ZMod 15))))

/-- The exact residual in 15.2.3, using the chosen action's own elementary structure. -/
noncomputable abbrev ChosenSmallSource.residual
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V) : Subgroup G :=
  letI := h.prepared.elementary
  caseIIResidual T M (chosenStarredPreimage M V h.prepared.normalized) Mc

/-- The permitted earlier-source and counterexample inputs. No conclusion of
15.2.1--8 is included here. The normalizer consequences of 15.1.14 follow from
`PreparedChosenModule.thompsonFixed_normalizers`. -/
structure SmallSourcePrior (T : Sylow 2 G) (M V : Subgroup G) : Prop where
  global_residual : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
    (centralizer (centralInvolutions T : Set G)).subtype ≤
      centralizer (thompsonFixed T V : Set G)
  not_model : ¬ ClassificationModels.IsTheoremEModel G
  not_orthogonal : ∀ N : Subgroup G, IsOrderingMaximal T N →
    ¬ Nonempty (NaturalOrthogonalAction N (localModule T N))

/-- Original 15.2.6 on the literal subgroup Y₁ of Y. Relative normality is
expressed by T-normalization; no normality in the whole ambient G is asserted. -/
structure SmallResidualWitness {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (Y₁ : Subgroup G) : Prop where
  le_residual : Y₁ ≤ h.residual
  perfect : IsPPerfect 2 Y₁
  invariant : (T : Subgroup G) ≤ normalizer (Y₁ : Set G)
  quotient :
    let L := Y₁ ⊔ (M ⊓ Mc).pCoreIn 2
    Nonempty ((L ⧸ pCore 2 L) ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* DihedralGroup 5) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)
  centralizer : Y₁ ⊓ centralizer (V : Set G) = Y₁.pCoreIn 2
  unique : maximalTwoLocalOvergroups (Y₁ ⊔ (T : Subgroup G)) = {M}

/-- The retained last normalizer assertion of 15.2.7, precisely on the
T-invariant two-perfect cubic subgroups consumed by 15.2.8. -/
def SmallCubicNormalizer {T : Sylow 2 G} {M Mc V : Subgroup G}
    (_h : ChosenSmallSource T M Mc V) (Y₁ : Subgroup G) : Prop :=
  ∀ X : Subgroup G, X ≠ ⊥ → IsPPerfect 2 X →
    X ≤ M ⊓ centralizer (V : Set G) →
    (T : Subgroup G) ≤ normalizer (X : Set G) →
    Nat.card (X ⧸ pCore 2 X) = 3 → X ≤ normalizer (Y₁ : Set G)

end CFSG.Quasithin.Chapter15.Section02
