module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Inputs
public import CFSG.Quasithin.Chapter10.SourceElementCentralizerComponent
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerReduced

/-!
# Remaining source steps for non-A₅ point control

The half-Sylow uniqueness assertion is exactly 10.2.6(1), with
T₁ = N_T(L). The point preparation concerns the actual opposite moved
factor and a locally saturated vector whose centralizer escapes M. It
must control both N_G(C_T(v)) and the action of C_T(v) on L, including
vectors fixed by L₀. These are conclusions to be proved from the source,
not properties supplied by a fundamental setup.

After this preparation, source 1.2.4 produces a strict normal containing
C-component. Its quasisimple and constrained branches can be treated
independently. The latter receives the literal characteristic-two join
and reduced orbit module, which the reduction constructs using A.1.26
and B.2.14. None of the definitions here asserts a source theorem.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
10.2.4--9, printed pp.747--753.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The literal subgroup L₀T₁, rather than L₀T. -/
def halfJoin (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  localOrbit T L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))

/-- The earlier source uniqueness obligation 10.2.6(1). -/
def HalfSylowUnique (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  ∀ M : Subgroup G, IsMaximalTwoLocal M → halfJoin T L ≤ M → M = D.maximalLocal

/-- The original point-normalizer and component-stabilizer steps, before
constructing the enlarged component. No fixed vector is omitted. -/
def PointSylowControl (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (t : G) : Prop :=
  ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
    ¬ centralizer ({v} : Set G) ≤ D.maximalLocal →
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G)) →
    normalizer ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G) ≤ D.maximalLocal ∧
      (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≤ normalizer (L : Set G)

/-- A counterexample configuration constructed by the point reduction.
Normality is inside C_G(v), and normal generation retains the original L. -/
structure EscapingComponent
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (t v : G) (I : Subgroup G) : Prop where
  t_mem : t ∈ (T : Subgroup G)
  t_not_normalizes : t ∉ normalizer (L : Set G)
  crossed : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)
  v_mem : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom
  v_ne : v ≠ 1
  v_not_fixed : v ∉ centralizer (halfJoin T L : Set G)
  half_unique : HalfSylowUnique D
  sylow : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
    (centralizer ({v} : Set G))
  sylow_normalizer : normalizer ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G) ≤
    D.maximalLocal
  sylow_normalizes : (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≤ normalizer (L : Set G)
  component_normalizer : normalizer (L : Set G) ≤ D.maximalLocal
  moved_normalizer : normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal
  strict : L < I
  le_centralizer : I ≤ centralizer ({v} : Set G)
  component : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent
  normalizes : centralizer ({v} : Set G) ≤ normalizer (I : Set G)
  escapes : ¬ I ≤ D.maximalLocal
  generation : componentOrbit L I = I

/-- Source 10.2.6 is independent of the choice of module seed. -/
def HalfSylowUniqueAt (T : Sylow 2 G) : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) → HalfSylowUnique D

/-- Choose the source module and prove the point-Sylow step. Keeping the
independent half-Sylow uniqueness premise inside the conclusion lets both
source arguments proceed independently. Final assembly must discharge it. -/
def SelectionAt (T : Sylow 2 G) : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ L : Subgroup G, L ∈ Chapter1.LStar G (T : Subgroup G) →
    ChapterA.Section04.IsFaithfulSignalizerType L → IsQuasisimple (L ⧸ pCore 2 L) →
    ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L, D.IsMinimalFullModule ∧
      ∃ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) ∧
        (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) ∧
        (HalfSylowUnique D → PointSylowControl D t)

/-- The quasisimple containing-component branch of 10.2.9, pp.750--751. -/
def QuasisimpleExclusionAt (T : Sylow 2 G) : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    D.IsMinimalFullModule →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
    ∀ (t v : G) (I : Subgroup G), EscapingComponent D t v I → IsQuasisimple I → False

/-- The constrained containing-component branch, including the linear-five
endgame on pp.752--753. The reduction constructs both displayed inputs. -/
def ConstrainedExclusionAt (T : Sylow 2 G) : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    D.IsMinimalFullModule →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
    ∀ (t v : G) (I : Subgroup G), EscapingComponent D t v I → ¬ IsQuasisimple I →
      generalizedFitting (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Subgroup G) =
        pCore 2 (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Subgroup G) →
      IsPReduced 2 ((conjugateSpanBy
        (⁅D.fullModule,L⁆ ⊓ centralizer (((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Set G)) I).subgroupOf
          (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)))) → False

end CFSG.Quasithin.Chapter10.PointControl
