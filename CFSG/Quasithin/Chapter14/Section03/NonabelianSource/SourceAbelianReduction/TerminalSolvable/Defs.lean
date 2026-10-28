module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.SourceNonsolvable.Original
public import CFSG.Quasithin.Chapter14.Section03.EmptyFamilySieve.DerivedG2
public import CFSG.Quasithin.Chapter14.Section03.EmptyFamilySieve.MathieuTwentyTwo

/-!
# Component contracts for the nonsolvable branch of 14.3.15

The lift retains the original point normalizer, its C-component, and the
literal image under the terminal action quotient. Normality is relative to
that point normalizer and concerns the T-conjugate span, not the join with T.

The four excluded rows require actual two-core quotient isomorphisms, exactly
as in the proved empty-family sieve. The three remaining rows instead mark
the actual dotted component. This distinction leaves the kernel comparison,
the A₆ diagram action, and the paired A₅ normalizer calculation with their
source producers; an abstract dotted isomorphism does not identify K/O₂(K).
These definitions assert no exhaustiveness or classification theorem.

Source: Aschbacher--Smith 14.3.13--15, printed pp.993--994.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G}

/-- An actual moved component and its ambient local lift. -/
structure ComponentLift (F : InvariantFlag T V 2) (g : G) (K : Subgroup G) : Prop where
  le_pointNormalizer : K ≤ F.H
  local_component : K ∈ MainForward.localComponents T
  component : (K.subgroupOf F.H).IsCComponent
  image_component : IsComponent F.TerminalHdot (F.terminalDot K)
  image_moved : ⁅F.terminalDot K, F.terminalDot (F.X g)⁆ ≠ ⊥
  normal_span : ((conjugateSpanBy K (T : Subgroup G)).subgroupOf F.H).Normal

/-- The already proved sieve rows, on the actual two-core quotient. -/
def ExcludedQuotientRow (K : Subgroup G) : Prop :=
  Nonempty ((K ⧸ pCore 2 K) ≃* Atlas.G2.BinaryParabolicPair.DerivedModel) ∨
  Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) ∨
  Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) ∨
  Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22TripleCover)

/-- Both the single and exchanged A₅ branches are included here. The A₆
mark does not silently assert that its Sylow action is inner. -/
def SmallImageRow (F : InvariantFlag T V 2) (K : Subgroup G) : Prop :=
  Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 5)) ∨
  Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 6))

/-- The surviving rank-one image with its literal conjugate-span equality. -/
def EightImageRow (F : InvariantFlag T V 2) (K : Subgroup G) : Prop :=
  K = conjugateSpanBy K (T : Subgroup G) ∧
  Nonempty (F.terminalDot K ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3))

/-- The precise catalogue still needed for the solvability assembly.
Its first branch includes the quotient lifting, not just a model name. -/
def ComponentCases (F : InvariantFlag T V 2) (K : Subgroup G) : Prop :=
  (K = conjugateSpanBy K (T : Subgroup G) ∧ ExcludedQuotientRow K) ∨
  SmallImageRow F K ∨ EightImageRow F K

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
