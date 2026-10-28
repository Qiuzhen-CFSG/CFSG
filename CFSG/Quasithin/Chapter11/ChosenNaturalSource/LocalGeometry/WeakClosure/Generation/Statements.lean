module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Central
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.CartanTransport
public import Theory.Representation.BinaryConjugationSection

/-!
# Literal outputs and remaining inputs for 11.2.1

The doubled alternative uses the original subgroup V_M, the original quotient
L/O₂(L), and the same full SL₃ marking as the chosen central quotient. Its
coordinate homomorphism is bijective and intertwines ambient conjugation with
two copies of that natural action. These definitions specify mathematical
outputs; they do not assert the source theorem.

Source: Aschbacher--Smith, 11.2.1, printed pp.766--767.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterE.Section06.FixedPointBounds
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Two isomorphic natural summands on the literal full module, including
its entire central part and the full center of SL₃. -/
def DoubledNatural : Prop :=
  ∃ m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3),
    Nonempty (BinaryConjugationSection L
      (Source.conjugateSpan (normalizer (L : Set G)) V) ⊥
      ((repeated (linearNatural S.field 3) 2).comp
        (m.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))

/-- The exact H-star normalization clause of the preceding 11.0.3(5). -/
def OtherRowsNormalize : Prop :=
  ∀ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
    (Nonempty (ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) ∨
      Nonempty (ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))) →
    H ⊓ normalizer (L : Set G) ≤ normalizer (V : Set G)

/-- The specialized earlier 4.4.3 conclusion needed for an elementary Hall
kernel. It is not included in NonbinaryNaturalInput and must be proved. -/
def OddKernelNormalizer : Prop :=
  ∀ (p : ℕ), p.Prime → Odd p → ∀ A : Subgroup G,
    A ≠ ⊥ → IsElementaryAbelian p A →
    A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) →
    (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) →
    normalizer (A : Set G) ≤ normalizer (L : Set G)

/-- The two actual automizer bounds used in the source proof. -/
def AutomizerBounds : Prop :=
  nPrime (inducedAutomizer V
    (normalizer (L : Set G) ⊓ normalizer (V : Set G))) ≤ S.field.degree ∧
  (DoubledNatural D S →
    nPrime (inducedAutomizer (Source.conjugateSpan (normalizer (L : Set G)) V)
      (normalizer (L : Set G))) ≤ 2 * S.field.degree)

/-- The representation-theoretic step after Thompson movement: the enlarged
full module is precisely two copies of the same natural SL₃ action. -/
def DoublingStep : Prop :=
  Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
    L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ →
    V ≠ Source.conjugateSpan (normalizer (L : Set G)) V → DoubledNatural D S

/-- All clauses of the original generation alternative. -/
def Conclusion (H : Subgroup G) : Prop :=
  ChapterE.generationParameter H ≤ S.field.degree ∨
    (Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
      DoubledNatural D S ∧ V ⊓ centralizer (H : Set G) = ⊥ ∧
      L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      ChapterE.generationParameter H ≤ 2 * S.field.degree)

/-- A doubled marking supplies the full special-linear quotient, not PSL₃. -/
theorem DoubledNatural.isSL (h : DoubledNatural D S) :
    Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) := by
  obtain ⟨m, _⟩ := h
  exact ⟨S.field.Carrier, inferInstance, inferInstance, S.field.card_eq, ⟨m.groupEquiv⟩⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation
