module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Setup
public import CFSG.Quasithin.ChapterE.Section03.Parameters
public import CFSG.Quasithin.ChapterE.Section06.Obstructions

/-!
# Model calculations required for the natural-module parameters

These are output specifications, not assumptions in the chosen natural input.
All fixed spaces use the faithful automizer of the original V, including its
central part. The root calculation concerns actual subgroups and conjugation
by L; it does not assume any global centralizer or weak-closure conclusion.
The consumers in Centralizers and Closure explain precisely where each
calculation is needed. Their construction remains a separate proof obligation.

Source: Aschbacher--Smith, 11.2.2, printed pp.767--768, using I.2.3(1),
B.4.6 and E.3.10.
-/

@[expose] public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The source parameter is tied to the actual action marking. -/
def naturalParameter (c : Coordinates D S.field) : ℕ :=
  match c with
  | .g2 _ => 2 * S.field.degree
  | .sl3 _ => S.field.degree
  | .sp4 _ => S.field.degree

theorem naturalParameter_gt_one (c : Coordinates D S.field) :
    1 < naturalParameter D S c := by
  have hn := S.nonbinary
  cases c <;> simp only [naturalParameter] <;> omega

/-- Required I.2.3/B.4.6 calculations on the full faithful automizer.
In particular no complement to C_V(L) is part of this specification. -/
structure FixedCodimensions (c : Coordinates D S.field) : Prop where
  involution_lower : letI := D.elementary; ∀ a : Automizer V, orderOf a = 2 →
    naturalParameter D S c ≤
      fixedCodim (@automizerRepresentation G _ V D.elementary) (zpowers a)
  involution_attains : letI := D.elementary; ∃ a : Automizer V, orderOf a = 2 ∧
    fixedCodim (@automizerRepresentation G _ V D.elementary) (zpowers a) =
      naturalParameter D S c
  odd_prime_lower : letI := D.elementary; ∀ (p : ℕ), p.Prime → Odd p → ∀ a : Automizer V,
    orderOf a = p → 2 * naturalParameter D S c ≤
      fixedCodim (@automizerRepresentation G _ V D.elementary) (zpowers a)
  dimension : 2 * naturalParameter D S c < subgroupCorank V ⊥

/-- The two model statements used after the lower bound has been proved.
The first classifies a minimal fixed space up to the actual L-action. The
second places A₂ actors inside the preimage of the inner action, retaining
the two-core kernel in LT. Neither statement mentions a weak closure. -/
structure RootGeometry {c : Coordinates D S.field} (f : InvariantFlag c) : Prop where
  minimal_fixed : ∀ U : Subgroup G, U ≤ V →
    subgroupCorank V U = naturalParameter D S c →
    ¬ ChapterE.Section06.oddCentralizerCondition (normalizer (L : Set G)) V U →
    (∃ l : L, (f.Vi 2).map (MulAut.conj (l : G)).toMonoidHom ≤ U) ∨
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
        ∃ l : L, (f.Vi 1).map (MulAut.conj (l : G)).toMonoidHom = U)
  two_family : letI := D.elementary; ∀ A : Subgroup G, A ≤ (T : Subgroup G) →
    inducedAutomizer V A ∈ fixedSpaceFamily
      (@automizerRepresentation G _ V D.elementary) 2 →
    A ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2

/-- The minimum is computed using actual involutions, so the odd-order
fallback in the E.3 definition cannot create a spurious value. -/
theorem localM_of_fixedCodimensions {c : Coordinates D S.field}
    (h : FixedCodimensions D S c) :
    @localM G _ V D.elementary = naturalParameter D S c := by
  let := D.elementary
  obtain ⟨a, ha, hca⟩ := h.involution_attains
  obtain ⟨b, hb, hcb⟩ := moduleM_attained (automizerRepresentation V) ⟨a, ha⟩
  exact le_antisymm ((moduleM_le_involution _ ha).trans_eq hca)
    ((h.involution_lower b hb).trans_eq hcb)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters
