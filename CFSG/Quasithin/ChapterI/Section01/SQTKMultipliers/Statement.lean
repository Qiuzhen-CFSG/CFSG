module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ClassificationModels.Families
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.GroupTheory.PerfectCentralCoverRank

/-!
# The source statement of I.1.3

This neutral Chapter I boundary retains the six actual model rows and the
literal kernel of the constructed universal perfect cover. The odd PSL₂
exception q ≠ 9, the exclusion of PSL₃(4) from the cyclic-three row, and the
unitary fixed-field convention are part of the statement. In particular,
the Sz(8) and PSL₃(4) multipliers are C₂ × C₂ and (C₄ × C₄) × C₃.

The boundary imports no Chapter B module. The B.5 adapter compares this
statement with its existing input without changing that older interface.
Definitions here state the source theorem; its remaining model calculations
and rank exclusions must still be discharged by the assembly.

Source: Aschbacher--Smith, I.1.3, printed p.407.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterI.SQTKMultipliers
open PerfectCentralCovering
universe u

/-- The six multiplier types in all six rows of I.1.3. -/
inductive MultiplierShape
  | two | three | six | twelve | elementaryFour | exceptionalFortyEight

/-- The actual finite abelian group in the corresponding source row. -/
def MultiplierShape.Carrier : MultiplierShape → Type
  | .two => Multiplicative (ZMod 2)
  | .three => Multiplicative (ZMod 3)
  | .six => Multiplicative (ZMod 6)
  | .twelve => Multiplicative (ZMod 12)
  | .elementaryFour => Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
  | .exceptionalFortyEight =>
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) × Multiplicative (ZMod 3)

instance MultiplierShape.carrierGroup (r : MultiplierShape) : Group r.Carrier := by
  cases r <;> unfold MultiplierShape.Carrier <;> infer_instance

/-- All source model conditions, through actual carrier equivalences.
Finite field witnesses in `IsPSL` enforce the prime-power restriction.
The unitary parameter is the fixed-field order, with coefficient field of
its square order and the specified Frobenius conjugation. -/
def MultiplierRow (S : Type u) [Group S] : MultiplierShape → Prop
  | .two => ClassicalGroup.IsPSL S 4 2 ∨ ClassificationModels.IsG2At S 4 ∨
      Nonempty (S ≃* Sporadic.Mathieu.M12) ∨
      Nonempty (S ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty (S ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty (S ≃* Rudvalis.Model) ∨
      ∃ q : ℕ, Odd q ∧ q ≠ 9 ∧ ClassicalGroup.IsPSL S 2 q
  | .three => (¬ ClassicalGroup.IsPSL S 3 4) ∧
      ((∃ q : ℕ, q % 3 = 1 ∧ ClassicalGroup.IsPSL S 3 q) ∨
       ∃ p f : ℕ, p.Prime ∧ 0 < f ∧ (p ^ f) % 3 = 2 ∧
         ClassicalGroup.IsPSU S 3 (p ^ f))
  | .six => Nonempty (S ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (S ≃* alternatingGroup (Fin 7))
  | .twelve => Nonempty (S ≃* Sporadic.Mathieu.M22)
  | .elementaryFour => Nonempty (S ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)
  | .exceptionalFortyEight => ClassicalGroup.IsPSL S 3 4

/-- Both exhaustiveness and every multiplier identification in I.1.3.
In particular the exceptional order-48 multiplier is not declared cyclic. -/
structure MultiplierTable (S : Type u) [Group S] [Group.IsPerfect S] : Prop where
  exhaustive : Nontrivial (schurMultiplier S) ↔ ∃ r, MultiplierRow S r
  values : ∀ r, MultiplierRow S r → Nonempty (schurMultiplier S ≃* r.Carrier)


/-- The full source statement, for the complete known-simple K-class. -/
def SourceStatement : Prop :=
  ∀ (S : Type u) [Group S] [Finite S] [Group.IsPerfect S] [IsSimpleGroup S],
    IsSQTK KnownSimple.IsKnownSimple S → MultiplierTable S

/-- An individual catalogue calculation either proves vanishing or supplies
an actual source row with its full canonical-kernel isomorphism. -/
def Calculated (S : Type u) [Group S] [Group.IsPerfect S] : Prop :=
  Subsingleton (schurMultiplier S) ∨
    ∃ r, MultiplierRow S r ∧ Nonempty (schurMultiplier S ≃* r.Carrier)

instance MultiplierShape.carrierNontrivial (r : MultiplierShape) : Nontrivial r.Carrier := by
  let : Fact (1 < 6) := ⟨by decide⟩
  let : Fact (1 < 12) := ⟨by decide⟩
  cases r <;> unfold MultiplierShape.Carrier <;> infer_instance

/-- A calculation plus the independently established row values proves the
exhaustive iff. In the vanishing branch, nontriviality is impossible. -/
theorem table_of_calculated
    {S : Type u} [Group S] [Group.IsPerfect S] (h : Calculated S)
    (hv : ∀ r, MultiplierRow S r → Nonempty (schurMultiplier S ≃* r.Carrier)) :
    MultiplierTable S := by
  refine ⟨⟨?_, ?_⟩, hv⟩
  · intro hn
    rcases h with hz | ⟨r, hr, _⟩
    · exact (not_nontrivial_iff_subsingleton.mpr hz hn).elim
    · exact ⟨r, hr⟩
  · rintro ⟨r, hr⟩
    obtain ⟨e⟩ := hv r hr
    exact e.surjective.nontrivial

end CFSG.Quasithin.ChapterI.SQTKMultipliers
