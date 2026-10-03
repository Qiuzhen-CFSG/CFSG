module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityThreeGenerators
public import Theory.SpecificGroups.ReeTwo.CollectedOperations

/-!
# Coordinates and finite counting contract for the long rank-three parity rows

Local rows 0, 1, 2 denote global rows 0, 1, 5 (labels 76, 209, 478).
The cyclic-four coordinate and seven, six, or five free binary core coordinates
parametrize the proposed carriers. Reading these free coordinates is inverse
to the parametrization, independently of any subgroup or order assertion.

The quotient coordinates use the basis convention of `SmallParityProfiles`.
The finite counts below use collected powers and multiplication, so their
certificates can be proved independently of the identification of the carriers
with the original generator closures. That identification, multiplicativity,
and the Frattini-kernel theorem remain separate obligations.

Source: Shinoda (1975), (2.3), pp. 81–82, through the verified Sylow model and
`CollectedOperations`; the exact original generators and profile conventions
are in `SmallParityThreeGenerators` and `SmallParityProfiles`.
-/

@[expose] public section
namespace ReeTwo.SylowModel.SmallParityLong
set_option maxRecDepth 32768

def index : Fin 3 → Fin 6 := ![0,1,5]
abbrev Parameters (c : Fin 3) := FiveFour.Cyclic 4 × (Fin (7-c.val) → ZMod 2)
def bit (c : Fin 3) (p : Parameters c) (j : ℕ) : ZMod 2 :=
  p.2 ⟨j % (7-c.val), Nat.mod_lt _ (by omega)⟩
def element (c : Fin 3) (p : Parameters c) : SylowModel :=
  let t₀ : ZMod 2 := p.1.toAdd.val
  let t₁ : ZMod 2 := (p.1.toAdd.val / 2 : ℕ)
  ⟨⟨t₀, t₀+t₁, t₀+t₀*t₁, bit c p 0, bit c p 1,
    if c = 0 then bit c p 5 else t₁+t₀*t₁+t₀*bit c p 0+bit c p 1,
    if c = 2 then t₁+t₀*t₁+t₀*bit c p 0+t₀*bit c p 1
      else bit c p (if c = 0 then 6 else 5),
    bit c p 2, bit c p 3, bit c p 4⟩, p.1⟩
def parameters (c : Fin 3) (x : SylowModel) : Parameters c :=
  (x.right, fun j =>
    (![x.left.b3, x.left.b4, x.left.b7, x.left.b8, x.left.b9,
       if c = 0 then x.left.b5 else x.left.b6, x.left.b6] : Fin 7 → ZMod 2)
      ⟨j.val, by have := j.isLt; omega⟩)
def carrier (c : Fin 3) (x : SylowModel) : Prop :=
  element c (parameters c x) = x
instance (c : Fin 3) (x : SylowModel) : Decidable (carrier c x) :=
  inferInstanceAs (Decidable (_ = _))

def coordinates (c : Fin 3) (x : SylowModel) : SmallParityThreeQuotient :=
  let b := x.left
  let t₀ : ZMod 2 := x.right.toAdd.val
  let t₁ : ZMod 2 := (x.right.toAdd.val / 2 : ℕ)
  Multiplicative.ofAdd ![t₀+t₁+t₀*t₁+b.b3, t₁+t₀*t₁+b.b3,
    (![b.b3+t₀*b.b3+b.b4+b.b5,
       b.b3+t₀*b.b3+t₀*b.b4+b.b6,
       b.b3+t₀*b.b3+t₀*t₁*b.b3+b.b4+t₁*b.b4+b.b7] : Fin 3 → ZMod 2) c]

theorem parameters_element (c : Fin 3) (p : Parameters c) : parameters c (element c p) = p := by
  rcases p with ⟨t,w⟩
  apply Prod.ext
  · rfl
  · funext i; fin_cases c <;> fin_cases i <;> rfl

/-- The exact original subgroup; no carrier identification is built into this abbreviation. -/
abbrev Candidate (c : Fin 3) := smallParityTwoCandidate (smallParityThreeIndex (index c))

/-- The proposed carrier has the stated independent finite parameters. -/
def carrierEquiv (c : Fin 3) : Parameters c ≃ {x : SylowModel // carrier c x} where
  toFun p := ⟨element c p, by unfold carrier; rw [parameters_element]⟩
  invFun x := parameters c x.val
  left_inv := parameters_element c
  right_inv x := Subtype.ext x.property

theorem carrier_card (c : Fin 3) :
    Nat.card {x : SylowModel // carrier c x} = 2 ^ (9-c.val) := by
  rw [← Nat.card_congr (carrierEquiv c)]
  fin_cases c <;> simp [Parameters, FiveFour.Cyclic]

set_option maxHeartbeats 8000000 in
/-- Values on the original basis lifts, checked against the actual root words. -/
theorem coordinates_basis : ∀ (c : Fin 3) (j : Fin 3),
    coordinates c (smallParityThreeBasisLift (index c) j).val =
      smallParityThreeBinaryBasis j := by decide +kernel

/-- Number of commuting parameters; transfer to an intrinsic centralizer count
requires the exact carrier-to-candidate equivalence. -/
def commutingCount (c : Fin 3) (x : SylowModel) : ℕ :=
  Fintype.card {p : Parameters c //
    collectedMul (element c p) x = collectedMul x (element c p)}

/-- Power tests for the only orders appearing in these three profile rows. -/
def orderTest (n : ℕ) (x : SylowModel) : Prop :=
  if n = 2 then collectedPow x 2 = 1 ∧ x ≠ 1
    else collectedPow x 4 = 1 ∧ collectedPow x 2 ≠ 1

instance (n : ℕ) (x : SylowModel) : Decidable (orderTest n x) := by
  unfold orderTest
  infer_instance

/-- The raw finite version of the specified intrinsic predicate. -/
def test (c k : Fin 3) (x : SylowModel) : Prop :=
  let t := smallParityThreeTests (index c) k
  orderTest t.1 x ∧ commutingCount c x = t.2.1 ∧
    (t.2.2 = 0 ∨ commutingCount c (collectedPow x 2) = t.2.2)

instance (c k : Fin 3) (x : SylowModel) : Decidable (test c k x) := by
  unfold test
  infer_instance

/-- The finite count to be transported to the quotient homomorphism's fibers. -/
def fiberCount (c k : Fin 3) (v : SmallParityThreeQuotient) : ℕ :=
  Fintype.card {p : Parameters c //
    coordinates c (element c p) = v ∧ test c k (element c p)}

/-- Orders are only two or four, and these rows never test the square centralizer. -/
theorem tests_spec : ∀ c k : Fin 3,
    ((smallParityThreeTests (index c) k).1 = 2 ∨
      (smallParityThreeTests (index c) k).1 = 4) ∧
    (smallParityThreeTests (index c) k).2.2 = 0 := by decide +kernel

end ReeTwo.SylowModel.SmallParityLong
