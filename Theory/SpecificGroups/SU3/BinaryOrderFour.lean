module
public import Theory.SpecificGroups.SU3.EvenSemilinear.Coordinates
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# An element of order four in binary projective unitary groups

Choose a Hermitian root element with first coordinate one. Its square has
coordinates (0,1), and its fourth power is one. The root embedding in the
projective group is injective. A genuine Hermitian basis change transports
the element to the original form, retaining its stored field involution.

Source: Huppert II.10.4 and II.10.12, the Hermitian unipotent coordinates.
-/

public noncomputable section
open BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.BinaryOrderFour
open OddPrimeSylow.NormalizedOuter.Coverage
open OddPrimeSylow.NormalizedOuter.FormTransport
variable {E : Type*} [Field E] [Finite E]

/-- Every actual PSU₃ over a positive-degree binary fixed field has an
element of order four, for the specified Hermitian form. -/
theorem exists_order_four (J : HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n)) :
    ∃ g : ProjectiveSpecialUnitaryMatrixGroup J, orderOf g = 4 := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa only [pow_mul, Nat.card_eq_fintype_card] using hcard)
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  let K := standardForm J
  obtain ⟨e⟩ := exists_projectiveEquiv J (2 ^ n) hcard hfixed
  obtain ⟨z, hz⟩ := EvenSemilinear.coord_first_surjective K hcard hfixed 1
  have hs : z ^ 2 ≠ 1 := by
    intro he
    have hh := (EvenSemilinear.square_eq_one_iff_first_zero K z).mp he
    exact one_ne_zero (hz.symm.trans hh)
  have hf : z ^ 4 = 1 := by
    rw [show 4 = 2 * 2 by decide, pow_mul,
      EvenSemilinear.square_eq_one_iff_first_zero]
    exact congrArg Prod.fst (EvenInner.square_coordinates K z)
  have ho : orderOf z = 4 :=
    @orderOf_eq_prime_pow _ _ z 1 2 ⟨Nat.prime_two⟩ hs hf
  let g := root K rfl z
  have hg : orderOf g = 4 :=
    (orderOf_injective (root K rfl) (root_injective K rfl) z).trans ho
  exact ⟨e.symm g, (e.symm.orderOf_eq g).trans hg⟩

end BenderSuzuki.MatrixGroups.HermitianForm.BinaryOrderFour
