module

public import Theory.SpecificGroups.SU3.OuterSylowFirstCoordinates
public import Theory.SpecificGroups.SU3.BinaryRootFrattini

/-!
# Square-one Sylow displacements force innerness in binary PSU₃

An outer square-one automorphism stabilizing the supplied Sylow and fixing a
nonidentity involution acts by Hermitian conjugation on its first coordinate.
If every displacement squares to one, the root square criterion makes its
first coordinate zero. Surjectivity of that coordinate then forces Hermitian
conjugation to be the identity, contradicting the two field cardinalities.

This applies the proved outer-coordinate theorem; it neither assumes pointwise
Sylow fixation nor classifies additional automorphisms. It supplies the unitary
whole-U action step in Aschbacher--Smith, Proposition 2.2.2, printed p.520.
-/

public section
open Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm
open BinaryRootFrattini
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

/-- Stabilizing a Sylow, fixing a nontrivial involution, and having square-one
displacements exclude the outer square-one action on the actual projective model. -/
theorem projective_inner_of_square_displacements
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1)
    (hstable : ∀ x, x ∈ P → a x ∈ P)
    (z : ProjectiveSpecialUnitaryMatrixGroup J) (hz : z ∈ P)
    (hne : z ≠ 1) (hz2 : z ^ 2 = 1) (hfix : a z = z)
    (hdisp : ∀ x ∈ P, (a x * x⁻¹) ^ 2 = 1) : ∃ g, a = MulAut.conj g := by
  classical
  by_contra houter
  let := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
    (by simpa only [← Nat.card_eq_fintype_card, pow_mul] using hcard)
  obtain ⟨c, hc⟩ := OuterSylowFirstCoordinates.projective_first_coordinates
    J hJ hn hcard hfixed P a ha houter hstable z hz hne hz2 hfix
  have hfirst (x : P) : (c ⟨a x, hstable x x.property⟩).val.1 = (c x).val.1 := by
    let ax : P := ⟨a x, hstable x x.property⟩
    have hd : (ax * x⁻¹) ^ 2 = 1 := Subtype.ext (hdisp x x.property)
    have hd' : (c (ax * x⁻¹)) ^ 2 = 1 := by rw [← map_pow, hd, map_one]
    have hzero := (square_one_iff J _).mp hd'
    have hk : firstCoordinate J (c (ax * x⁻¹)) = 1 :=
      congrArg Multiplicative.ofAdd hzero
    have he : firstCoordinate J (c ax) * (firstCoordinate J (c x))⁻¹ = 1 := by
      simpa only [map_mul, map_inv] using hk
    exact congrArg Multiplicative.toAdd (mul_inv_eq_one.mp he)
  apply J.conj_ne_one_of_card n hn hcard hfixed
  ext y
  change J.conj y = y
  obtain ⟨v, hv⟩ := firstCoordinate_surjective J hcard hfixed (Multiplicative.ofAdd y)
  obtain ⟨x, rfl⟩ := c.surjective v
  have hxy : (c x).val.1 = y := congrArg Multiplicative.toAdd hv
  have hh := (hc x).symm.trans (hfirst x)
  simpa only [hxy] using hh

end BenderSuzuki.MatrixGroups.HermitianForm
