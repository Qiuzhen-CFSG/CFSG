module

public import CFSG.Quasithin.ChapterF.Section01.SourceCartan.Unitary.Small
public import CFSG.Quasithin.ChapterF.Section01.SourceCartan.Unitary.Semilinear
public import Theory.SpecificGroups.SU3.EvenSemilinear.SpecialCoverage
public import Theory.FieldTheory.QuadraticUnitAction
public import Theory.FieldTheory.CubicQuadraticUnitAction

/-!
# Unitary Cartan quadratic rigidity in F.1.3(5)

The special-unitary branch is proved for every positive binary exponent,
including SU₃(2). For larger fields its actual matrix semilinearity gives
the field action on the full torus, where the elementary quadratic-unit
identity forces the field automorphism to be identity. The order-three
small torus is handled separately. Sylow conjugacy, Hall conjugacy and an
actual Hermitian basis equivalence transport to every specified model.

The projective branch is also proved for every positive exponent. For larger
fields the literal projective torus kernel gives cubically trivial double
multiplicative displacement. Finite-field rigidity forces its coefficient
automorphism to be identity. PSU₃(2) uses its small torus separately.
Source: Aschbacher–Smith, F.1.3(5), printed p.260.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open BenderSuzuki.MatrixGroups.HermitianForm
open BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
namespace CFSG.Quasithin.ChapterF.Source.Unitary
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- The standard SU₃ pair is quadratically rigid for n ≥ 2 on the full torus. -/
theorem special_pairRigidity {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) :
    PairRigidity (specialRoot J hJ) (specialTorus J hJ) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa [Nat.card_eq_fintype_card, pow_mul] using hcard)
  apply special_pairRigidity_of_semilinear_and_field J hJ hcard
    (fixed_card J n (by omega) hcard hconj)
    (EvenSemilinear.special_semilinear_coverage J hJ hn hcard hconj)
  intro σ hq
  have hs : σ = 1 := RingEquiv.eq_one_of_quadratic_units σ
    (fun k => special_injective J hJ (hq k))
  subst σ
  intro k
  rfl

/-- Cartan rigidity in the actual SU₃ carrier, for every Hermitian form
and every positive exponent, with no extra action premise. -/
theorem special_cartanRigidity {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    CartanQuadraticRigidity J.specialSubgroup := by
  by_cases he : n = 1
  · subst n
    exact special_cartanRigidity_two J (by simpa using hcard) (by simpa using hconj)
  have hn2 : 2 ≤ n := by omega
  obtain ⟨C,hC⟩ := FormTransport.exists_standard_basis J n hn hcard hconj
  apply CartanQuadraticRigidity.of_equiv (FormTransport.specialEquiv J C hC)
  apply special_cartanRigidity_of_pair (FormTransport.standardForm J) hn hcard hconj rfl
  exact special_pairRigidity (FormTransport.standardForm J) hn2 hcard hconj rfl

/-- The projective step reduces to a cubic-kernel field assertion.
The kernel condition is proved using the literal projective torus map. -/
theorem projective_pairRigidity_of_cubic_field {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hfield : ∀ σ : F ≃+* F,
      (∀ k : Fˣ, (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom k * k⁻¹) *
        (Units.map σ.toMonoidHom k * k⁻¹)⁻¹) ^ 3 = 1) → σ = 1) :
    PairRigidity (projectiveRoot J hJ) (projectiveTorus J hJ) := by
  apply projective_pairRigidity_of_field J hJ hn hcard hconj
  intro σ hq
  have hs : σ = 1 := hfield σ (fun k => by
    apply ((projective_eq_one_iff J hJ _).mp ?_).2
    rw [map_mul, map_inv, hq, mul_inv_cancel])
  subst σ
  intro k
  rfl

/-- Conditional assembly for the actual projective carrier from the displayed
finite-field assertion, handling all forms, Sylows and complements. -/
theorem projective_cartanRigidity_of_cubic_field {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hfield : 2 ≤ n → ∀ σ : F ≃+* F,
      (∀ k : Fˣ, (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom k * k⁻¹) *
        (Units.map σ.toMonoidHom k * k⁻¹)⁻¹) ^ 3 = 1) → σ = 1) :
    CartanQuadraticRigidity (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (suProjection_surjective J)
  by_cases he : n = 1
  · subst n
    exact projective_cartanRigidity_two J (by simpa using hcard) (by simpa using hconj)
  have hn2 : 2 ≤ n := by omega
  obtain ⟨C,hC⟩ := FormTransport.exists_standard_basis J n hn hcard hconj
  apply CartanQuadraticRigidity.of_equiv (FormTransport.projectiveEquiv J C hC)
  apply projective_cartanRigidity_of_pair (FormTransport.standardForm J) hn hcard hconj rfl
  exact projective_pairRigidity_of_cubic_field (FormTransport.standardForm J)
    hn2 hcard hconj rfl (hfield hn2)

/-- Cartan rigidity in the actual PSU₃ carrier, for every Hermitian form
and every positive exponent. Cubic-kernel field rigidity discharges the
large-field premise; the small group is handled by its torus order. -/
theorem projective_cartanRigidity {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    CartanQuadraticRigidity (ProjectiveSpecialUnitaryMatrixGroup J) := by
  exact projective_cartanRigidity_of_cubic_field J hn hcard hconj
    (fun hn2 σ hq => RingEquiv.eq_one_of_cubic_quadratic_units hn2 hcard σ hq)

end CFSG.Quasithin.ChapterF.Source.Unitary

namespace CFSG.Quasithin.ChapterF.Source
variable {H : Type*} [Group H] [Finite H]

/-- The full special-unitary model branch of F.1.3(5), including SU₃(2). -/
theorem cartanQuadraticRigidity_special_unitary {n : ℕ} (hn : 0 < n)
    (hmodel : IsSU H 3 (2 ^ n)) : CartanQuadraticRigidity H := by
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hmodel
  exact CartanQuadraticRigidity.of_equiv e (Unitary.special_cartanRigidity J hn hcard hconj)

/-- The small projective model branch, without simplicity or semilinearity. -/
theorem cartanQuadraticRigidity_projective_unitary_two
    (hmodel : ClassicalGroup.IsPSU H 3 2) : CartanQuadraticRigidity H := by
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hmodel
  exact CartanQuadraticRigidity.of_equiv e (Unitary.projective_cartanRigidity_two J hcard hconj)

/-- The projective model assembly conditional solely on cubic-kernel
rigidity of its binary matrix field. -/
theorem cartanQuadraticRigidity_projective_unitary_of_cubic_field {n : ℕ} (hn : 0 < n)
    (hmodel : ClassicalGroup.IsPSU H 3 (2 ^ n))
    (hfield : ∀ (F : Type) [Field F] [Finite F], Nat.card F = (2 ^ n) ^ 2 →
      2 ≤ n → ∀ σ : F ≃+* F,
      (∀ k : Fˣ, (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom k * k⁻¹) *
        (Units.map σ.toMonoidHom k * k⁻¹)⁻¹) ^ 3 = 1) → σ = 1) :
    CartanQuadraticRigidity H := by
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hmodel
  exact CartanQuadraticRigidity.of_equiv e
    (Unitary.projective_cartanRigidity_of_cubic_field J hn hcard hconj (hfield F hcard))

/-- The full projective-unitary model branch of F.1.3(5), including PSU₃(2),
with no additional simplicity, semilinearity or field-action premise. -/
theorem cartanQuadraticRigidity_projective_unitary {n : ℕ} (hn : 0 < n)
    (hmodel : ClassicalGroup.IsPSU H 3 (2 ^ n)) : CartanQuadraticRigidity H := by
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hmodel
  exact CartanQuadraticRigidity.of_equiv e
    (Unitary.projective_cartanRigidity J hn hcard hconj)

end CFSG.Quasithin.ChapterF.Source
