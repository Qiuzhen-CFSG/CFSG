module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.SemidihedralTorus.CyclicExtraction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.SemidihedralTorus.Model
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.SemidihedralTorus.ActorCoordinates
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.ProjectiveLinearInvolutions
public import Mathlib.GroupTheory.Sylow

/-!
# The odd torus obstruction from four-group centralizer coordinates

The explicit matrix torus and the cyclic extraction give an odd-prime
subgroup normalized by the full C_T(A), with commutator outside C_G(z).
The normal socle is embedded through its actual subtype map, so this
application retains all ambient two-extensions. It needs no SQTK hypothesis.

Simultaneous coordinates for the marked four-group put every element of
C_T(A) into the sign/Frobenius formula. The final `escape_of_isPSU` theorem
discharges this placement from the actual projective unitary model, with
arbitrary nondegenerate Hermitian form over the original field of order p².
Only normality and simplicity of the modeled subgroup are needed; hence the
result applies to the generalized Fitting subgroup in the source setup.

Source: Aschbacher--Smith E.1.14(7), printed p.214, and A.3.21, printed p.55;
Aschbacher, GF(2)-representations of finite groups (1982), Lemma 4.11.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.SemidihedralTorus
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

/-- The literal odd-prime obstruction, conditional only on the specified coordinate placement. -/
theorem escape_of_sign_coordinates (L : Subgroup G) [L.Normal]
    (J : HermitianForm 3 F) (hJ : J.form = 1)
    (e : L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    {p : ℕ} (hp : 1 < p) (ho : Odd p) (hm : p % 4 = 1)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (T : Sylow 2 G) (A : Subgroup G) (z : L) (hz : (z : G) ∈ A)
    (hez : e z = J.specialToProjective (Matrix.SU3.standardInvolution J hJ))
    (hcoord : ∀ g ∈ (T : Subgroup G) ⊓ centralizer (A : Set G),
      HasSignSemilinearForm J (MulAut.congr e (MulAut.conjNormal g))) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ ∃ X : Subgroup G,
      IsPGroup r X ∧
      (T : Subgroup G) ⊓ centralizer (A : Set G) ≤ normalizer (X : Set G) ∧
        ¬ ⁅X, A⁆ ≤ centralizer ({(z : G)} : Set G) := by
  have h2 : (2 : F) ≠ 0 := Field.two_ne_zero_of_odd_card F (by rw [hcard]; exact ho.pow)
  let D := (projectiveRotation J hJ h2).range
  let : IsCyclic D := projectiveRotation_isCyclic J hJ h2
  apply escape_of_model_torus L e A ((T : Subgroup G) ⊓ centralizer (A : Set G))
    D hp hm (projectiveRotation_card J hJ h2 hcard hc) z hz
  · rw [hez]
    exact projectiveRotation_inverted J hJ h2
  · intro g hg x hx
    exact rotation_preserved_of_signSemilinear J hJ h2
      (MulAut.congr e (MulAut.conjNormal g)) (hcoord g hg) x hx

/-- The odd-prime obstruction for an arbitrary Hermitian model. Simultaneous
coordinates preserve the full ambient actor and discharge all geometric premises. -/
theorem escape_of_unitary_model (L : Subgroup G) [L.Normal] [IsSimpleGroup L]
    (J : HermitianForm 3 F) (e₀ : L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : p % 4 = 1)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (T : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 4) (hAL : A ≤ L)
    (z : G) (hz : orderOf z = 2) (hzA : z ∈ A) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ ∃ X : Subgroup G,
      IsPGroup r X ∧
      (T : Subgroup G) ⊓ centralizer (A : Set G) ≤ normalizer (X : Set G) ∧
        ¬ ⁅X, A⁆ ≤ centralizer ({z} : Set G) := by
  obtain ⟨e, hez, hcoord⟩ :=
    exists_sign_coordinates L J hp ho hm hcard hc e₀ T A hA hAL z hzA hz
  exact escape_of_sign_coordinates L (HermitianForm.IdentityGram.identityGram J) rfl
    e hp.one_lt ho hm hcard hc T A ⟨z, hAL hzA⟩ hzA hez hcoord

/-- The normalized odd-prime subgroup required in the semidihedral branch of
E.1.14(7). This stronger normal-subgroup version needs neither SQTK, the Sylow
supplement condition, nor centrality of the marked involution in the whole Sylow. -/
theorem escape_of_isPSU (L : Subgroup G) [L.Normal] [IsSimpleGroup L]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : p % 4 = 1)
    (hmodel : ClassicalGroup.IsPSU L 3 p)
    (T : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 4) (hAL : A ≤ L)
    (z : G) (hz : orderOf z = 2) (hzA : z ∈ A) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ ∃ X : Subgroup G,
      IsPGroup r X ∧
      (T : Subgroup G) ⊓ centralizer (A : Set G) ≤ normalizer (X : Set G) ∧
        ¬ ⁅X, A⁆ ≤ centralizer ({z} : Set G) := by
  obtain ⟨F, _, _, J, hcard, hc, ⟨e₀⟩⟩ := hmodel
  exact escape_of_unitary_model L J e₀ hp ho hm hcard hc T A hA hAL z hz hzA

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.SemidihedralTorus
