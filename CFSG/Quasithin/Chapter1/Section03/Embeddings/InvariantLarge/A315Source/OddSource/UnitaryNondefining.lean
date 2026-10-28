module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.OddSource.FrattiniSquare
public import Theory.SpecificGroups.SU3.ThreeWeightLift.Square
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
/-!
# The nondefining odd PSU₃ branch of the original intrinsic pair

Normalize the stored Hermitian form while preserving the field involution
and the actual projective group. The two-power actor lifts to SU₃ with a
natural or contragredient matrix formula, so its square fixes the p-subgroup.
Transport through the marked component then contradicts the original
Frattini commutator identity. No action or subgroup-placement premise remains.
Source: Aschbacher–Smith, A.3.15 and Proposition 1.3.4, pp.50–51, 510–511.
-/
public section
noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open HermitianForm.OddPrimeSylow.NormalizedOuter
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.OddSource
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {D B : Subgroup G} {S : Sylow 2 G} {p q : ℕ}

theorem not_unitary_nondefining
    (h : OddCartan.AmbientInput κ D B S p)
    (ha : SourceTransport.PairAction p (S : Subgroup G) B)
    (hq : q.Prime) (ho : Odd q) (hpq : p≠q)
    (hm : ClassicalGroup.IsPSU D 3 q) : False := by
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨h.prime⟩
  let : Fact q.Prime := ⟨hq⟩
  let _ := Fintype.ofFinite F
  let _ : CharP F q := charP_of_card_eq_prime_pow (f:=2) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  have hfixed : Nat.card {x:F // J.conj x=x}=q := by
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj q 1 (by decide)
        (by simpa only [pow_one] using hF) (by simpa only [pow_one] using hconj)
  obtain ⟨eJ⟩ := FormTransport.exists_projectiveEquiv J q hF hfixed
  let e' := e.trans eJ
  let _ : IsSimpleGroup D := h.simple
  let _ : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J)) :=
    e'.symm.isSimpleGroup
  apply false_of_component_square h ha e'
  intro P hP β hβ hstable
  exact HermitianForm.ThreeWeightLift.square_on_pSubgroup (FormTransport.standardForm J)
    hq ho hF hfixed rfl h.large hpq β hβ P hP hstable
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.OddSource
