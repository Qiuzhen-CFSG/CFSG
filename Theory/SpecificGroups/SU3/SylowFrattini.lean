module
public import Theory.SpecificGroups.SU3.BinaryRootFrattini
public import Theory.SpecificGroups.SU3.SylowOmega

/-!
# Sylow involutions lie in the binary unitary Frattini subgroup

The Hermitian root coordinates identify their square-one elements with
the first-coordinate kernel, and norm surjectivity expresses every such
element as a square. Thus the first omega subgroup lies in the Frattini
subgroup. A genuine change of Hermitian basis and Sylow conjugacy carry
this to every projective Sylow subgroup. The literal scalar projection
is injective on two-subgroups, giving the same result in the full special
unitary group. All positive fixed-field degrees, including one, are covered.

Source: Huppert II.10.4 and II.10.12, through BinaryRootFrattini and the
existing projective Sylow coordinates. The concrete consumer is the
noncommuting beta-model exclusion in DGS (10.7), pp.158--159.
-/

public noncomputable section
open Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.SylowFrattini
open OddPrimeSylow.NormalizedOuter.FormTransport
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

private instance projectiveFinite : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
  Finite.of_surjective J.specialToProjective J.specialToProjective_surjective

private noncomputable def projectiveCoordinates
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2 ^ n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    P ≃* hermitianUnipotentCoord (standardForm J) := by
  let e := Classical.choice (exists_projectiveEquiv J (2^n) hcard hfixed)
  let T := P.mapSurjective (f := e.toMonoidHom) e.surjective
  exact ((P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).equivMapOfInjective e.toMonoidHom e.injective).trans
    ((T.equiv (EvenTwoRank.rootSylow (standardForm J) rfl hn hcard hfixed)).trans
      (MonoidHom.ofInjective (EvenInner.root_injective (standardForm J) rfl)).symm)

private theorem omega_le_frattini_of_coordinates [CharP E 2]
    {H : Type*} [Group H] (P : Subgroup H) {q : ℕ}
    (hcard : Nat.card E = q^2) (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (e : P ≃* hermitianUnipotentCoord J) :
    omegaOneAmbient P ≤ (frattini P).map P.subtype := by
  apply (omegaOneAmbient_le_iff _ _).mpr
  intro x hx hs
  exact ⟨⟨x,hx⟩,(BinaryRootFrattini.equiv_structure J hcard hfixed e).1 _ |>.mpr
    (Subtype.ext hs),rfl⟩

/-- Every projective-unitary Sylow involution lies in its intrinsic
Frattini subgroup, viewed under the same ambient embedding. -/
theorem projective_omega_le_frattini
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2 ^ n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    omegaOneAmbient (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≤
      (frattini P).map (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  exact omega_le_frattini_of_coordinates (standardForm J) (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) hcard hfixed
    (projectiveCoordinates J hn hcard hfixed P)

/-- The same property holds in the full special-unitary group, retaining
the scalar center and the literal special-to-projective map. -/
theorem special_omega_le_frattini
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2 ^ n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (P : Sylow 2 J.specialSubgroup) :
    omegaOneAmbient (P : Subgroup J.specialSubgroup) ≤
      (frattini P).map (P : Subgroup J.specialSubgroup).subtype := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  exact omega_le_frattini_of_coordinates (standardForm J) (P : Subgroup J.specialSubgroup) hcard hfixed
    ((SylowOmega.specialSylowEquivProjective J P).trans
      (projectiveCoordinates J hn hcard hfixed _))

end BenderSuzuki.MatrixGroups.HermitianForm.SylowFrattini
