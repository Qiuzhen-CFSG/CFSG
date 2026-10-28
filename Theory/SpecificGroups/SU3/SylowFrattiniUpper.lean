module
public import Theory.SpecificGroups.SU3.SylowFrattini
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.SpecificGroups.SU3.SylowOmega

/-!
# Frattini upper bounds in binary unitary Sylow subgroups

The existing Hermitian root coordinates put every Frattini element in the
center and give its square as one. The same coordinate equivalences transport
this inclusion to every Sylow of SU₃ and PSU₃, including fixed-field degree
one. Together with SylowFrattini this identifies the full Frattini layer.
The source consumer controls the image of Φ(Q_alpha) in the neighboring
unitary quotient in DGS85 (11.8), printed pp.175--176.
Source: Huppert II.10.4 and II.10.12, via BinaryRootFrattini.equiv_structure.
-/

public noncomputable section
open Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.SylowFrattiniUpper
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

private theorem frattini_le_omega_of_coordinates [CharP E 2]
    {H : Type*} [Group H] (P : Subgroup H) {q : ℕ}
    (hcard : Nat.card E = q^2) (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (e : P ≃* hermitianUnipotentCoord J) :
    (frattini P).map P.subtype ≤ omegaCenterIn P := by
  rintro x ⟨y,hy,rfl⟩
  have hs := BinaryRootFrattini.equiv_structure J hcard hfixed e
  exact (mem_omegaCenterIn_iff P y).mpr ⟨y.property,
    fun z hz => congrArg Subtype.val (mem_center_iff.mp (hs.2 hy) ⟨z,hz⟩),
    congrArg Subtype.val ((hs.1 y).mp hy)⟩

/-- The projective Sylow Frattini subgroup lies in its central omega layer. -/
theorem projective
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2 ^ n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    (frattini P).map (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype ≤
      omegaCenterIn (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  exact frattini_le_omega_of_coordinates (standardForm J) (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) hcard hfixed
    (projectiveCoordinates J hn hcard hfixed P)

/-- The special Sylow Frattini subgroup lies in its central omega layer. -/
theorem special
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2 ^ n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (P : Sylow 2 J.specialSubgroup) :
    (frattini P).map (P : Subgroup J.specialSubgroup).subtype ≤
      omegaCenterIn (P : Subgroup J.specialSubgroup) := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  exact frattini_le_omega_of_coordinates (standardForm J) (P : Subgroup J.specialSubgroup) hcard hfixed
    ((SylowOmega.specialSylowEquivProjective J P).trans
      (projectiveCoordinates J hn hcard hfixed _))

end BenderSuzuki.MatrixGroups.HermitianForm.SylowFrattiniUpper
