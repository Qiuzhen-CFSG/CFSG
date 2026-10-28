module
public import Theory.SpecificGroups.SU3.SylowFrattini
public import Theory.GroupTheory.PGroup.OmegaCenterIn

/-!
# Binary unitary Sylow omega orders and indices

The first-coordinate homomorphism of the Hermitian root group has kernel
exactly its square-one elements. Those elements are central, so this kernel
is the full omega-center. Its quotient is the additive coefficient field,
of order q²; the root order q³ gives omega-center order q.

A Hermitian basis change and Sylow conjugacy transport the calculation to
any PSU₃ Sylow. The actual special-to-projective map identifies SU₃ Sylows
with their images, retaining both carriers and every positive degree,
including q=2. CoreProductOrders applies these two literal numerical
invariants to the DGS core-product comparison.
Source: Huppert II.10.4 and II.10.12; DGS, Groups and Graphs (1985),
(5.4) and (11.4), printed pp.106--107,171.
-/

public noncomputable section
open Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.SylowOmegaIndex
open OddPrimeSylow.NormalizedOuter.FormTransport
open OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
private instance : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

private theorem coordinates_index [CharP E 2]
    {H : Type*} [Group H] (P : Subgroup H)
    {q : ℕ} (hcard : Nat.card E = q^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (e : P ≃* hermitianUnipotentCoord J) :
    (omegaCenterIn P).relIndex P = q^2 := by
  let f := (BinaryRootFrattini.firstCoordinate J).comp e.toMonoidHom
  have hf : Function.Surjective f :=
    (BinaryRootFrattini.firstCoordinate_surjective J hcard hfixed).comp e.surjective
  have hk : (omegaCenterIn P).subgroupOf P = f.ker := by
    ext x
    change x.val ∈ omegaCenterIn P ↔ f x = 1
    rw [mem_omegaCenterIn_iff]
    have hs : x^2=1 ↔ f x=1 := by
      rw [←e.injective.eq_iff, map_pow, map_one, BinaryRootFrattini.square_one_iff]
      rfl
    constructor
    · intro hx
      exact hs.mp (Subtype.ext hx.2.2)
    · intro hx
      have hsq := hs.mpr hx
      have hz := (BinaryRootFrattini.equiv_structure J hcard hfixed e).2
        ((BinaryRootFrattini.equiv_structure J hcard hfixed e).1 x |>.mpr hsq)
      exact ⟨x.property,fun y hy => congrArg Subtype.val (mem_center_iff.mp hz ⟨y,hy⟩),
        congrArg Subtype.val hsq⟩
  change ((omegaCenterIn P).subgroupOf P).index = _
  rw [hk,index_ker,MonoidHom.range_eq_top.mpr hf,card_top]
  exact (Nat.card_congr Multiplicative.toAdd).trans hcard

private theorem coordinates_card_index [CharP E 2]
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {H : Type*} [Group H] (P : Subgroup H)
    {q : ℕ} (hq : 0 < q) (hcard : Nat.card E = q^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (e : P ≃* hermitianUnipotentCoord J) :
    Nat.card (omegaCenterIn P) = q ∧ (omegaCenterIn P).relIndex P = q^2 := by
  have hi := coordinates_index J P hcard hfixed e
  have hP : Nat.card P = q^3 :=
    (Nat.card_congr (e.trans (MonoidHom.ofInjective (root_injective J hJ))).toEquiv).trans
      (rootGroup_card J hJ q hcard hfixed)
  have hle : omegaCenterIn P ≤ P := map_subtype_le _
  have hm := ((omegaCenterIn P).subgroupOf P).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,hP] at hm
  change Nat.card (omegaCenterIn P) * (omegaCenterIn P).relIndex P = q^3 at hm
  rw [hi] at hm
  exact ⟨Nat.eq_of_mul_eq_mul_right (pow_pos hq 2) (hm.trans (by ring)),hi⟩

private def projectiveCoordinates {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    P ≃* hermitianUnipotentCoord (standardForm J) := by
  let e := Classical.choice (exists_projectiveEquiv J (2^n) hcard hfixed)
  let T := P.mapSurjective (f := e.toMonoidHom) e.surjective
  exact ((P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).equivMapOfInjective e.toMonoidHom e.injective).trans
    ((T.equiv (EvenTwoRank.rootSylow (standardForm J) rfl hn hcard hfixed)).trans
      (MonoidHom.ofInjective (EvenInner.root_injective (standardForm J) rfl)).symm)

/-- The exact omega-center order and index in any projective-unitary Sylow,
including fixed-field degree one. -/
theorem projective {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card (omegaCenterIn (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) = 2^n ∧
      (omegaCenterIn (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))).relIndex P = (2^n)^2 := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  exact coordinates_card_index (standardForm J) (H := ProjectiveSpecialUnitaryMatrixGroup J) rfl
    (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (q := 2^n) (by positivity) hcard hfixed
    (projectiveCoordinates J hn hcard hfixed P)

/-- The same calculation for the full special-unitary group, under its literal
scalar projection; no quotient by the scalar center is silently substituted. -/
theorem special {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (P : Sylow 2 J.specialSubgroup) :
    Nat.card (omegaCenterIn (P : Subgroup J.specialSubgroup)) = 2^n ∧
      (omegaCenterIn (P : Subgroup J.specialSubgroup)).relIndex P = (2^n)^2 := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  exact coordinates_card_index (standardForm J) (H := J.specialSubgroup) rfl
    (P : Subgroup J.specialSubgroup) (q := 2^n) (by positivity) hcard hfixed
    ((SylowOmega.specialSylowEquivProjective J P).trans
      (projectiveCoordinates J hn hcard hfixed _))
end BenderSuzuki.MatrixGroups.HermitianForm.SylowOmegaIndex
