module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import ABG.Basic
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Transport to the concrete standard PSU₃ model

An orthonormal Hermitian basis identifies an arbitrary nondegenerate form
with the identity form. A finite-field equivalence then identifies its
quadratic coefficient field with GF(p²); compatibility with Frobenius proves
that this really carries the unitary equations. Both equivalences descend
to the actual images in PGL, using the existing general matrix transport API.

Centralizers and their first commutator subgroups transport through genuine
group equivalences. Source: Aschbacher–Smith A.3.21(a), printed p.55, and
Huppert II.10.4(a).
-/

public noncomputable section

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
namespace Matrix.SU3.InnerThreeRank

/-- Every allowed ternary Hermitian model is the standard concrete PSU₃(p). -/
theorem exists_projective_equiv_standard (p : ℕ) [Fact p.Prime]
    (E : Type*) [Field E] [Finite E] (J : HermitianForm 3 E)
    (hcard : Nat.card E = p ^ 2) (hc : ∀ x, J.conj x = x ^ p) :
    Nonempty (ProjectiveSpecialUnitaryMatrixGroup J ≃*
      ProjectiveSpecialUnitaryMatrixGroup (ABG.unitaryForm 3 p 1 (by decide))) := by
  classical
  let : Fintype E := Fintype.ofFinite E
  let : CharP E p := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨C, hC⟩ := J.exists_orthonormal_basis_of_prime_frobenius hc hcard
  let F := GaloisField p (2 * 1)
  let : Fintype F := Fintype.ofFinite F
  let e : E ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard]
    exact (GaloisField.card p (2 * 1) (by decide)).symm)
  let K := ABG.unitaryForm 3 p 1 (by decide)
  have hK (x : F) : K.conj x = x ^ p := by
    simp only [K, ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one]
  let ec := projectiveCoefficientEquiv (n := 3) e J.conj J.conj_involutive
    K.conj K.conj_involutive (by intro x; rw [hc, hK, map_pow])
  exact ⟨(projectiveBasisEquiv J C hC).trans ec⟩

/-- An equivalence restricts to the centralizers of corresponding elements. -/
def centralizerEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (z : G) :
    Subgroup.centralizer ({z} : Set G) ≃* Subgroup.centralizer ({e z} : Set H) where
  toFun x := ⟨e x, Subgroup.mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using congrArg e
      (Subgroup.mem_centralizer_singleton_iff.mp x.property))⟩
  invFun x := ⟨e.symm x, Subgroup.mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      Subgroup.mem_centralizer_singleton_iff.mp x.property)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_mul' x y := Subtype.ext (e.map_mul x y)

/-- An equivalence restricts to the first commutator subgroups. -/
def commutatorEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    commutator G ≃* commutator H :=
  (e.subgroupMap (commutator G)).trans (MulEquiv.subgroupCongr (by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl))

end Matrix.SU3.InnerThreeRank
