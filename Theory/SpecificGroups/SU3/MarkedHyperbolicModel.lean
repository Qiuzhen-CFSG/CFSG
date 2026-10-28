module

public import Theory.SpecificGroups.SU3.MarkedHyperbolicModel.Plane
public import Theory.SpecificGroups.SU3.MarkedHyperbolicModel.Generators
public import Theory.SpecificGroups.SU3.MarkedHyperbolicModel.Sylow
public import Theory.SpecificGroups.SU3.CyclicCoreSylow.Order

/-!
# The full marked hyperbolic unitary Sylow model

For p congruent to one modulo four, the hyperbolic unitary plane maps into
SU₃ by inserting the inverse determinant on its orthogonal line. After
projective descent and inner conjugation, this map retains scalar minus
one, the rotation, the swap and the action of entrywise Frobenius on every
plane element. The exact two-part of p-1 supplies both the rotation and a
fixed square root of minus one. The strengthened cyclic Sylow construction
retains the generators while the existing order and coverage results prove
maximality in the full automorphism group.

Simplicity is inherited from the model application. No extra coordinate,
conjugator, abelian-centralizer or fusion premise is imposed.

Source: Aschbacher–Smith E.1.14(7), p.214, citing Aschbacher (1982),
Lemma 4.11; A.3.21(a,b), p.55; ABG II.2 Lemma 1.
-/

public section
open Matrix Subgroup BenderSuzuki.External Theory.GroupTheory Matrix.UnitaryQuaternionRotation
namespace BenderSuzuki.MatrixGroups.HermitianForm.MarkedHyperbolicModel
open OddPrimeSylow.NormalizedOuter

/-- The full marked plane in a Sylow subgroup of the actual automorphism group. -/
theorem exists_markedCyclicByFour_sylow
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hmod : p % 4 = 1)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) :
    ∃ (S : Sylow 2 (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
      (w : ProjectiveSpecialUnitaryMatrixGroup J) (J₂ : HermitianForm 2 F),
      orderOf w = 2 ∧ Nonempty (MarkedCyclicByFour
        (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
        (S : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) (MulAut.conj w) J₂) := by
  obtain ⟨n, hdiv, hodd⟩ := CyclicCoreSylow.exists_parameter hp hmod
  obtain ⟨k, _, hhalf, hk, hx, hy, hyx, hγx, hγy⟩ :=
    exists_marked_generators J hJ hp ho hcard hc n hdiv hodd
  obtain ⟨S, hw, q, ha, hb, hγ, _⟩ := exists_marked_sylow_of_generators J hJ hp ho hcard hc
    n (hermitianTorusPSU J hJ k) (hermitianWeylPSU J hJ) hx hy hyx
    (entrywiseProjectiveAut J hJ) (entrywiseProjectiveAut_isEntrywiseConjugation J hJ)
    hγx hγy (CyclicCoreSylow.two_subgroup_card_le J hJ hp ho hcard hc n hdiv hodd)
  obtain ⟨i, hi, hfix⟩ := fixed_sqrt_neg_one J k n hhalf hk
  let r : Fˣ := -k⁻¹
  have hr : (plane J).conj (r : F) = -(r : F) := by
    change J.conj ((-k⁻¹ : Fˣ) : F) = -((-k⁻¹ : Fˣ) : F)
    simp [hk]
  have hrot : projectiveBlock J hJ (torus (plane J) rfl r hr) =
      hermitianTorusPSU J hJ k := by
    exact (projectiveBlock_torus J hJ r hr).trans
      (congrArg (hermitianTorusPSU J hJ) (by simp [r]))
  have hmark : projectiveBlock J hJ (minusOne (plane J) rfl) =
      (hermitianTorusPSU J hJ k) ^ (2 ^ (n + 2)) := by
    rw [← map_pow, hhalf, projectiveBlock_minusOne]
  have h2 : (2 : F) ≠ 0 := Coverage.two_ne_zero_of_prime_square hp
    (by have := hp.two_le; omega) hcard
  refine ⟨S, (hermitianTorusPSU J hJ k) ^ (2 ^ (n + 2)), plane J, hw, ⟨{
    coordinates := q
    form_eq := rfl
    two_ne_zero := h2
    r := r
    r_conj := hr
    i := i
    i_sq := hi
    i_conj := hfix
    embedding := innerBlock J hJ
    embedding_inner := innerBlock_mem J hJ
    marker_eq := congrArg MulAut.conj hmark
    rotation_eq := ?_
    swap_eq := ?_
    actor_action := ?_ }⟩⟩
  · change MulAut.conj (projectiveBlock J hJ _) = q.a
    rw [hrot, ha]
  · change MulAut.conj (projectiveBlock J hJ _) = q.b
    rw [projectiveBlock_swap, hb]
  · intro A
    rw [hγ]
    exact innerBlock_fieldConj J hJ A

end BenderSuzuki.MatrixGroups.HermitianForm.MarkedHyperbolicModel
