module

public import Theory.SpecificGroups.SU3.OddRootFixers.NormalForms
public import Theory.SpecificGroups.SU3.OddRootFixers.TriangularConjugacy.FourthPower

/-!
# Odd triangular unitary actors are conjugate to diagonal actors

A root conjugation diagonalizes the fourth power of an upper triangular unitary
representative with equal outer entries. An odd-order automorphism is a power
of its own fourth power, so the conjugated actor has a diagonal representative.
This uses the order of the actual automorphism throughout; it does not assume
that a chosen unitary representative has odd order. The power formula also holds
without faithfulness, so the scalar kernel in the literal projective image
requires no choice of a lift of odd order. Identity actors are included.

The conjugating element lies in the canonical special-unitary root group, and
its projective image lies in the canonical projective root group. Thus the new
conjugating automorphism preserves the specified Sylow placement.

Source: the diagonal-complement step of GLS4, Chapter 4, Lemma 3.6(c,d), used
in Chapter 2, Lemma 13.2. The triangular normal form is an explicit premise;
field elimination and the intrinsic root-fixer assembly supply that premise.
-/

open Matrix BenderSuzuki.External Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddRootFixers
open BorelTorus

private theorem actor_pow_formula {D G : Type*} [Group D] [Group G]
    (f : D →* G) (a : MulAut D) (v : G)
    (ha : ∀ x, f (a x) = v * f x * v⁻¹) (k : ℕ) (x : D) :
    f ((a ^ k) x) = v ^ k * f x * (v ^ k)⁻¹ := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, ih, ha, pow_succ]
    group

private theorem odd_actor_formula {D G : Type*} [Group D] [Group G]
    (f : D →* G) (a : MulAut D) (v : G)
    (ha : ∀ x, f (a x) = v * f x * v⁻¹) (hodd : Odd (orderOf a)) :
    ∃ k : ℕ, ∀ x, f (a x) = (v ^ 4) ^ k * f x * ((v ^ 4) ^ k)⁻¹ := by
  have hcop : Nat.Coprime 4 (orderOf a) := (Nat.coprime_two_left.mpr hodd).pow_left 2
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime (x := a) hcop
  exact ⟨k, fun x => by simpa only [pow_mul, hk] using actor_pow_formula f a v ha (4 * k) x⟩

private theorem conjugate_formula {D G : Type*} [Group D] [Group G]
    (f : D →* G) (a : MulAut D) (u : G)
    (ha : ∀ x, f (a x) = u * f x * u⁻¹) (r : D) (x : D) :
    f (MulAut.congr (MulAut.conj r) a x) =
      (f r * u * (f r)⁻¹) * f x * (f r * u * (f r)⁻¹)⁻¹ := by
  change f (r * a (r⁻¹ * x * r) * r⁻¹) = _
  simp only [map_mul, map_inv, ha]
  group

private theorem marked_conj {G : Type*} [Group G]
    (P R : Subgroup G) (e : MulAut G) (he : P.map e.toMonoidHom = R)
    (r : G) (hr : r ∈ R) :
    P.map (e.trans (MulAut.conj r)).toMonoidHom = R := by
  change P.map ((MulAut.conj r).toMonoidHom.comp e.toMonoidHom) = R
  rw [← Subgroup.map_map, he]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (R.le_normalizer hr)

private theorem congr_trans_inner {G : Type*} [Group G] (e a : MulAut G) (r : G) :
    MulAut.congr (e.trans (MulAut.conj r)) a =
      MulAut.congr (MulAut.conj r) (MulAut.congr e a) := by
  ext x
  rfl

variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  {n : ℕ} (hcard : Nat.card E = (2 ^ n) ^ 2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)

include hcard in
private theorem binary_charTwo : CharP E 2 := by
  let := Fintype.ofFinite E
  apply charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
  simpa [Nat.card_eq_fintype_card, pow_mul] using hcard

include hcard hfixed in
/-- Odd order turns a marked triangular formula on SU₃ into a marked diagonal formula. -/
public theorem special_diagonal_form_of_triangular
    (P : Sylow 2 J.specialSubgroup) (a : MulAut J.specialSubgroup)
    (hodd : Odd (orderOf a))
    (hform : HasSpecialRootForm J hJ (IsRootTriangular J) P a) :
    HasSpecialRootForm J hJ (IsRootDiagonal J) P a := by
  let : CharP E 2 := binary_charTwo hcard
  obtain ⟨e, u, hu, hP, ha⟩ := hform
  obtain ⟨r, v, hr, hv, hd⟩ := exists_root_conjugate_fourth_diagonal J hJ hcard hfixed u hu
  let e' := e.trans (MulAut.conj r)
  let b := MulAut.congr e' a
  have hb : Odd (orderOf b) := by simpa only [b, MulEquiv.orderOf_eq] using hodd
  have hbf (x : J.specialSubgroup) : (b x).val = v.val * x.val * v.val⁻¹ := by
    dsimp only [b, e']
    rw [congr_trans_inner, hv]
    exact conjugate_formula J.specialSubgroup.subtype (MulAut.congr e a) u.val ha r x
  obtain ⟨k, hk⟩ := odd_actor_formula J.specialSubgroup.subtype b v.val hbf hb
  refine ⟨e', (v ^ 4) ^ k, IsRootDiagonal.pow J _ hd k,
    marked_conj _ _ e hP r hr, ?_⟩
  exact hk

include hcard hfixed in
/-- The same diagonalization on the literal projective special unitary group,
with the quotient map retained in the actor formula. -/
public theorem projective_diagonal_form_of_triangular
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hodd : Odd (orderOf a))
    (hform : HasProjectiveRootForm J hJ (IsRootTriangular J) P a) :
    HasProjectiveRootForm J hJ (IsRootDiagonal J) P a := by
  let : CharP E 2 := binary_charTwo hcard
  obtain ⟨e, u, hu, hP, ha⟩ := hform
  obtain ⟨r, v, hr, hv, hd⟩ := exists_root_conjugate_fourth_diagonal J hJ hcard hfixed u hu
  let rp := J.specialToProjective r
  have hrp : rp ∈ projectiveRoot J hJ := by
    obtain ⟨z, hz⟩ := hr
    refine ⟨z, Subtype.ext ?_⟩
    change ProjGenLinGroup.mk (hermitianUnipotentGL J z) = (J.specialToProjective r).val
    rw [J.specialToProjective_apply_val, ← hz]
    rfl
  have hrpv : rp.val = ProjGenLinGroup.mk r.val := J.specialToProjective_apply_val r
  let e' := e.trans (MulAut.conj rp)
  let b := MulAut.congr e' a
  have hb : Odd (orderOf b) := by simpa only [b, MulEquiv.orderOf_eq] using hodd
  have hbf (x : ProjectiveSpecialUnitaryMatrixGroup J) :
      (b x).val = ProjGenLinGroup.mk v.val * x.val * (ProjGenLinGroup.mk v.val)⁻¹ := by
    dsimp only [b, e']
    rw [congr_trans_inner, hv, map_mul, map_mul, map_inv, ← hrpv]
    apply conjugate_formula (ProjectiveSpecialUnitaryMatrixGroup J).subtype
      (MulAut.congr e a) (ProjGenLinGroup.mk u.val) _ rp x
    intro y
    rw [ha]
    exact J.unitaryConj_apply_val u y
  obtain ⟨k, hk⟩ := odd_actor_formula (ProjectiveSpecialUnitaryMatrixGroup J).subtype
    b (ProjGenLinGroup.mk v.val) hbf hb
  refine ⟨e', (v ^ 4) ^ k, IsRootDiagonal.pow J _ hd k,
    marked_conj _ _ e hP rp hrp, ?_⟩
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [J.unitaryConj_apply_val]
  simpa only [b, Subgroup.subtype_apply, Subgroup.coe_pow, map_pow] using hk x

end BenderSuzuki.MatrixGroups.HermitianForm.OddRootFixers
