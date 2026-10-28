module

public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Fusion.Certificate

/-!
# All involutions in the concrete Mathieu group M23 are conjugate

The certificate module supplies an explicitly enumerated subgroup of order 128
and conjugating words for every involution in it. Since 128 is the full 2-part
of |M23|, every involution is conjugate into this subgroup by the Sylow theorems.
Thus the computation proves exhaustiveness in the actual design automorphism
group, without a class-table assumption.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma 5.2.21, printed p.657 (PDF p.674).
-/

namespace Sporadic.Mathieu.M23Geometry

/-- Every involution is conjugate to the certified permutation representative. -/
public theorem involution_isConj_representative (x : M23) (hx : orderOf x = 2) :
    IsConj x FusionCertificate.representative := by
  obtain ⟨y, hxy⟩ := FusionCertificate.sylow.exists_isConj_of_orderOf_eq_prime_pow
    (n := 1) (by simpa using hx)
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  have hy : orderOf (y : M23) = 2 := by
    rw [← hg, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hx]
  exact hxy.trans (FusionCertificate.local_fusion y hy)

/-- Exhaustive involution fusion in the actual automorphism group of W23. -/
public theorem involutions_isConj (x y : M23)
    (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y :=
  (involution_isConj_representative x hx).trans
    (involution_isConj_representative y hy).symm

end Sporadic.Mathieu.M23Geometry
