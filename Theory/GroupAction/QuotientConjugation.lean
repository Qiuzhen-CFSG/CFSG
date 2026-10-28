module

public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Descending conjugation past a centralizing normal subgroup

If Q is normal in N and centralizes the normal subgroup D, the literal
conjugation homomorphism N → Aut(D) factors through N/Q. Its restriction
to the image of K ≤ N is trivial only if K centralizes D. The equations
below retain the quotient map and conjugation on representatives.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, Lemma 14.4.9, printed p.1010, with Q = O₂(N_G(D)).
-/

public section
open Subgroup
namespace MulAut
variable {N : Type*} [Group N]

/-- Conjugation on D, descended through the actual quotient by Q. -/
@[expose] def quotientConjNormal (D Q : Subgroup N) [D.Normal] [Q.Normal]
    (hQ : Q ≤ centralizer (D : Set N)) : N ⧸ Q →* MulAut D :=
  QuotientGroup.lift Q (conjNormal : N →* MulAut D)
    (by rwa [conjNormal_ker_eq_centralizer])

/-- The automorphism attached to the coset of n is conjugation by n. -/
theorem quotientConjNormal_mk (D Q : Subgroup N) [D.Normal] [Q.Normal]
    (hQ : Q ≤ centralizer (D : Set N)) (n : N) :
    quotientConjNormal D Q hQ (QuotientGroup.mk' Q n) = conjNormal n := rfl

/-- In particular, the quotient action has the original pointwise formula. -/
theorem quotientConjNormal_mk_apply (D Q : Subgroup N) [D.Normal] [Q.Normal]
    (hQ : Q ≤ centralizer (D : Set N)) (n : N) (d : D) :
    (quotientConjNormal D Q hQ (QuotientGroup.mk' Q n) d : N) =
      n * (d : N) * n⁻¹ := rfl

/-- Pulling the quotient action back along the quotient map recovers conjugation. -/
theorem quotientConjNormal_comp_mk (D Q : Subgroup N) [D.Normal] [Q.Normal]
    (hQ : Q ≤ centralizer (D : Set N)) :
    (quotientConjNormal D Q hQ).comp (QuotientGroup.mk' Q) = conjNormal :=
  MonoidHom.ext (quotientConjNormal_mk D Q hQ)

/-- Triviality on the actual quotient image of K means that K centralizes D. -/
theorem le_centralizer_of_quotientConjNormal_image_eq_one
    (D Q K : Subgroup N) [D.Normal] [Q.Normal]
    (hQ : Q ≤ centralizer (D : Set N))
    (hK : (quotientConjNormal D Q hQ).comp (K.map (QuotientGroup.mk' Q)).subtype = 1) :
    K ≤ centralizer (D : Set N) := by
  rw [← conjNormal_ker_eq_centralizer]
  intro k hk
  change conjNormal k = (1 : MulAut D)
  exact DFunLike.congr_fun hK
    (⟨QuotientGroup.mk' Q k, mem_map_of_mem (QuotientGroup.mk' Q) hk⟩ :
      K.map (QuotientGroup.mk' Q))

end MulAut
