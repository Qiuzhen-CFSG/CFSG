module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.MatrixConditions

/-!
# Coprime powers in the max2 matrix quotient

A nonidentity element killed by a number coprime to 6912 cannot occur in a
subgroup of order 6912. This arithmetic bridge is shared by the adapters for
the existing prime-order certificates, used in Proposition 1.3.4, printed
p.511/PDF p.528 of Aschbacher--Smith.
-/

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2.PairIncidenceCertificates

/-- The small prime-order witnesses also obstruct the 6912th-power identity. -/
public theorem power6912_ne_one
    (g : MatrixGroup)
    (p : ℕ) (hp : p.Coprime 6912) (hpow : g ^ p = 1) (hne : g ≠ 1) :
    g ^ 6912 ≠ 1 := by
  intro h
  apply hne
  apply orderOf_eq_one_iff.mp
  apply Nat.dvd_one.mp
  have hd := Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr hpow)
    (orderOf_dvd_iff_pow_eq_one.mpr h)
  simpa only [hp.gcd_eq_one] using hd

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2.PairIncidenceCertificates
