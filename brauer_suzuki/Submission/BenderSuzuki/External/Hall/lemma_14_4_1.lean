/-
Authors: OpenAI
-/

module

public import Submission.BenderSuzuki.External.Hall.Basic

/-!
# Hall Lemma 14.4.1

Book-order wrapper for the transfer cycle decomposition used throughout Hall
§14.4.  The underlying transfer theorem is already available in Mathlib.
-/

namespace BenderSuzuki
namespace External

open Function MulAction Subgroup

universe u

/-- Hall Lemma 14.4.1: the transfer is the product over the cycles of the
permutation induced by `g` on the left cosets of `H`.  This is the Mathlib
transfer product formula under the Hall lemma name. -/
public theorem hall_lemma_14_4_1_transfer_cycle_decomposition
    {G : Type u} [Group G] {H : Subgroup G} [H.FiniteIndex]
    {A : Type u} [CommGroup A] (φ : H →* A) (g : G)
    [Fintype (Quotient (orbitRel (zpowers g) (G ⧸ H)))] :
    MonoidHom.transfer φ g =
      ∏ q : Quotient (orbitRel (zpowers g) (G ⧸ H)),
        φ ⟨q.out.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * q.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem H g q.out⟩ := by
  simpa using
    (MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot (ϕ := φ) (g := g))

end External
end BenderSuzuki
