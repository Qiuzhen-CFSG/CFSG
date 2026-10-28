module

public import Theory.SpecificGroups.ReeG2.InvolutionProjectiveProduct
public import CFSG.Quasithin.Defs

/-!
# The Ree product-subgroup step in A.2.17

The concrete seven-dimensional Ree model contains the product of its torus
involution with PSL₂ over the defining field. Applying the projective-product
rank theorem gives local 3-rank at least 2m+1, contradicting quasithinness
when m ≥ 1. The proof transports through any injective homomorphism of the
actual model; it makes no assertion about the separate derived group at m=0.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), proof of Lemma A.2.17, printed p.38.
-/

public section

namespace CFSG.Quasithin.ChapterA.Section02.ReeProduct
variable {F G : Type*} [Field F] [Finite F] [CharP F 3] [Group G] [Finite G]

/-- The literal C₂ × PSL₂ subgroup supplies the Ree exclusion in the source proof. -/
theorem not_quasithin_of_embedding (m : ℕ) (hm : 1 ≤ m)
    (hcard : Nat.card F = 3^(2*m+1))
    (f : Atlas.ReeG2.Model F m →* G) (hf : Function.Injective f) : ¬ IsQuasithin G := by
  intro hqt
  obtain ⟨z, hz, hz2, hr⟩ :=
    Atlas.ReeG2.InvolutionProduct.exists_involution_primeRank_ge m hcard f hf
  have ho : orderOf z = 2 := orderOf_eq_prime hz2 hz
  have hloc := Theory.GroupTheory.isTwoLocal_involution_centralizer ho
  have hu := (Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hqt) _ hloc 3
    (by decide) (by decide)
  omega

/-- The large small-Ree models are not quasithin, by their actual product subgroup. -/
theorem not_quasithin (m : ℕ) (hm : 1 ≤ m)
    (hcard : Nat.card F = 3^(2*m+1)) : ¬ IsQuasithin (Atlas.ReeG2.Model F m) :=
  not_quasithin_of_embedding m hm hcard (MonoidHom.id _) Function.injective_id

end CFSG.Quasithin.ChapterA.Section02.ReeProduct
