module

public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.GroupTheory.PResidual.PrimeToMonotone

/-!
# Images and normal restrictions of prime-to-p residuals

For finite groups, a surjection carries O^{p′} onto O^{p′}. A normal
subgroup containing the ambient residual has that same embedded residual.
Both assertions follow from the prime-to-p index characterization; the
second uses that the residual of a normal subgroup is itself normal.

These transfers retain the actual subgroup embeddings and quotient maps.
They are used for O^{3′}(M ∩ L)* in Aschbacher–Smith, combined manuscript
(1 March 2004), proof of 15.3.28, printed p.1131.
-/

public section
namespace Subgroup
variable {A B : Type*} [Group A] [Group B] [Finite A]
variable (p : ℕ) [Fact p.Prime]

/-- Finite surjections preserve the prime-to-p residual exactly. -/
theorem map_primeToResidual_of_surjective (f : A →* B) (hf : Function.Surjective f) :
    (primeToResidual p A).map f = primeToResidual p B := by
  let : ((primeToResidual p A).map f).Normal :=
    (inferInstance : (primeToResidual p A).Normal).map f hf
  exact le_antisymm (map_primeToResidual_le f hf)
    (primeToResidual_le _ ((primeToResidual_index_coprime p).coprime_dvd_right
      ((primeToResidual p A).index_map_dvd hf)))

/-- The embedded residual of a finite subgroup commutes with every homomorphism. -/
theorem map_embedded_primeToResidual_of_hom (U : Subgroup A) (f : A →* B) :
    ((primeToResidual p U).map U.subtype).map f =
      (primeToResidual p (U.map f)).map (U.map f).subtype := by
  have he : f.comp U.subtype = (U.map f).subtype.comp (f.subgroupMap U) := rfl
  rw [map_map, he, ← map_map,
    map_primeToResidual_of_surjective p _ (f.subgroupMap_surjective U)]

/-- A normal subgroup containing the residual has the same embedded residual. -/
theorem embedded_primeToResidual_eq_of_normal (N : Subgroup A) [N.Normal]
    (hN : primeToResidual p A ≤ N) :
    (primeToResidual p N).map N.subtype = primeToResidual p A := by
  let R := (primeToResidual p N).map N.subtype
  have hn : R.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← N.normalizer_eq_top]
    exact normalizer_le_normalizer_characteristic_image N (primeToResidual p N)
  let := hn
  apply le_antisymm (map_primeToResidual_le_of_hom p N.subtype)
  apply primeToResidual_le R
  change Nat.Coprime p ((primeToResidual p N).map N.subtype).index
  rw [index_map_subtype]
  exact (primeToResidual_index_coprime p).mul_right
    ((primeToResidual_index_coprime p).coprime_dvd_right (index_dvd_of_le hN))

end Subgroup
