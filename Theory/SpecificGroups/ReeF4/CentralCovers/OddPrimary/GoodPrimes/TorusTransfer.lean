module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.ProductTori

/-!
# Full torus embeddings and the good-prime Ree configurations

An injective map of a finite cyclic product into the literal Ree model
restricts to an injective map of the two Sylow factors. The index of the
restricted image is the product of the two factor indices and the original
image index. Consequently a prime-to-p image index and the actual ambient
pair action supply `AbelianSylowData`. A single cyclic torus instead supplies
cyclicity of every Sylow subgroup by Sylow conjugacy.

The marked torus types below contain actual homomorphisms into `Model m`,
injectivity proofs, and (for a product) the pair action. The types have no
existence instances. Their cofactor applications connect them to the existing
covering calculation without assuming a Sylow or multiplier conclusion.

Sources: the local route to Aschbacher–Smith I.1.1–4, printed pp.407–408;
GLS3 §4.10 and the subsystem conventions of Example 2.6.3. Concrete torus
construction remains separate from these Sylow deductions.
-/

public section

namespace ReeF4.CentralCovers.OddPrimary
open Subgroup

/-- Restrict a full cyclic product torus to its two Sylow factors. -/
theorem goodPrimeGeometry_of_cyclic_product {m p : ℕ} [Fact p.Prime]
    {C : Type*} [Group C] [Finite C] [IsCyclic C]
    (j : C × C →* Model m) (hj : Function.Injective j)
    (hi : ¬ p ∣ j.range.index)
    (hrev : ∀ z : C, ReversesPair (j (z, 1)) (j (1, z))) :
    GoodPrimeGeometry m p := by
  classical
  let P : Sylow p C := Classical.choice inferInstance
  let s : P →* C := (P : Subgroup C).subtype
  let k : P × P →* Model m := j.comp (s.prodMap s)
  have hk : ¬ p ∣ k.range.index := by
    change ¬ p ∣ (j.comp ((P : Subgroup C).subtype.prodMap
      (P : Subgroup C).subtype)).range.index
    rw [MonoidHom.range_comp, MonoidHom.range_prodMap, range_subtype,
      index_map_of_injective _ hj, index_prod]
    exact (Fact.out : p.Prime).not_dvd_mul
      ((Fact.out : p.Prime).not_dvd_mul P.not_dvd_index P.not_dvd_index) hi
  exact Or.inr (exists_abelianSylowData_of_product P.isPGroup' k hk
    (fun z => by simpa [k, s] using hrev (z : C)))

/-- One cyclic torus of prime-to-p index controls every Sylow p-subgroup. -/
theorem goodPrimeGeometry_of_cyclic_torus {m p : ℕ} [Fact p.Prime]
    {C : Type*} [Group C] [Finite C] [IsCyclic C]
    (j : C →* Model m) (hj : Function.Injective j)
    (hi : ¬ p ∣ j.range.index) : GoodPrimeGeometry m p := by
  classical
  let P : Sylow p C := Classical.choice inferInstance
  have hindex : ¬ p ∣ ((P : Subgroup C).map j).index := by
    rw [index_map_of_injective _ hj]
    exact (Fact.out : p.Prime).not_dvd_mul P.not_dvd_index hi
  let R : Sylow p (Model m) := (P.isPGroup'.map j).toSylow hindex
  have : IsCyclic R := isCyclic_of_surjective
    (j.subgroupMap (P : Subgroup C)) (j.subgroupMap_surjective _)
  exact Or.inl (fun Q => isCyclic_of_surjective (R.equiv Q) (R.equiv Q).surjective)

/-- A specified cofactor of an embedded finite group's order is its image index. -/
theorem torus_image_index {m n c : ℕ} {C : Type*} [Group C] [Finite C]
    (j : C →* Model m) (hj : Function.Injective j) (hC : Nat.card C = n)
    (horder : Nat.card (Model m) = n * c) : j.range.index = c := by
  have hcard : Nat.card j.range = n := (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm.trans hC
  have hn : 0 < n := hC ▸ Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hn
  rw [← hcard, j.range.card_mul_index, horder, hcard]

/-- A marked cyclic torus in the literal exceptional fixed subgroup. -/
structure CyclicTorusEmbedding (m n : ℕ) where
  map : Multiplicative (ZMod n) →* Model m
  injective : Function.Injective map

/-- A marked product torus, including the actual ambient pair action. -/
structure ProductTorusEmbedding (m n : ℕ) where
  map : Multiplicative (ZMod n) × Multiplicative (ZMod n) →* Model m
  injective : Function.Injective map
  reverses : ∀ z, ReversesPair (map (z, 1)) (map (1, z))

/-- A cyclic torus supplies the cyclic Sylow alternative from its cofactor. -/
theorem CyclicTorusEmbedding.goodPrimeGeometry {m n c p : ℕ} [Fact p.Prime]
    (T : CyclicTorusEmbedding m n) (hn : 0 < n)
    (horder : Nat.card (Model m) = n * c) (hc : ¬ p ∣ c) :
    GoodPrimeGeometry m p := by
  have : NeZero n := ⟨hn.ne'⟩
  apply goodPrimeGeometry_of_cyclic_torus T.map T.injective
  rw [torus_image_index T.map T.injective (by
    change Nat.card (ZMod n) = n
    exact Nat.card_zmod n) horder]
  exact hc

/-- A full product torus supplies the two marked Sylow generators and action. -/
theorem ProductTorusEmbedding.goodPrimeGeometry {m n c p : ℕ} [Fact p.Prime]
    (T : ProductTorusEmbedding m n) (hn : 0 < n)
    (horder : Nat.card (Model m) = n ^ 2 * c) (hc : ¬ p ∣ c) :
    GoodPrimeGeometry m p := by
  have : NeZero n := ⟨hn.ne'⟩
  apply goodPrimeGeometry_of_cyclic_product T.map T.injective _ T.reverses
  rw [torus_image_index T.map T.injective (by
    rw [Nat.card_prod]
    change Nat.card (ZMod n) * Nat.card (ZMod n) = n ^ 2
    rw [Nat.card_zmod, pow_two]) horder]
  exact hc

end ReeF4.CentralCovers.OddPrimary
