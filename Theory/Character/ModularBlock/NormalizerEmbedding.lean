module

public import Theory.Character.ModularBlock.NormalizerAction

/-!
# Embedding the centralizer algebra in the normalizer algebra

The inclusion of the centralizer into the normalizer induces an injective
ring homomorphism preserving augmentation and intertwining conjugation.
A normalizer-fixed element embeds centrally. Consequently a nonzero central
factor of an embedded orbit sum meets the embedded base member nontrivially:
if it missed one member, conjugation would make it miss every member.

The embedding definitions are exposed because downstream orbit constructions
need the canonical subgroup inclusion and its coefficient-level reduction.

Ported from the corresponding embedding and principal-action parts of
`c3503435:glauberman_zStar/Submission/ZStar/NormalizerBrauerAction.lean`.
The original public names and hypotheses are retained.
-/

public section
noncomputable section
namespace ModularBlock.NormalizerBrauerAction
open Subgroup
universe u v
attribute [local instance] Fintype.ofFinite

/-- The canonical inclusion `C_G(Q) ↪ N_G(Q)`. -/
@[expose] noncomputable def centralizerToNormalizer
    {G : Type u} [Group G] (Q : Subgroup G) :
    Subgroup.centralizer (Q : Set G) →*
      Subgroup.normalizer (Q : Set G) := by
  let C := Subgroup.centralizer (Q : Set G)
  let N := Subgroup.normalizer (Q : Set G)
  let hCN : C ≤ N := Subgroup.centralizer_le_normalizer (Q : Set G)
  exact
    { toFun := fun c => ⟨(c : G), hCN c.property⟩
      map_one' := rfl
      map_mul' := by intro a b; rfl }

@[simp] theorem centralizerToNormalizer_coe
    {G : Type u} [Group G] (Q : Subgroup G)
    (c : Subgroup.centralizer (Q : Set G)) :
    ((centralizerToNormalizer Q c : Subgroup.normalizer (Q : Set G)) : G) =
      (c : G) := rfl

/-- The induced embedding of the centralizer group algebra into the
normalizer group algebra. -/
@[expose] noncomputable def normalizerAlgebraEmbedding
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G) :
    MonoidAlgebra R (Subgroup.centralizer (Q : Set G)) →+*
      MonoidAlgebra R (Subgroup.normalizer (Q : Set G)) :=
  MonoidAlgebra.mapDomainRingHom R (centralizerToNormalizer Q)

@[simp] theorem normalizerAlgebraEmbedding_single
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G) (c : Subgroup.centralizer (Q : Set G)) (r : R) :
    normalizerAlgebraEmbedding R Q (MonoidAlgebra.single c r) =
      MonoidAlgebra.single (centralizerToNormalizer Q c) r := by
  simp [normalizerAlgebraEmbedding]

theorem normalizerAlgebraEmbedding_injective
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G) :
    Function.Injective (normalizerAlgebraEmbedding R Q) := by
  apply MonoidAlgebra.mapDomain_injective
  intro c e hce
  apply Subtype.ext
  exact congrArg
    (fun x : Subgroup.normalizer (Q : Set G) => (x : G)) hce

/-- Conjugation by a normalizer element commutes with the subgroup-algebra
embedding. -/
theorem normalizerAlgebraEmbedding_conjugation
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G) (n : Subgroup.normalizer (Q : Set G))
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G))) :
    MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n *
          normalizerAlgebraEmbedding R Q a *
          MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n⁻¹ =
      normalizerAlgebraEmbedding R Q
        (normalizerConjugate R Q n a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
      rw [map_add, map_add, mul_add, add_mul, ha, hb, map_add]
  | single c r =>
      rw [normalizerAlgebraEmbedding_single]
      rw [show normalizerConjugate R Q n (MonoidAlgebra.single c r) =
          MonoidAlgebra.single (centralizerConjEquiv Q n c) r by
        simp [normalizerConjugate]]
      rw [normalizerAlgebraEmbedding_single]
      change MonoidAlgebra.single n 1 *
          MonoidAlgebra.single (centralizerToNormalizer Q c) r *
          MonoidAlgebra.single n⁻¹ 1 =
        MonoidAlgebra.single
          (centralizerToNormalizer Q (centralizerConjEquiv Q n c)) r
      rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single]
      simp only [one_mul, mul_one]
      congr 1

/-- An element fixed by all normalizer conjugations embeds as a central
element of the normalizer group algebra. -/
theorem normalizerAlgebraEmbedding_mem_center_of_fixed
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G)
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))
    (hfixed : ∀ n : Subgroup.normalizer (Q : Set G),
      normalizerConjugate R Q n a = a) :
    normalizerAlgebraEmbedding R Q a ∈
      Set.center
        (MonoidAlgebra R (Subgroup.normalizer (Q : Set G))) := by
  rw [Semigroup.mem_center_iff]
  intro x
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | single n r =>
      have hconj := normalizerAlgebraEmbedding_conjugation Q n a
      rw [hfixed n] at hconj
      have hunit :
          MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n *
              normalizerAlgebraEmbedding R Q a =
            normalizerAlgebraEmbedding R Q a *
              MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n := by
        calc
          MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n *
                normalizerAlgebraEmbedding R Q a =
              (MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n *
                  normalizerAlgebraEmbedding R Q a *
                  MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n⁻¹) *
                MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n := by
              symm
              calc
                (MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n *
                      normalizerAlgebraEmbedding R Q a *
                      MonoidAlgebra.of R
                        (Subgroup.normalizer (Q : Set G)) n⁻¹) *
                    MonoidAlgebra.of R
                      (Subgroup.normalizer (Q : Set G)) n =
                    (MonoidAlgebra.of R
                        (Subgroup.normalizer (Q : Set G)) n *
                      normalizerAlgebraEmbedding R Q a) *
                      (MonoidAlgebra.of R
                          (Subgroup.normalizer (Q : Set G)) n⁻¹ *
                        MonoidAlgebra.of R
                          (Subgroup.normalizer (Q : Set G)) n) := by
                    rw [mul_assoc]
                _ = MonoidAlgebra.of R
                      (Subgroup.normalizer (Q : Set G)) n *
                    normalizerAlgebraEmbedding R Q a := by
                  rw [← map_mul, inv_mul_cancel n, map_one, mul_one]
          _ = normalizerAlgebraEmbedding R Q a *
                MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n := by
              rw [hconj]
      have hsingle :
          (MonoidAlgebra.single n r :
              MonoidAlgebra R (Subgroup.normalizer (Q : Set G))) =
            r • MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n := by
        simp
      rw [hsingle, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
      exact congrArg (fun z :
        MonoidAlgebra R (Subgroup.normalizer (Q : Set G)) => r • z) hunit

theorem augmentation_normalizerAlgebraEmbedding
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (Q : Subgroup G)
    (a : MonoidAlgebra R (Subgroup.centralizer (Q : Set G))) :
    groupAlgebraAugmentation R
        (Subgroup.normalizer (Q : Set G))
        (normalizerAlgebraEmbedding R Q a) =
      groupAlgebraAugmentation R
        (Subgroup.centralizer (Q : Set G)) a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | single c r => simp [normalizerAlgebraEmbedding]

/-- Every nonzero central factor of the embedded orbit sum has nonzero
intersection with the embedded base orbit member. -/
theorem mul_baseEmbedding_ne_zero_of_factor_embeddedOrbitSum
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (Q : Subgroup G)
    (b : MonoidAlgebra R (Subgroup.centralizer (Q : Set G)))
    (a : MonoidAlgebra R (Subgroup.normalizer (Q : Set G)))
    (haCenter : a ∈ Set.center
      (MonoidAlgebra R (Subgroup.normalizer (Q : Set G))))
    (haNe : a ≠ 0)
    (haFactor : a *
        normalizerAlgebraEmbedding R Q (normalizerOrbitSum R Q b) = a) :
    a * normalizerAlgebraEmbedding R Q b ≠ 0 := by
  classical
  intro hbase
  let E := normalizerAlgebraEmbedding R Q
  let s := normalizerOrbit R Q b
  let Bc := normalizerOrbitSum R Q b
  have hterm : ∀ c ∈ s, a * E c = 0 := by
    intro c hc
    rcases (mem_normalizerOrbit_iff (R := R) Q b c).mp hc with ⟨n, rfl⟩
    let un := MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n
    let uinv := MonoidAlgebra.of R (Subgroup.normalizer (Q : Set G)) n⁻¹
    have hconj := normalizerAlgebraEmbedding_conjugation Q n b
    change un * E b * uinv = E (normalizerConjugate R Q n b) at hconj
    rw [← hconj]
    have hcomm : un * a = a * un :=
      Semigroup.mem_center_iff.mp haCenter un
    calc
      a * (un * E b * uinv) = (a * un) * E b * uinv := by
        simp only [mul_assoc]
      _ = (un * a) * E b * uinv := by rw [hcomm]
      _ = un * (a * E b) * uinv := by simp only [mul_assoc]
      _ = 0 := by
        change un * (a * normalizerAlgebraEmbedding R Q b) * uinv = 0
        rw [hbase, mul_zero, zero_mul]
  have hzero : a * E Bc = 0 := by
    change a * E (∑ c ∈ s, c) = 0
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro c hc
    exact hterm c hc
  apply haNe
  calc
    a = a * E Bc := by simpa [E, Bc] using haFactor.symm
    _ = 0 := hzero

end ModularBlock.NormalizerBrauerAction
