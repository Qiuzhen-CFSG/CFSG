module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1.CentralizerSection.TwoKernel.Certificates
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.TypeTags.Finite

/-!
# A concrete rank-three obstruction in Co₁'s involution centralizer

Three certified words in the literal 24-dimensional numerator commute, have
cube one, and give 27 distinct products. They therefore embed C₃³ in that
numerator. This is the elementary-embedding alternative to proving that the
whole eight-dimensional action kernel is a two-group. No kernel structure,
centrality, splitting, group order or table recognition is assumed.

The multiplication program is checked in `TwoKernel.Certificates`; the small
relation and independence certificates below use packed binary matrices.
The actual numerator centralizes the previously certified involution z, so
this supplies the odd-rank obstruction used by the Co₁ source application.

Source: Aschbacher--Smith A.2.19 and I.1.3, printed pp.40--41 and 407;
GLS3 Table 5.3l, using the fixed ATLAS `Co1G1-f2r24B0` carrier and the
`Co1G1-max5W1` words. See `TwoKernel/source/README.md`.
-/

public noncomputable section
namespace Sporadic.LeechRelated.Co1.CentralizerSection.ElementaryThree
open Packed

private def representation : numerator →* Matrix (Fin 24) (Fin 24) (ZMod 2) where
  toFun g := g.val.val.val
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem representation_injective : Function.Injective representation := by
  intro a b h
  exact Subtype.ext (Subtype.ext (Units.ext h))

private def generators (i : Fin 3) : numerator := (exists_generators i).choose

private theorem representation_generators (i : Fin 3) :
    representation (generators i) = decode (generatorRows i) :=
  (exists_generators i).choose_spec

private def squareRows : Fin 3 → Rows :=
  ![![12380491, 10909533, 12605121, 7958348, 10729035, 15965055, 7930456, 10740119, 13802516, 275320, 10907517, 14351040, 10730105, 10647528, 16764573, 1438933, 15315893, 9254175, 10745437, 12866248, 5281080, 15727238, 10004255, 11564059],
    ![8448175, 3183274, 9586163, 9655685, 7336629, 1661547, 4450016, 1457629, 3098138, 10885571, 634999, 449377, 5754395, 12888982, 5621605, 15885945, 7714579, 6026735, 10931524, 404468, 13586395, 5738153, 13454630, 12805979],
    ![4130805, 4169468, 10175539, 14978108, 13975401, 14619651, 5105145, 6854967, 2559919, 4708226, 9495866, 43036, 13468750, 10210904, 14883727, 3223870, 15050756, 7998746, 16175510, 12745491, 10031620, 7746334, 9844009, 2540776]]

private theorem square_certificate : ∀ i : Fin 3,
    product (generatorRows i) (generatorRows i) = squareRows i := by decide +kernel

private theorem cube_certificate : ∀ i : Fin 3,
    product (squareRows i) (generatorRows i) = Matrices.identityRows 24 := by decide +kernel

private theorem commute_certificate : ∀ i j : Fin 3,
    product (generatorRows i) (generatorRows j) =
      product (generatorRows j) (generatorRows i) := by decide +kernel

private theorem generators_cube (i : Fin 3) : generators i ^ 3 = 1 := by
  apply representation_injective
  rw [map_pow, map_one, representation_generators, pow_succ, pow_two]
  rw [mul_eq_of_certificate _ _ _ (square_certificate i)]
  rw [mul_eq_of_certificate _ _ _ (cube_certificate i), Matrices.decode_identity]

private theorem generators_commute (i j : Fin 3) : Commute (generators i) (generators j) := by
  apply representation_injective
  simp only [map_mul, representation_generators, ← decode_product]
  exact congrArg decode (commute_certificate i j)

private def cycle (i : Fin 3) : Multiplicative (ZMod 3) →* numerator where
  toFun a := generators i ^ a.toAdd.val
  map_one' := pow_zero _
  map_mul' a b := by
    change generators i ^ (a.toAdd + b.toAdd).val = _
    rw [ZMod.val_add, ← pow_add]
    exact pow_eq_pow_of_modEq (Nat.mod_mod _ _) (generators_cube i)

private theorem cycles_commute : Pairwise (fun (i j : Fin 3) =>
    ∀ (a b : Multiplicative (ZMod 3)), Commute (cycle i a) (cycle j b)) := by
  intro i j _ a b
  change Commute (generators i ^ a.toAdd.val) (generators j ^ b.toAdd.val)
  exact @Commute.pow_pow numerator (inferInstance : Monoid numerator)
    (generators i) (generators j) (generators_commute i j) a.toAdd.val b.toAdd.val

/-- An actual elementary abelian subgroup of the fixed centralizing numerator. -/
def embedding : (Fin 3 → Multiplicative (ZMod 3)) →* numerator :=
  MonoidHom.noncommPiCoprod cycle cycles_commute

private theorem embedding_apply (a : Fin 3 → Multiplicative (ZMod 3)) :
    embedding a = generators 0 ^ (a 0).toAdd.val *
      (generators 1 ^ (a 1).toAdd.val * generators 2 ^ (a 2).toAdd.val) := by
  rw [embedding, MonoidHom.noncommPiCoprod_apply]
  have h : (Finset.univ : Finset (Fin 3)) = [0, 1, 2].toFinset := by decide
  rw [h, Finset.noncommProd_toFinset _ _ _ (by decide)]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rfl

private def powerRows (i : Fin 3) (a : ZMod 3) : Rows :=
  if a = 0 then Matrices.identityRows 24 else if a = 1 then generatorRows i else squareRows i

private theorem representation_cycle (i : Fin 3) (a : Multiplicative (ZMod 3)) :
    representation (cycle i a) = decode (powerRows i a.toAdd) := by
  change representation (generators i ^ a.toAdd.val) = _
  rw [map_pow, representation_generators]
  generalize a.toAdd = ha
  fin_cases ha
  · exact (Matrices.decode_identity 24).symm
  · exact pow_one _
  · change (decode (generatorRows i) : Matrix (Fin 24) (Fin 24) (ZMod 2)) ^ 2 = _
    rw [pow_two]
    exact mul_eq_of_certificate _ _ _ (square_certificate i)

private def wordRows (a b c : ZMod 3) : Rows :=
  product (powerRows 0 a) (product (powerRows 1 b) (powerRows 2 c))

-- The first row already separates the identity from the other 26 products.
private theorem wordRows_kernel : ∀ a b c : ZMod 3,
    (∀ j : Fin 24, (decode (wordRows a b c) : Matrix (Fin 24) (Fin 24) (ZMod 2)) 0 j =
      (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) 0 j) → a = 0 ∧ b = 0 ∧ c = 0 := by
  decide +kernel

private theorem representation_embedding (a : Fin 3 → Multiplicative (ZMod 3)) :
    representation (embedding a) = decode (wordRows (a 0).toAdd (a 1).toAdd (a 2).toAdd) := by
  rw [embedding_apply]
  change representation (cycle 0 (a 0) * (cycle 1 (a 1) * cycle 2 (a 2))) = _
  simp only [map_mul, representation_cycle, wordRows, decode_product]

/-- Independence is checked in the faithful 24-dimensional representation. -/
theorem embedding_injective : Function.Injective embedding := by
  apply (injective_iff_map_eq_one embedding).mpr
  intro a ha
  have h := congrArg representation ha
  rw [representation_embedding, map_one] at h
  obtain ⟨h0, h1, h2⟩ := wordRows_kernel _ _ _ (fun j => congrArg (fun m => m 0 j) h)
  funext i
  apply Multiplicative.toAdd.injective
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- The exact numerator of the eight-space action has 3-rank at least three. -/
theorem numerator_primeRank_three_ge : 3 ≤ primeRank 3 numerator := by
  apply primeRank_ge_of_elementary_embedding (f := embedding) (hf := embedding_injective)
  · intro a
    funext i
    change Multiplicative.ofAdd (3 • (a i).toAdd) = Multiplicative.ofAdd 0
    exact congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero 3 (a i).toAdd)
  · simp [Nat.card_eq_fintype_card]

end Sporadic.LeechRelated.Co1.CentralizerSection.ElementaryThree
