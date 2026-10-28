module
public import Theory.SpecificGroups.ClassicalOrthogonal.A02ParabolicSections.BinaryD4
import all Theory.SpecificGroups.ClassicalOrthogonal.A02ParabolicSections.BinaryD4
import all Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.BinaryEightObstruction.Rank
public import Theory.GroupTheory.CentralExtensionPartialInversion
public import Theory.GroupTheory.OddCentralInvolutionLifting.Centralizers

/-!
# The binary D₄ local rank obstruction in odd central covers

Each cubic generator of the existing rank-three subgroup is a product of two
involutory Siegel roots. Odd central lifting preserves these product relations.
One root inverts its own cubic generator and commutes with the other two;
partial inversion therefore makes the three lifted cubic generators commute.
Their exact images retain the original faithful projective marking.

The rank-three subgroup lies in the centralizer of the unique involutory lift
of the old local involution. This proves the obstruction upstairs without any
rank monotonicity assertion for central quotients.

The two private imports intentionally extend the original root-word and local
constructions; their internal matrix formulas are not added to the public API.
All finite calculations concern three 8-by-8 matrices, not the ambient group.
Source: Aschbacher–Smith A.2.18, printed p.40; the inherited Siegel construction
and its ATLAS attribution are retained in `BinaryEightObstruction.Rank`.
-/
public noncomputable section
namespace ClassicalOrthogonal.A02ParabolicSections.BinaryD4
open BinaryEightObstruction Subgroup
local notation "K" => ZMod 2
local notation "E" => OmegaPlus 4 K
local notation "Q" => formD 4 K
local notation "H" => POmegaPlus 4 K

private def firstRoot : Fin 3 → E :=
  ![rootEF 0 1 (by decide), rootEE 0 1, rootEF 2 3 (by decide)]
private def secondRoot : Fin 3 → E :=
  ![rootEF 1 0 (by decide), rootFF 0 1, rootEF 3 2 (by decide)]

private theorem roots_product (i : Fin 3) : firstRoot i * secondRoot i = generators i := by
  fin_cases i <;> rfl

private theorem firstRoot_square (i : Fin 3) : firstRoot i ^ 2 = 1 := by
  apply representation_injective
  rw [map_pow, map_one, pow_two]
  fin_cases i
  · change representation (rootEF 0 1 (by decide)) * representation (rootEF 0 1 (by decide)) = 1
    rw [representation_rootEF]; decide
  · change representation (rootEE 0 1) * representation (rootEE 0 1) = 1
    rw [representation_rootEE]; decide
  · change representation (rootEF 2 3 (by decide)) * representation (rootEF 2 3 (by decide)) = 1
    rw [representation_rootEF]; decide

private theorem secondRoot_square (i : Fin 3) : secondRoot i ^ 2 = 1 := by
  apply representation_injective
  rw [map_pow, map_one, pow_two]
  fin_cases i
  · change representation (rootEF 1 0 (by decide)) * representation (rootEF 1 0 (by decide)) = 1
    rw [representation_rootEF]; decide
  · change representation (rootFF 0 1) * representation (rootFF 0 1) = 1
    rw [representation_rootFF]; decide
  · change representation (rootEF 3 2 (by decide)) * representation (rootEF 3 2 (by decide)) = 1
    rw [representation_rootEF]; decide

private theorem firstRoot_inverts (i : Fin 3) :
    firstRoot i * generators i * (firstRoot i)⁻¹ = (generators i)⁻¹ := by
  rw [← roots_product]
  have h₁ : (firstRoot i)⁻¹ = firstRoot i :=
    inv_eq_of_mul_eq_one_left ((pow_two (firstRoot i)) ▸ firstRoot_square i)
  have h₂ : (secondRoot i)⁻¹ = secondRoot i :=
    inv_eq_of_mul_eq_one_left ((pow_two (secondRoot i)) ▸ secondRoot_square i)
  rw [mul_inv_rev, h₁, h₂, ← mul_assoc, ← pow_two, firstRoot_square, one_mul]

private def firstMatrix : Fin 3 → Matrix (Index 4) (Index 4) K :=
  ![1 + Matrix.single (.inl 0) (.inl 1) 1 + Matrix.single (.inr 1) (.inr 0) 1,
    1 + Matrix.single (.inl 0) (.inr 1) 1 + Matrix.single (.inl 1) (.inr 0) 1,
    1 + Matrix.single (.inl 2) (.inl 3) 1 + Matrix.single (.inr 3) (.inr 2) 1]

private theorem representation_first (i : Fin 3) : representation (firstRoot i) = firstMatrix i := by
  fin_cases i
  · exact representation_rootEF 0 1 (by decide)
  · exact representation_rootEE 0 1
  · exact representation_rootEF 2 3 (by decide)

private theorem firstMatrix_commutes : ∀ i j : Fin 3, i ≠ j →
    firstMatrix i * generatorMatrix j = generatorMatrix j * firstMatrix i := by decide

private theorem firstRoot_commutes (i j : Fin 3) (hij : i ≠ j) :
    Commute (firstRoot i) (generators j) := by
  change firstRoot i * generators j = generators j * firstRoot i
  apply representation_injective
  simp only [map_mul, representation_generators, representation_first]
  exact firstMatrix_commutes i j hij

variable {G : Type*} [Group G]
variable (q : G →* H) (hq : Function.Surjective q)
variable (hk : q.ker ≤ center G) (ho : Odd (Nat.card q.ker))

private def liftedFirst (i : Fin 3) : G := OddCentralLifting.involutionLift q hq ho
  (projectiveElementaryMap Q (firstRoot i)) (by rw [← map_pow, firstRoot_square, map_one])
private def liftedSecond (i : Fin 3) : G := OddCentralLifting.involutionLift q hq ho
  (projectiveElementaryMap Q (secondRoot i)) (by rw [← map_pow, secondRoot_square, map_one])
private def liftedGenerator (i : Fin 3) : G := liftedFirst q hq ho i * liftedSecond q hq ho i

private theorem liftedGenerator_image (i : Fin 3) :
    q (liftedGenerator q hq ho i) = projectiveElementaryMap Q (generators i) := by
  rw [liftedGenerator, map_mul, liftedFirst, liftedSecond,
    OddCentralLifting.involutionLift_image, OddCentralLifting.involutionLift_image,
    ← map_mul, roots_product]

include hk in
private theorem liftedGenerator_cube (i : Fin 3) : liftedGenerator q hq ho i ^ 3 = 1 := by
  apply OddCentralLifting.involution_product_relation q ho hk
    (OddCentralLifting.involutionLift_square q hq ho _ _)
    (OddCentralLifting.involutionLift_square q hq ho _ _)
  rw [← map_mul]
  change q (liftedGenerator q hq ho i) ^ 3 = 1
  rw [liftedGenerator_image, ← map_pow, generators_cube, map_one]

include hk in
private theorem liftedGenerators_commute (i j : Fin 3) :
    Commute (liftedGenerator q hq ho i) (liftedGenerator q hq ho j) := by
  by_cases hij : i = j
  · subst j; exact Commute.refl _
  · apply CentralExtension.commute_lifts_of_partial_inversion q hq hk
      (projectiveElementaryMap Q (generators i)) (projectiveElementaryMap Q (generators j))
      (projectiveElementaryMap Q (firstRoot i)) (by decide : Nat.Coprime 3 2)
      (by rw [← map_pow, generators_cube, map_one])
      ((generators_commute i j).map _) _ ((firstRoot_commutes i j hij).map _)
      _ _ (liftedGenerator_image _ _ _ _) (liftedGenerator_image _ _ _ _)
    simpa only [map_mul, map_inv] using congrArg (projectiveElementaryMap Q) (firstRoot_inverts i)

private def liftedCycle (i : Fin 3) : Multiplicative (ZMod 3) →* G where
  toFun a := liftedGenerator q hq ho i ^ a.toAdd.val
  map_one' := pow_zero _
  map_mul' a b := by
    change liftedGenerator q hq ho i ^ (a.toAdd+b.toAdd).val = _
    rw [ZMod.val_add, ← pow_add]
    exact pow_eq_pow_of_modEq (Nat.mod_mod _ _) (liftedGenerator_cube q hq hk ho i)

private theorem liftedCycles_commute : Pairwise (fun i j => ∀ a b,
    Commute (liftedCycle q hq hk ho i a) (liftedCycle q hq hk ho j b)) := by
  intro i j _ a b
  exact (liftedGenerators_commute q hq hk ho i j).pow_pow a.toAdd.val b.toAdd.val

/-- The literal rank-three root subgroup lifts through every odd central kernel. -/
def liftedEmbedding : (Fin 3 → Multiplicative (ZMod 3)) →* G :=
  MonoidHom.noncommPiCoprod (liftedCycle q hq hk ho) (liftedCycles_commute q hq hk ho)

/-- The lift retains the original marked projective embedding. -/
theorem liftedEmbedding_image (a : Fin 3 → Multiplicative (ZMod 3)) :
    q (liftedEmbedding q hq hk ho a) = projectiveEmbedding a := by
  rw [liftedEmbedding, MonoidHom.noncommPiCoprod_apply]
  have he : (Finset.univ : Finset (Fin 3)) = [0,1,2].toFinset := by decide
  rw [he, Finset.noncommProd_toFinset _ _ _ (by decide)]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  change q (liftedGenerator q hq ho 0 ^ (a 0).toAdd.val *
    (liftedGenerator q hq ho 1 ^ (a 1).toAdd.val *
      liftedGenerator q hq ho 2 ^ (a 2).toAdd.val)) = _
  rw [projectiveEmbedding_apply, embedding_apply]
  simp only [map_mul, map_pow, liftedGenerator_image]

theorem liftedEmbedding_injective : Function.Injective (liftedEmbedding q hq hk ho) := by
  intro a b hab
  apply projectiveEmbedding_injective
  rw [← liftedEmbedding_image q hq hk ho a, ← liftedEmbedding_image q hq hk ho b, hab]

variable [Finite G]
include q hq hk ho in
/-- A nontrivial lifted involution has a centralizer of three-rank at least three. -/
theorem exists_lifted_local_rank_three :
    ∃ z : G, z ≠ 1 ∧ z ^ 2 = 1 ∧ 3 ≤ primeRank 3 (centralizer ({z} : Set G)) := by
  have hz2 : involution ^ 2 = 1 := by simpa only [involution_order] using pow_orderOf_eq_one involution
  obtain ⟨z,hz,hzs⟩ := OddCentralLifting.exists_involution_lift q ho hq involution hz2
  have hzn : z ≠ 1 := by
    intro he
    have hi : involution = 1 := hz.symm.trans (he ▸ map_one q)
    have ht := involution_order
    rw [hi, orderOf_one] at ht
    omega
  let f : (Fin 3 → Multiplicative (ZMod 3)) →* centralizer ({z} : Set G) :=
    (liftedEmbedding q hq hk ho).codRestrict _ (by
      intro a
      apply mem_centralizer_singleton_iff.mpr
      apply OddCentralLifting.centralizes_of_image q ho hk hzs
      rw [liftedEmbedding_image, hz]
      have hc := (localEmbedding a).prop
      rw [localEmbedding_val] at hc
      exact mem_centralizer_singleton_iff.mp hc)
  have hf : Function.Injective f := by
    intro a b he
    exact liftedEmbedding_injective q hq hk ho (congrArg Subtype.val he)
  have hp : ∀ a : Fin 3 → Multiplicative (ZMod 3), a^3=1 := by
    intro a
    funext i
    change Multiplicative.ofAdd (3 • (a i).toAdd) = Multiplicative.ofAdd 0
    exact congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero 3 (a i).toAdd)
  refine ⟨z,hzn,hzs,primeRank_ge_of_elementary_embedding hp ?_ f hf⟩
  simp [Nat.card_eq_fintype_card]

end ClassicalOrthogonal.A02ParabolicSections.BinaryD4
