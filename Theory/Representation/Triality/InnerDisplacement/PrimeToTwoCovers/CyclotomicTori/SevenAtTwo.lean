module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.SmallParameter
public import Theory.SpecificGroups.Triality.BinarySevenPlane


/-!
# The seven-primary kernel exclusion for the smallest triality group

The existing Lang-conjugated order-49 torus has a further actual normalizer
word: the twisting Weyl word itself. On the independent plane vectors
(1,1) and (4,1), it acts by powers 4 and 1. The determinant minus one is
therefore 3, coprime to 7, so the lifted alternating pairing vanishes in
every central extension. The genuine Bruhat count makes this torus Sylow,
and central transfer excludes seven from every perfect central kernel.

This completes the missing seven-local calculation at q = 2 in the
cyclotomic part of GLS3 Theorem 6.1.4. The torus and Lang witness are those
of `Standard.BinarySevenPlane`, attributed there to ATLAS, printed p.89.
No multiplier table or additional group identification is an input.
-/

public section

open QuaternionSevenPlane
open PerfectCentralCovering PerfectCentralCovering.OddSylow
open Triality.Standard Triality.Standard.BinarySevenPlane
open Triality.Standard.ConcreteBruhat.FixedDescent

namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.SevenAtTwo
noncomputable section
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "G" => BinaryCarrier 1 Nat.zero_lt_one
local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

private lemma graphField_twist : graphFieldAutomorphism P twistWord = twistWord := by
  rw [twistWord, graphField_word]
  apply word_eq
  decide +kernel

private def fixedActor : fixedSubgroup P :=
  ⟨langWitness * twistWord * langWitness⁻¹,
    conjugate_mem_fixed _ (by rw [graphField_twist])⟩

def embedding : Multiplicative Plane →* G :=
  (carrierFixedEquiv P rfl).symm.toMonoidHom.comp fixedEmbedding

theorem embedding_injective : Function.Injective embedding :=
  (carrierFixedEquiv P rfl).symm.injective.comp fixedEmbedding_injective

def actor : G := (carrierFixedEquiv P rfl).symm fixedActor

def left : G := embedding (Multiplicative.ofAdd (1,1))
def right : G := embedding (Multiplicative.ofAdd (4,1))

private theorem conjugates (z w : Plane)
    (h : ∀ r, weight (planeCoordinates z) r = weight (planeCoordinates w)
      (permWord [1,0,2,3,1,0,2,3] r)) :
    actor * embedding (Multiplicative.ofAdd z) * actor⁻¹ =
      embedding (Multiplicative.ofAdd w) := by
  have he : twistWord * splitEmbedding (Multiplicative.ofAdd z) * twistWord⁻¹ =
      splitEmbedding (Multiplicative.ofAdd w) :=
    (congrArg (fun g => g * twistWord⁻¹) (word_intertwine _ _ _ h)).trans
      (mul_inv_cancel_right _ _)
  have hf : fixedActor * fixedEmbedding (Multiplicative.ofAdd z) * fixedActor⁻¹ =
      fixedEmbedding (Multiplicative.ofAdd w) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, fixedEmbedding_val]
    change (MulAut.conj langWitness) twistWord *
      (MulAut.conj langWitness) (splitEmbedding (Multiplicative.ofAdd z)) *
      ((MulAut.conj langWitness) twistWord)⁻¹ =
      (MulAut.conj langWitness) (splitEmbedding (Multiplicative.ofAdd w))
    simpa only [map_mul, map_inv] using congrArg (MulAut.conj langWitness) he
  simpa only [actor, embedding, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    map_mul, map_inv] using congrArg (carrierFixedEquiv P rfl).symm hf

theorem conjugate_left : actor * left * actor⁻¹ = left ^ 4 := by
  have h := conjugates (1,1) (4 • ((1,1) : Plane)) (by decide +kernel)
  simpa only [left, ofAdd_nsmul, map_pow] using h

theorem conjugate_right : actor * right * actor⁻¹ = right :=
  conjugates (4,1) (4,1) (by decide +kernel)

private theorem plane_generated : ∀ z : Multiplicative Plane,
    ∃ a b : Fin 7, z = Multiplicative.ofAdd (1,1) ^ a.val *
      Multiplicative.ofAdd (4,1) ^ b.val := by decide +kernel

theorem generates : Subgroup.closure ({left, right} : Set G) = embedding.range := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | h
    · exact ⟨_, rfl⟩
    · rcases Set.mem_singleton_iff.mp h with rfl
      exact ⟨_, rfl⟩
  · rintro g ⟨z, rfl⟩
    obtain ⟨a, b, rfl⟩ := plane_generated z
    rw [map_mul, map_pow, map_pow]
    change left ^ a.val * right ^ b.val ∈ Subgroup.closure ({left, right} : Set G)
    have hl : left ∈ Subgroup.closure ({left, right} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hr : right ∈ Subgroup.closure ({left, right} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hl _) (Subgroup.pow_mem _ hr _)

theorem card_range : Nat.card embedding.range = 7 ^ 2 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective embedding_injective).toEquiv]
  change Nat.card Plane = _
  rw [Nat.card_prod]
  norm_num

private theorem card_carrier : Nat.card G = 2 ^ 12 * 3 ^ 4 * 7 ^ 2 * 13 := by
  rw [ConcreteBruhat.FixedCellCount.card_carrier 1 Nat.zero_lt_one,
    ConcreteBruhat.FixedCellCount.card_borel]
  norm_num [binaryParameters_q]

private theorem not_dvd_index : ¬ 7 ∣ embedding.range.index := by
  intro h
  have h' := Nat.mul_dvd_mul_left (7 ^ 2) h
  have he : 7 ^ 2 * embedding.range.index = 2 ^ 12 * 3 ^ 4 * 7 ^ 2 * 13 :=
    (congrArg (· * embedding.range.index) card_range.symm).trans
      (embedding.range.card_mul_index.trans card_carrier)
  rw [he] at h'
  norm_num at h'

def sylow : Sylow 7 G :=
  (IsPGroup.of_card card_range).toSylow not_dvd_index

def pair : TorusPair (sylow : Subgroup G) where
  left := left
  right := right
  actor := actor
  generates := generates
  commute := (Commute.all _ _).map embedding
  exponent := 7
  leftPower := 4
  rightPower := 1
  positive := by decide
  coprime := by decide
  pow_eq_one := by
    rw [left, ← map_pow]
    exact (congrArg embedding (show Multiplicative.ofAdd ((1,1) : Plane) ^ 7 = 1 by
      decide +kernel)).trans (map_one embedding)
  conjugate_left := conjugate_left
  conjugate_right := by simpa only [pow_one] using conjugate_right

theorem geometry : Geometry 7 G := .torus sylow pair

end
end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.SevenAtTwo
