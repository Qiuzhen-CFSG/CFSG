module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.FiniteConfigurations.PureMasks
/-!
# Exhaustive marked pure-subgroup census

Pull a subgroup back to its exact finite native mask set. Starting with the
actual marked four-group, closure and purity force each strict extension into
the certified eight and sixteen lists; no pure extension of a sixteen exists.
Thus all larger eligible groups have order eight or sixteen. The no-native-pair
condition will eliminate five extra pure sixteens in the final census.
Source: Kleidman--Wilson (1988), Section 2.1, pp.488--489.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.FiniteConfigurations
open MarkedIntersection
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData LowerBound
attribute [local irreducible] modelGroup matrixA matrixB toMatrix
attribute [local instance 2000] Finset.decidableDforallFinset
attribute [local instance 2000] Finset.decidableExistsAndFinset
set_option Elab.async false
private theorem finite_pure_census (S : Finset (Fin 8192))
    (hp : S ⊆ pureMasks) (hplane : planeMasks ⊆ S)
    (hmul : ∀ m ∈ S, ∀ n ∈ S, maskMul m n ∈ S) (hc : 4 < S.card) :
    (∃ i : Fin 16, S = rowMasks (eightIndex i)) ∨
      ∃ j : Fin 15, S = pureSixteenMasks j := by
  have hn : ¬ S ⊆ planeMasks := by
    intro hh
    have hh := Finset.card_le_card hh
    have h4 : planeMasks.card = 4 := by decide +kernel
    omega
  obtain ⟨m,hm,hn⟩ := Finset.not_subset.mp hn
  obtain ⟨i,hi⟩ := extend_plane m (hp hm) hn
  have hiS : rowMasks (eightIndex i) ⊆ S := by
    rw [hi]
    apply Finset.union_subset hplane
    intro n hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    exact hmul m hm p (hplane hp)
  by_cases hS : S ⊆ rowMasks (eightIndex i)
  · exact Or.inl ⟨i,Finset.Subset.antisymm hS hiS⟩
  obtain ⟨n,hn,hni⟩ := Finset.not_subset.mp hS
  obtain ⟨j,hj⟩ := extend_eight i n (hp hn) hni
    (fun p hh => hp (hmul n hn p (hiS hh)))
  have hjS : pureSixteenMasks j ⊆ S := by
    rw [hj]
    apply Finset.union_subset hiS
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact hmul n hn q (hiS hq)
  exact Or.inr ⟨j,Finset.Subset.antisymm
    (fun p hpS => no_extend_sixteen j p (hp hpS)
      (fun q hq => hp (hmul p hpS q (hjS hq)))) hjS⟩

@[expose] def carrierMasks (X : Subgroup Model) : Finset (Fin 8192) :=
  by classical exact Finset.univ.filter fun m => nativeWord m ∈ X

@[simp] theorem mem_carrierMasks (X : Subgroup Model) (m : Fin 8192) :
    m ∈ carrierMasks X ↔ nativeWord m ∈ X := by simp [carrierMasks]

theorem carrierMasks_card (X : Subgroup Model) (hX : X ≤ markedIntersection) :
    (carrierMasks X).card = Nat.card X := by
  let f : {m // m ∈ carrierMasks X} → X :=
    fun m => ⟨nativeWord m.val,(mem_carrierMasks X m.val).mp m.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro m n hh
      exact Subtype.ext (nativeWord_injective (congrArg (fun z : X => (z : Model)) hh))
    · intro x
      obtain ⟨i,hi⟩ := (mem_markedIntersection_iff _).mp (hX x.property)
      exact ⟨⟨coordinate i,(mem_carrierMasks X _).mpr (by change (kernelProduct (coordinate i) : Model) ∈ X; rw [hi]; exact x.property)⟩,Subtype.ext hi⟩
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using
    Nat.card_congr (Equiv.ofBijective f hf)

theorem nativeWord_one : nativeWord 1 = markedT := by
  have hh : kernelProduct 1 = kernelFactor 0 := by
    change kernelFactor 0 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * 1)))))))))))) = _
    simp only [mul_one]
  change (kernelProduct 1 : Model) = OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.t
  rw [hh]
  exact coe_sourceSeed_sq

theorem pure_census (X : Subgroup Model) (hX : X ≤ markedIntersection)
    (ht : markedT ∈ X) (hP : markedP ∈ X)
    (hp : ∀ x ∈ X, x ≠ 1 → IsConj a x) (hc : 4 < Nat.card X) :
    (∃ i : Fin 16, carrierMasks X = rowMasks (eightIndex i)) ∨
      ∃ j : Fin 15, carrierMasks X = pureSixteenMasks j := by
  apply finite_pure_census
  · intro m hm
    have hm := (mem_carrierMasks X m).mp hm
    apply marked_pure_mask m (hX hm)
    by_cases he : nativeWord m = 1
    · exact Or.inl he
    · exact Or.inr (hp _ hm he)
  · intro m hm
    have hs : ∀ m ∈ planeMasks, m = 0 ∨ m = 1 ∨ m = maskMul 1 6607 ∨ m = 6607 := by
      decide +kernel
    rw [mem_carrierMasks]
    rcases hs m hm with rfl | rfl | rfl | rfl
    · rw [nativeWord_zero]; exact X.one_mem
    · rw [nativeWord_one]; exact ht
    · rw [nativeWord_mul,nativeWord_one]; exact X.mul_mem ht hP
    · exact hP
  · intro m hm n hn
    rw [mem_carrierMasks,nativeWord_mul]
    exact X.mul_mem ((mem_carrierMasks X m).mp hm) ((mem_carrierMasks X n).mp hn)
  · rwa [carrierMasks_card X hX]

theorem pure_card_eight_or_sixteen (X : Subgroup Model) (hX : X ≤ markedIntersection)
    (ht : markedT ∈ X) (hP : markedP ∈ X)
    (hp : ∀ x ∈ X, x ≠ 1 → IsConj a x) (hc : 4 < Nat.card X) :
    Nat.card X = 8 ∨ Nat.card X = 16 := by
  rw [← carrierMasks_card X hX]
  rcases pure_census X hX ht hP hp hc with ⟨i,hi⟩ | ⟨i,hi⟩
  · rw [hi]
    exact Or.inl ((by decide +kernel : ∀ i : Fin 16, (rowMasks (eightIndex i)).card = 8) i)
  · rw [hi]
    exact Or.inr ((by decide +kernel : ∀ i : Fin 15, (pureSixteenMasks i).card = 16) i)

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.FiniteConfigurations
