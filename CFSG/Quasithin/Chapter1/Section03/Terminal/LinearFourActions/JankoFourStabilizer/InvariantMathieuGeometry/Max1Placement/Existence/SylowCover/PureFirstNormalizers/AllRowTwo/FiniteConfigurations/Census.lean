module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.FiniteConfigurations.PureCensus
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.FiniteConfigurations.PairRanks
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.FiniteConfigurations.Tables

/-!
# Complete literal census of marked all-row-two subgroups

Purity and the actual two marked points reduce an arbitrary subgroup of the
certified intersection to sixteen eights or fifteen pure sixteens. The five
extra sixteens contain the explicit rank-twenty pairs, contradicting the
no-native-pair hypothesis. Every surviving row satisfies that hypothesis by
its all-pairs certificate. The conclusion is equality of literal native
subgroups, with no supplied enumeration callback or extra marking premise.
Source: Kleidman--Wilson (1988), Corollary 1.2.2(a), Section 2.1, pp.488--489.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.FiniteConfigurations
open MarkedIntersection ElementaryNormalizerCover.PureTwoA.NativePair
attribute [local irreducible] modelGroup matrixA matrixB toMatrix
set_option Elab.async false

private theorem eq_row_of_masks (X : Subgroup Model) (hX : X ≤ markedIntersection)
    (i : Fin 26) (he : carrierMasks X = rowMasks i) : X = row i := by
  apply le_antisymm
  · intro x hx
    obtain ⟨j,rfl⟩ := (mem_markedIntersection_iff _).mp (hX hx)
    apply (nativeWord_mem_row_iff i _).mpr
    rw [← he,mem_carrierMasks]
    exact hx
  · intro x hx
    obtain ⟨m,hm,rfl⟩ := (mem_row_iff i x).mp hx
    apply (mem_carrierMasks X m).mp
    rwa [he]

private theorem not_extra_masks (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hp : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hn : ¬ ∃ g : Model, nativePair.map (MulAut.conj g).toMonoidHom ≤ X)
    (i : Fin 5) : carrierMasks X ≠ extraMasks i := by
  intro he
  obtain ⟨hm,hnm,hm0,hn0,hmn⟩ := PairOrbitData.bad_pair_mem i
  have hmem (m : Fin 8192) (hm : m ∈ extraMasks i) : nativeWord m ∈ X := by
    rw [← mem_carrierMasks,he]
    exact hm
  have hne (m : Fin 8192) (h0 : m ≠ 0) : nativeWord m ≠ 1 :=
    fun hh => h0 (nativeWord_injective (hh.trans nativeWord_zero.symm))
  have hr := pair_rank X hp hn _ _ (hmem _ hm) (hmem _ hnm)
    (hne _ hm0) (hne _ hn0) (fun hh => hmn (nativeWord_injective hh))
  have hb := extra_pairRank i
  omega

/-- The complete literal family: sixteen eights and ten sixteens. -/
theorem marked_census (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hX : X ≤ markedIntersection) (ht : markedT ∈ X) (hP : markedP ∈ X)
    (hc : 4 < Nat.card X) (hp : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hn : ¬ ∃ g : Model, nativePair.map (MulAut.conj g).toMonoidHom ≤ X) :
    ∃ i : Fin 26, X = row i := by
  rcases pure_census X hX ht hP hp hc with ⟨i,hi⟩ | ⟨i,hi⟩
  · exact ⟨eightIndex i,eq_row_of_masks X hX _ hi⟩
  · by_cases h : i.val < 10
    · exact ⟨sixteenIndex ⟨i.val,h⟩,eq_row_of_masks X hX _ (by simpa [pureSixteenMasks,h] using hi)⟩
    · exact (not_extra_masks X hp hn ⟨i.val-10,by omega⟩ (by simpa [pureSixteenMasks,h] using hi)).elim

/-- At order sixteen the complete census has precisely the ten literal rows. -/
theorem marked_sixteen_census (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hX : X ≤ markedIntersection) (ht : markedT ∈ X) (hP : markedP ∈ X)
    (hc : Nat.card X = 16) (hp : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hn : ¬ ∃ g : Model, nativePair.map (MulAut.conj g).toMonoidHom ≤ X) :
    ∃ i : Fin 10, X = row (sixteenIndex i) := by
  obtain ⟨i,rfl⟩ := marked_census X hX ht hP (by omega) hp hn
  have h : ¬ i.val < 16 := by
    intro hh
    rw [row_card,if_pos hh] at hc
    omega
  refine ⟨⟨i.val-16,by omega⟩,congrArg row (Fin.ext ?_)⟩
  change i.val = 16+(i.val-16)
  omega

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.FiniteConfigurations
