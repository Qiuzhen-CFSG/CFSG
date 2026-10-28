module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.FiniteConfigurations.OvergroupTables
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.FiniteConfigurations.HullCertificates
/-!
# Literal canonical hulls and their exact orders

The finite hull lists are subgroups in the same marked elementary intersection.
They contain the eight and every listed sixteen, and every listed hull element
is a product of elements of the two sixteen overgroups (or belongs to the line
eight). The unrestricted overgroup table therefore identifies these literal
subgroups with the canonical hull. The line hull has order eight; every other
eight has a hull of order thirty-two. Sixteen rows are their own hulls.
Source: Kleidman--Wilson (1988), Section 2.1, pp.488--489.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.FiniteConfigurations
open MarkedIntersection HullCertificates
attribute [local irreducible] modelGroup matrixA matrixB toMatrix
attribute [local instance 2000] Finset.decidableDforallFinset
attribute [local instance 2000] Finset.decidableExistsAndFinset
set_option Elab.async false

private theorem hull_word_mem (i : Fin 16) (m : Fin 8192) (hm : m ∈ hullMasks i) :
    nativeWord m ∈ markedIntersection := by
  obtain ⟨j,hj⟩ := hull_coordinates i m hm
  exact (mem_markedIntersection_iff _).mpr ⟨j,congrArg nativeWord hj⟩

theorem listedHull_le_markedIntersection (i : Fin 16) : listedHull i ≤ markedIntersection := by
  apply (closure_le _).mpr
  rintro _ ⟨m,hm,rfl⟩
  exact hull_word_mem i m hm

theorem mem_listedHull_iff (i : Fin 16) (x : Model) : x ∈ listedHull i ↔
    ∃ m ∈ hullMasks i, nativeWord m = x := by
  let S : Subgroup Model := {
    carrier := nativeWord '' (hullMasks i : Set (Fin 8192))
    one_mem' := ⟨0,hull_zero i,nativeWord_zero⟩
    mul_mem' := by
      rintro _ _ ⟨m,hm,rfl⟩ ⟨n,hn,rfl⟩
      exact ⟨maskMul m n,hull_mul i m hm n hn,nativeWord_mul m n⟩
    inv_mem' := by
      rintro _ ⟨m,hm,rfl⟩
      refine ⟨m,hm,?_⟩
      let := markedIntersection_elementary
      have hs := elemPow_eq_one_of_isElementaryAbelian (p := 2) (nativeWord m)
        (hull_word_mem i m hm)
      exact (inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs)).symm
  }
  have he : listedHull i = S := closure_eq S
  rw [he]
  rfl

theorem nativeWord_mem_listedHull_iff (i : Fin 16) (m : Fin 8192) :
    nativeWord m ∈ listedHull i ↔ m ∈ hullMasks i := by
  rw [mem_listedHull_iff]
  constructor
  · rintro ⟨n,hn,he⟩
    exact nativeWord_injective he ▸ hn
  · exact fun hm => ⟨m,hm,rfl⟩

theorem listedHull_card (i : Fin 16) : Nat.card (listedHull i) = if i = 5 then 8 else 32 := by
  let f : {m // m ∈ hullMasks i} → listedHull i :=
    fun m => ⟨nativeWord m.val,(nativeWord_mem_listedHull_iff i m.val).mpr m.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro m n h
      apply Subtype.ext
      exact nativeWord_injective (congrArg (fun x : listedHull i => (x : Model)) h)
    · intro x
      obtain ⟨m,hm,hx⟩ := (mem_listedHull_iff i x.val).mp x.property
      exact ⟨⟨m,hm⟩,Subtype.ext hx⟩
  have hc : ∀ i, (hullMasks i).card = if i = 5 then 8 else 32 := by decide +kernel
  calc
    Nat.card (listedHull i) = Nat.card {m // m ∈ hullMasks i} :=
      (Nat.card_congr (Equiv.ofBijective f hf)).symm
    _ = (hullMasks i).card := by simp only [Nat.card_eq_fintype_card,Fintype.card_coe]
    _ = _ := hc i

/-- The literal hull list is exactly the canonical join of the full ambient family. -/
theorem sixteenHull_eight (i : Fin 16) :
    sixteenHull (row (eightIndex i)) = listedHull i := by
  apply le_antisymm
  · refine sup_le ?_ (sSup_le ?_)
    · intro x hx
      obtain ⟨m,hm,rfl⟩ := (mem_row_iff _ x).mp hx
      exact (nativeWord_mem_listedHull_iff i m).mpr ((rows_in_hull i).1 hm)
    · intro Y hY
      rw [sixteenOvergroups_eight] at hY
      obtain ⟨j,hj,rfl⟩ := hY
      intro x hx
      obtain ⟨m,hm,rfl⟩ := (mem_row_iff _ x).mp hx
      exact (nativeWord_mem_listedHull_iff i m).mpr ((rows_in_hull i).2 j hj hm)
  · apply (closure_le _).mpr
    rintro _ ⟨m,hm,rfl⟩
    rcases hull_generation i m hm with hm | ⟨hj,hk,n,hn,p,hp,he⟩
    · exact (show row (eightIndex i) ≤ sixteenHull (row (eightIndex i)) from le_sup_left)
        ((nativeWord_mem_row_iff _ m).mpr hm)
    · have hmem (j : Fin 10) (hj : j ∈ listedSixteenOvergroups i) (n : Fin 8192)
          (hn : n ∈ rowMasks (sixteenIndex j)) :
          nativeWord n ∈ sixteenHull (row (eightIndex i)) := by
        have hY : row (sixteenIndex j) ∈ sixteenOvergroups (row (eightIndex i)) := by
          rw [sixteenOvergroups_eight]
          exact ⟨j,hj,rfl⟩
        exact le_sup_of_le_right (le_sSup hY) ((nativeWord_mem_row_iff _ n).mpr hn)
      rw [← he,nativeWord_mul]
      exact (sixteenHull _).mul_mem (hmem _ hj n hn) (hmem _ hk p hp)

theorem sixteenHull_eight_card (i : Fin 16) :
    Nat.card (sixteenHull (row (eightIndex i))) = if i = 5 then 8 else 32 := by
  rw [sixteenHull_eight,listedHull_card]

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.FiniteConfigurations
