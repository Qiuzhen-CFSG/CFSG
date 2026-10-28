module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.FiniteConfigurations.Census
/-!
# Exact unrestricted sixteen-overgroup tables

Every ambient eligible sixteen containing a literal row contains both actual
marked points. The source intersection theorem and complete finite census
therefore identify it with one of the ten literal sixteens. This discharges
the distinction between the earlier candidate table and the unrestricted
ambient family; it uses no normalizer-placement assumption.
Source: Kleidman--Wilson (1988), Section 2.1, pp.488--489.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.FiniteConfigurations
open MarkedIntersection ElementaryNormalizerCover.PureTwoA.NativePair
attribute [local irreducible] modelGroup matrixA matrixB toMatrix
attribute [local instance 2000] Finset.decidableDforallFinset
set_option Elab.async false

theorem mem_sixteenOvergroups_row_iff (i : Fin 26) (Y : Subgroup Model) :
    Y ∈ sixteenOvergroups (row i) ↔
      ∃ j : Fin 10, Y = row (sixteenIndex j) ∧ row i ≤ row (sixteenIndex j) := by
  constructor
  · rintro ⟨hle,hc,hE,hp,hn⟩
    let := hE
    have ht := hle (markedT_mem_row i)
    have hP := hle (markedP_mem_row i)
    have hM := marked_all_row_two_le Y hp hn ht hP
    obtain ⟨j,rfl⟩ := marked_sixteen_census Y hM ht hP hc hp hn
    exact ⟨j,rfl,hle⟩
  · rintro ⟨j,rfl,hle⟩
    exact ⟨hle,sixteen_card j,row_elementary _,row_pure _,row_no_native_pair _⟩

/-- The earlier candidate incidence list is exactly the full ambient family. -/
theorem sixteenOvergroups_eight (i : Fin 16) :
    sixteenOvergroups (row (eightIndex i)) =
      (fun j => row (sixteenIndex j)) '' (listedSixteenOvergroups i : Set (Fin 10)) := by
  ext Y
  rw [mem_sixteenOvergroups_row_iff]
  constructor
  · rintro ⟨j,rfl,hj⟩
    exact ⟨j,(eight_le_sixteen_iff i j).mp hj,rfl⟩
  · rintro ⟨j,hj,rfl⟩
    exact ⟨j,rfl,(eight_le_sixteen_iff i j).mpr hj⟩

theorem sixteenOvergroups_sixteen (i : Fin 10) :
    sixteenOvergroups (row (sixteenIndex i)) = {row (sixteenIndex i)} := by
  ext Y
  rw [mem_sixteenOvergroups_row_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨j,rfl,hj⟩
    have ht : ∀ i j : Fin 10, rowMasks (sixteenIndex i) ⊆ rowMasks (sixteenIndex j) → i = j := by
      decide +kernel
    have he := ht i j ((row_le_iff _ _).mp hj)
    rw [he]
  · intro he
    exact ⟨i,he,le_rfl⟩

theorem sixteenHull_sixteen (i : Fin 10) :
    sixteenHull (row (sixteenIndex i)) = row (sixteenIndex i) := by
  simp [sixteenHull,sixteenOvergroups_sixteen]

/-- The line eight has no eligible sixteen overgroup anywhere in the model. -/
theorem sixteenOvergroups_line : sixteenOvergroups (row 5) = ∅ := by
  change sixteenOvergroups (row (eightIndex 5)) = ∅
  rw [sixteenOvergroups_eight,listedSixteenOvergroups_table]
  simp

theorem sixteenHull_line : sixteenHull (row 5) = row 5 := by
  simp only [sixteenHull,sixteenOvergroups_line,sSup_empty,sup_bot_eq]

/-- Each other eight has exactly the two distinct ambient sixteen overgroups. -/
theorem sixteenOvergroups_non_line (i : Fin 16) (hi : i ≠ 5) :
    ∃ j k : Fin 10, j ≠ k ∧ sixteenOvergroups (row (eightIndex i)) =
      {row (sixteenIndex j),row (sixteenIndex k)} := by
  obtain ⟨j,k,hjk,h⟩ := two_listed_sixteens i hi
  refine ⟨j,k,hjk,?_⟩
  ext Y
  rw [mem_sixteenOvergroups_row_iff]
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨l,rfl,hl⟩
    rcases (h l).mp hl with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨j,rfl,(h j).mpr (Or.inl rfl)⟩
    · exact ⟨k,rfl,(h k).mpr (Or.inr rfl)⟩

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.FiniteConfigurations
