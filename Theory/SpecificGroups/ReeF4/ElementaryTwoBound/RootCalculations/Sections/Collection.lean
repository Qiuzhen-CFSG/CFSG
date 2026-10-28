module
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.Sections.SplitSupport
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.Sections.Exchanges

/-!
# Collection in the six smaller split-root supports

Adjacent root exchanges preserve each displayed support and increase the
positive-root height. Filtered collection therefore gives the ordered supported
factorization in the actual split matrix group. All exchanges are checked
instances of `xc`, `xs`, and `xb`; no finite group enumeration is used.

Source: GLS3 2.4.5(d), 2.4.6 and Lemma 3.3.9.
-/
@[expose] public section
noncomputable section
namespace ReeF4.ElementaryTwoBound.RootCalculations.Sections
open Parabolics Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations.LongCommutators
open NormalizedRootCentralizers.CenterExponent.OuterElimination
open Theory.AlgebraicGroup.StandardRootSystem
open FilteredCollection
attribute [local irreducible] MatrixRelations.LongCommutators.X

private def sectionOrder (s : Kind) : List (Fin 24) :=
  [22,23,4,5,16,17,10,11,0,1,2,3,12,13,14,15,18,19,20,21,6,7,8,9].filter
    (fun i => decide (Allowed s i))

private theorem mem_sectionOrder (s : Kind) (i : Fin 24) :
    i ∈ sectionOrder s ↔ Allowed s i := by
  have hall : i ∈ ([22,23,4,5,16,17,10,11,0,1,2,3,12,13,14,15,18,19,20,21,6,7,8,9] :
      List (Fin 24)) := by fin_cases i <;> decide
  simp only [sectionOrder, List.mem_filter, decide_eq_true_eq, hall, true_and]

private theorem sectionOrder_nodup (s : Kind) : (sectionOrder s).Nodup := by
  exact List.Nodup.filter _ (by decide)

private theorem word_inv (m : ℕ) (w : List (Fin 24 × CoefficientField m)) :
    (wordProduct (MatrixRelations.LongCommutators.X m) w)⁻¹ =
      wordProduct (MatrixRelations.LongCommutators.X m) w.reverse := by
  induction w with
  | nil => simp [wordProduct]
  | cons z w ih =>
    simpa only [wordProduct, List.map_cons, List.prod_cons, List.reverse_cons,
      List.map_append, List.prod_append, List.map_nil, List.prod_nil,
      mul_one, mul_inv_rev, xi] using congrArg
        (fun y => y * MatrixRelations.LongCommutators.X m z.1 z.2) ih

private theorem exists_supported_word (m : ℕ) (s : Kind) (x : SplitGroup m)
    (hx : x ∈ splitSection m s) :
    ∃ w : List (Fin 24 × CoefficientField m),
      (∀ z ∈ w, Allowed s z.1) ∧
      x = wordProduct (MatrixRelations.LongCommutators.X m) w := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, a, rfl⟩ := hx
    exact ⟨[(i,a)], by simpa using hi, by simp [wordProduct]⟩
  | one => exact ⟨[], by simp, by simp [wordProduct]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    exact ⟨w ++ v, by simpa only [List.mem_append, or_imp, forall_and] using ⟨hw,hv⟩,
      by simp [wordProduct]⟩
  | inv x _ hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨w.reverse, by simpa only [List.mem_reverse] using hw, word_inv m w⟩

private theorem splitWord_restrict (m : ℕ) (s : Kind) (v : Fin 24 → CoefficientField m) :
    splitWord m (fun i => if Allowed s i then v i else 0) =
      ((sectionOrder s).map fun i => MatrixRelations.LongCommutators.X m i (v i)).prod := by
  cases s <;> simp [splitWord, sectionOrder, Allowed, omitted, xz]

/-- Every element of each of the six actual generated split subgroups has
ordered coordinates with all omitted root parameters zero. -/
theorem splitCollection (m : ℕ) : SplitCollection m := by
  intro s x hx
  obtain ⟨w, hw, he⟩ := exists_supported_word m s x hx
  obtain ⟨v, hv⟩ := filteredCollection_exists_params degree
    (MatrixRelations.LongCommutators.X m) (sectionOrder s) (sectionOrder_nodup s) 12
    (fun i _ => (show ∀ i : Fin 24, degree i < 12 by decide) i)
    (xa m)
    (fun i j a b hi hj _ => by
      obtain ⟨c, hc, he⟩ := exchange m s i j a b
        ((mem_sectionOrder s i).mp hi) ((mem_sectionOrder s j).mp hj)
      exact ⟨c, fun z hz => ⟨(mem_sectionOrder s z.1).mpr (hc z hz).1,
        (hc z hz).2⟩, he⟩)
    w (fun z hz => (mem_sectionOrder s z.1).mpr (hw z hz))
  refine ⟨fun i => if Allowed s i then v i else 0, ?_, ?_⟩
  · intro i hi
    simp only [if_neg hi]
  · rw [splitWord_restrict, ← hv, ← he]

end ReeF4.ElementaryTwoBound.RootCalculations.Sections
