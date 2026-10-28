module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SubfieldOvergroups.FieldGeometry.Coefficients
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates

/-!
# Field descent of positive root products

The unique ordered positive-root coordinates are natural under coefficient
embeddings. If the matrix entries are fixed by the smaller Frobenius power,
uniqueness fixes each coordinate, so every coordinate lies in the embedded
field. Their smaller-field root product is the required preimage in the
actual root-generated split group.

Source: the Chevalley normal form in GLS3 1.11.5,
`refs/KGroup/GLS3/Chapter1.tex`, used for Malle's subfield groups.
-/

public section

open Theory.AlgebraicGroup
open ReeF4 ReeF4.Subfield ReeF4.LargeLocalSeeds ReeF4.Parabolics.RadicalCoordinates

namespace ReeF4.Subfield
noncomputable section

theorem splitMap_entry {k m : ℕ} (f : CoefficientField k →+* CoefficientField m)
    (x : SplitGroup k) (i j : F4Chevalley.BasisIndex) :
    (splitMap f x).val.val i j = f (x.val.val i j) := rfl

theorem splitMap_word {k m : ℕ} (f : CoefficientField k →+* CoefficientField m)
    {s : Support} (e : RootOrder s) (t : Parameters k s) :
    splitMap f (word k e t) = word m e (f ∘ t) := by
  rw [word, map_list_prod, List.map_ofFn, word]
  congr 1
  apply congrArg List.ofFn
  funext i
  exact splitMap_rootGenerator f _ _

theorem splitMap_mem_unipotent {k m : ℕ}
    (f : CoefficientField k →+* CoefficientField m) {x : SplitGroup k}
    (hx : x ∈ splitUnipotent k) : splitMap f x ∈ splitUnipotent m := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, t, hr, rfl⟩ := hx
    rw [splitMap_rootGenerator]
    exact Subgroup.subset_closure ⟨r, f t, hr, rfl⟩
  | one => simpa only [map_one] using (splitUnipotent m).one_mem
  | mul x y _ _ hx hy => simpa only [map_mul] using (splitUnipotent m).mul_mem hx hy
  | inv x _ hx => simpa only [map_inv] using (splitUnipotent m).inv_mem hx

theorem splitMap_frobenius_fixed_of_entries {k m : ℕ}
    (f : CoefficientField k →+* CoefficientField m) {x : SplitGroup m}
    (hx : ∀ i j, x.val.val i j ∈ Set.range f) :
    splitMap (iterateFrobenius (CoefficientField m) 2 (2*k+1)) x = x := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [splitMap_entry]
  exact (coefficient_mem_range_iff f _).mp (hx i j)

theorem entries_mem_range_of_splitMap_frobenius_fixed {k m : ℕ}
    (f : CoefficientField k →+* CoefficientField m) {x : SplitGroup m}
    (hx : splitMap (iterateFrobenius (CoefficientField m) 2 (2*k+1)) x = x) :
    ∀ i j, x.val.val i j ∈ Set.range f := by
  intro i j
  apply (coefficient_mem_range_iff f _).mpr
  exact congrArg (fun z : SplitGroup m => z.val.val i j) hx

theorem unipotent_mem_range_of_entries {k m : ℕ}
    (f : CoefficientField k →+* CoefficientField m) {x : SplitGroup m}
    (hu : x ∈ splitUnipotent m) (hx : ∀ i j, x.val.val i j ∈ Set.range f) :
    x ∈ (splitMap f).range := by
  classical
  obtain ⟨e⟩ := rootOrder_nonempty .positive
  obtain ⟨t, ht⟩ := (wordInSubgroup_bijective m e).2 ⟨x, hu⟩
  have he : word m e t = x := congrArg Subtype.val ht
  have hf := splitMap_frobenius_fixed_of_entries f hx
  rw [← he, splitMap_word] at hf
  have htfix : (iterateFrobenius (CoefficientField m) 2 (2*k+1)) ∘ t = t :=
    (wordInSubgroup_bijective m e).1 (Subtype.ext hf)
  have htmem (r : Root .positive) : t r ∈ Set.range f := by
    apply (coefficient_mem_range_iff f _).mpr
    exact congrFun htfix r
  choose a ha using htmem
  refine ⟨word k e a, ?_⟩
  rw [splitMap_word, ← he]
  congr 1
  funext r
  exact ha r

end
end ReeF4.Subfield
