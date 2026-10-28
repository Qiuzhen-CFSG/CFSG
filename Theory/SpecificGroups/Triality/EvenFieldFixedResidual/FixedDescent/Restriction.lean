module

public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.FixedDescent.Diagram
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.FixedDescent.Field
/-!
# Restricting the smaller-field embedding to triality fixed groups

The entrywise embedding intertwines the smaller defining twist with the
forward half-parameter twist over the larger coefficient field. Injectivity
therefore detects fixedness in both directions. If a fixed matrix over the
larger field has a lift in the smaller split group, that lift is necessarily
fixed by the smaller defining twist. This gives the fixed-group equivalence
from the precise split-group lift premise.

Only this lift premise remains here; matrix entries lying in the smaller
field do not by themselves prove membership in its root-generated group.
The separate carrier assembly uses this restriction together with the
inverse-diagram comparison and the proved elementary central quotient.

Source: GLS3 §§2.2 and 2.5 (`refs/KGroup/GLS3/chapter2.tex`), in the field
case of Aschbacher–Smith 16.1.4(4), printed p.1171 (`refs/quasithin.pdf`).
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.EvenField
open OuterOdd

private theorem restrict_surjective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (K : Subgroup G) (L : Subgroup H) (F : K →* L)
    (hF : ∀ y : K, (F y).val = f y.val)
    (hlift : ∀ x : H, x ∈ L → ∃ y : G, f y = x)
    (hback : ∀ y : G, f y ∈ L → y ∈ K) : Function.Surjective F := by
  intro x
  obtain ⟨y, hy⟩ := hlift x.val x.property
  have hmem : y ∈ K := hback y (hy.symm ▸ x.property)
  exact ⟨⟨y, hmem⟩, Subtype.ext ((hF ⟨y, hmem⟩).trans hy)⟩

/-- Compatibility with the named forward half-parameter automorphism. -/
theorem halfSplitMap_forward (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    (hnm : n = 2*m) (x : SplitGroup (binaryParameters m hm)) :
    halfSplitMap n hn m hm hnm (graphFieldAutomorphism (binaryParameters m hm) x) =
      forwardGraphHalf n hn m (halfSplitMap n hn m hm hnm x) :=
  halfSplitMap_graphField n hn m hm hnm x

/-- Injectivity detects the smaller defining fixed subgroup exactly. -/
theorem halfSplitMap_mem_forward_iff (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    (hnm : n = 2*m) (x : SplitGroup (binaryParameters m hm)) :
    halfSplitMap n hn m hm hnm x ∈ (forwardGraphHalf n hn m).fixedSubgroup ↔
      x ∈ fixedSubgroup (binaryParameters m hm) := by
  constructor
  · intro hx
    apply halfSplitMap_injective n hn m hm hnm
    exact (halfSplitMap_forward n hn m hm hnm x).trans
      ((MulAut.mem_fixedSubgroup _ _).mp hx)
  · intro hx
    exact (MulAut.mem_fixedSubgroup _ _).mpr
      ((halfSplitMap_forward n hn m hm hnm x).symm.trans
        (congrArg (halfSplitMap n hn m hm hnm) hx))

/-- The smaller fixed group embeds by the literal entrywise coefficient map. -/
def halfFixedMap (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m) (hnm : n = 2*m) :
    fixedSubgroup (binaryParameters m hm) →* (forwardGraphHalf n hn m).fixedSubgroup :=
  ((halfSplitMap n hn m hm hnm).comp (fixedSubgroup (binaryParameters m hm)).subtype).codRestrict
    (forwardGraphHalf n hn m).fixedSubgroup
    (fun x => (halfSplitMap_mem_forward_iff n hn m hm hnm x.val).mpr x.property)

@[simp] theorem halfFixedMap_val (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    (hnm : n = 2*m) (x : fixedSubgroup (binaryParameters m hm)) :
    (halfFixedMap n hn m hm hnm x).val = halfSplitMap n hn m hm hnm x.val := rfl

/-- Restriction retains injectivity of the coefficient embedding. -/
theorem halfFixedMap_injective (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    (hnm : n = 2*m) : Function.Injective (halfFixedMap n hn m hm hnm) := by
  intro x y h
  exact Subtype.ext (halfSplitMap_injective n hn m hm hnm (congrArg Subtype.val h))

/-- A lift of a forward-fixed matrix is automatically fixed by the smaller twist. -/
theorem halfFixedMap_surjective_of_split_lifts (n : ℕ) (hn : 0 < n)
    (m : ℕ) (hm : 0 < m) (hnm : n = 2*m)
    (hlift : ∀ x : SplitGroup (binaryParameters n hn), forwardGraphHalf n hn m x = x →
      ∃ y : SplitGroup (binaryParameters m hm), halfSplitMap n hn m hm hnm y = x) :
    Function.Surjective (halfFixedMap n hn m hm hnm) :=
  restrict_surjective (halfSplitMap n hn m hm hnm) _ _ (halfFixedMap n hn m hm hnm)
    (halfFixedMap_val n hn m hm hnm)
    (fun x hx => hlift x ((MulAut.mem_fixedSubgroup _ _).mp hx))
    (fun y hy => (halfSplitMap_mem_forward_iff n hn m hm hnm y).mp hy)

/-- The fixed-group equivalence, conditional only on actual split-group lifts. -/
def halfFixedEquivOfSplitLifts (n : ℕ) (hn : 0 < n)
    (m : ℕ) (hm : 0 < m) (hnm : n = 2*m)
    (hlift : ∀ x : SplitGroup (binaryParameters n hn), forwardGraphHalf n hn m x = x →
      ∃ y : SplitGroup (binaryParameters m hm), halfSplitMap n hn m hm hnm y = x) :
    fixedSubgroup (binaryParameters m hm) ≃* (forwardGraphHalf n hn m).fixedSubgroup :=
  MulEquiv.ofBijective (halfFixedMap n hn m hm hnm)
    ⟨halfFixedMap_injective n hn m hm hnm,
      halfFixedMap_surjective_of_split_lifts n hn m hm hnm hlift⟩

end Triality.Standard.EvenField
