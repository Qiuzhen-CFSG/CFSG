module
public import Theory.SpecificGroups.PSL3.OddPrimeGraphExtension.GraphLargeStructure
public import Theory.SpecificGroups.PSL3Three.GraphLocalQuotients
public import Theory.SpecificGroups.PSL3Three.Cardinality

/-!
# Matrix coordinates for the inner-actor placement calculation

The canonical SL₃(3) projection followed by inner conjugation embeds the
matrix group in the literal graph extension. Every extension element has a
unique inner or inner-times-graph expression. Thus the actual extension has
order 11232, without replacing it by an unrelated finite carrier.

These marked coordinates support the Sylow and centralizer certificates for
Aschbacher–Smith E.1.14(7), printed p.214, via E.1.2 and E.1.5, pp.209–210
(Asc82a, Lemma 4.11). The automorphism coverage and graph outerness are reused
from `PSL3Three.GraphWitnesses.EightCentralizers.GraphModel`.
-/

public section
open Subgroup Theory.GroupTheory
open Matrix.PSL3Three Matrix.PSL3Three.GraphLocalQuotients
open Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.InnerActors

@[expose] def inner : SL →* G :=
  ((MulAut.conj : PSL →* MulAut PSL).comp project).codRestrict _
    (fun x => Subgroup.mem_sup_left ⟨project x, rfl⟩)

theorem inner_injective : Function.Injective inner := by
  intro x y h
  exact project_injective (MulAut.conj_injective_of_center_eq_bot
    Matrix.PSL3Three.GraphWitnesses.EightCentralizers.psl_center_eq_bot
    (congrArg Subtype.val h))

theorem range_inner : inner.range = innerPart (ZMod 3) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨project y, rfl⟩
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := project_surjective y
    exact ⟨z, Subtype.ext hy⟩

theorem graph_inner (x : SL) : graphElement * inner x =
    inner (graphSL (ZMod 3) x) * graphElement := by
  apply Subtype.ext
  apply MulEquiv.ext
  intro y
  change graph (ZMod 3) (project x * y * (project x)⁻¹) =
    project (graphSL (ZMod 3) x) * graph (ZMod 3) y *
      (project (graphSL (ZMod 3) x))⁻¹
  simp only [map_mul, map_inv]
  rfl

theorem graphElement_sq : graphElement ^ 2 = 1 :=
  Subtype.ext (graph_sq (ZMod 3))

theorem graphElement_not_inner : graphElement ∉ inner.range := by
  rw [range_inner]
  exact Matrix.PSL3Three.GraphWitnesses.EightCentralizers.GraphModel.graph_not_inner

/-- The literal extension is covered by the two matrix cosets. -/
theorem inner_or_inner_graph (x : G) :
    ∃ y : SL, x = inner y ∨ x = inner y * graphElement := by
  obtain ⟨y, hy | hy⟩ :=
    Matrix.PSL3Three.GraphWitnesses.EightCentralizers.GraphModel.automorphism_inner_or_inner_graph x.val
  · obtain ⟨z, rfl⟩ := project_surjective y
    exact ⟨z, Or.inl (Subtype.ext hy)⟩
  · obtain ⟨z, rfl⟩ := project_surjective y
    exact ⟨z, Or.inr (Subtype.ext hy)⟩

/-- Matrix coordinates retain the actual inner and graph automorphisms. -/
noncomputable def coordinates : SL × Bool ≃ G := Equiv.ofBijective
  (fun p => if p.2 then inner p.1 * graphElement else inner p.1) (by
    constructor
    · rintro ⟨x, b⟩ ⟨y, c⟩ h
      cases b <;> cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
      · exact Prod.ext (inner_injective h) rfl
      · exfalso
        apply graphElement_not_inner
        refine ⟨y⁻¹ * x, ?_⟩
        rw [map_mul, map_inv]
        rw [h]
        group
      · exfalso
        apply graphElement_not_inner
        refine ⟨x⁻¹ * y, ?_⟩
        rw [map_mul, map_inv]
        rw [← h]
        group
      · exact Prod.ext (inner_injective (mul_right_cancel h)) rfl
    · intro x
      obtain ⟨y, h | h⟩ := inner_or_inner_graph x
      · exact ⟨(y, false), h.symm⟩
      · exact ⟨(y, true), h.symm⟩)

@[simp] theorem coordinates_apply (x : SL) (b : Bool) :
    coordinates (x, b) = (if b then inner x * graphElement else inner x) := by
  unfold coordinates
  rfl

theorem card_extension : Nat.card G = 11232 := by
  rw [← Nat.card_congr coordinates, Nat.card_prod, card_SL]
  simp

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.InnerActors
