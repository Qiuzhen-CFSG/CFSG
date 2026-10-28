module
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentModels.Original
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedModels

/-!
# The three genuine paired component families

The actual paired-component sieve and sporadic exclusion leave exactly
binary PSL₂, Suzuki and prime-field odd PSL₂. This statement is applied to
the same C-component in H/J. Normality and its failure lift through the
solvable core, so the original exchanged branch is preserved by the
quotient. The original component normalizer has index two in that branch.

Source: Aschbacher–Smith E.2.2(1), printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Structure
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

/-- Remove the sporadic row from the original core-free paired-component sieve. -/
theorem source_paired_component_models
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    (K : Subgroup H) (hK : IsComponent H K)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal) :
    (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSL K 2 (2^f)) ∨
    (∃ m : ℕ, 1 ≤ m ∧ Nonempty (K ≃* SuzukiMatrixGroup m)) ∨
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL K 2 p) := by
  rcases PairedModels.source hC hH T hP hs hJ K hK hgen hn with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · have hrad : solvableRadical H = ⊥ :=
      (ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs).symm.trans hJ
    let : IsSimpleGroup K := hK.isCComponent.isSimpleGroup_of_solvableRadical_eq_bot hrad
    exact (source_simple_component_not_sporadic hH T hP K hK hgen h).elim

/-- The original C-component is normal or has exactly two conjugates. -/
theorem source_original_component_normal_or_index_two
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    K.Normal ∨ (normalizer (K : Set H)).index = 2 := by
  let J := ChapterB.minimalParabolicCore T hP
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  have hi := source_component_simple_image T hP hs K hK hgen
  rcases hi.2.1.normal_or_index_two_of_odd_rank_le_two
    (source_star_sqtk hA hH T hP hs).stronglyQuasithin with hn | hn
  · exact Or.inl (cComponent_normal_of_quotient_normal hK J hn)
  · exact Or.inr ((cComponent_normalizer_index_quotient hK J).symm.trans hn)

/-- The actual star image of an exchanged original C-component has one of the three source families. -/
theorem source_original_paired_models
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal) :
    let D := K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))
    (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSL D 2 (2^f)) ∨
    (∃ m : ℕ, 1 ≤ m ∧ Nonempty (D ≃* SuzukiMatrixGroup m)) ∨
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL D 2 p) := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  have hsX : ¬ Group.IsSolvable (H ⧸ J) := fun hx =>
    hs ((Group.isSolvable_iff_subgroup_quotient J).mpr ⟨inferInstance,hx⟩)
  have hi := source_component_simple_image T hP hs K hK hgen
  exact source_paired_component_models hC (source_star_sqtk hA hH T hP hs)
    S (source_star_minimal_core_free T hP).1 hsX (source_star_minimal_core_free T hP).2
    (K.map q) hi.2.1 hi.2.2.2 (fun hd => hn (cComponent_normal_of_quotient_normal hK J hd))
end CFSG.Quasithin.ChapterE.Structure
